//! The oracle is the shipped native assertion ingress. The checker receives
//! only the raw parser tree and lexical metadata, never native verdicts/IR.
use nibli_kr::{
    parser::parse_statements,
    reify::{self, InputIntent},
};
use nibli_session::CoreSession;
use nibli_types::logic::{LogicBuffer, LogicalTerm, QueryResult};
use std::sync::{Mutex, MutexGuard, OnceLock};

const CHECKER: &str = include_str!("../spec/nibli_checker.nibli");

struct Checker {
    session: CoreSession,
    // Keep ordinary `cargo test` bounded too; the self AST is much larger
    // than the adversarial fixtures. No test relies on another test's KB.
    _serial: MutexGuard<'static, ()>,
}

impl std::ops::Deref for Checker {
    type Target = CoreSession;
    fn deref(&self) -> &CoreSession {
        &self.session
    }
}

fn checker(subject: &str, intent: InputIntent) -> Checker {
    static SERIAL: Mutex<()> = Mutex::new(());
    let serial = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    static RULES: OnceLock<Vec<(LogicBuffer, String)>> = OnceLock::new();
    let mut compiled = RULES
        .get_or_init(|| {
            let session = CoreSession::new();
            parse_statements(CHECKER)
                .unwrap()
                .iter()
                .map(|s| {
                    let text = &CHECKER[s.span.clone()];
                    (
                        session
                            .compile_text(text)
                            .unwrap_or_else(|e| panic!("{text}\n{e:?}")),
                        text.to_owned(),
                    )
                })
                .collect()
        })
        .clone();
    let tree = parse_statements(subject)
        .unwrap_or_else(|e| panic!("subject does not parse: {e:?}\n{subject}"));
    let facts = reify::reify(&tree, intent).unwrap();
    for fact in facts.facts {
        let args = fact
            .arguments
            .into_iter()
            .map(LogicalTerm::Constant)
            .collect::<Vec<_>>();
        let buffer = nibli_semantics::compile_injected_fact(fact.relation, &args).unwrap();
        compiled.push((buffer, format!("reified {}", fact.relation)));
    }
    let (kb, _) = nibli_reason::KnowledgeBase::from_compiled_batch(compiled).unwrap();
    Checker {
        session: CoreSession::with_kb(kb),
        _serial: serial,
    }
}

fn verdict(session: &CoreSession, query: &str) -> bool {
    let result = session.query_text(query).unwrap();
    let (complete, refused) = session.materialization_report().unwrap();
    let relation = query.split('(').next().unwrap();
    assert!(
        complete.iter().any(|r| r == relation),
        "checker did not complete {relation}: {refused:?}"
    );
    match result {
        QueryResult::True => true,
        QueryResult::False => false,
        other => panic!("incomplete checker result for {query}: {other:?}"),
    }
}

fn compare(subject: &str, intent: InputIntent, expected: bool, category: Option<&str>) {
    let native = CoreSession::new();
    let native_result = match intent {
        InputIntent::Assertion => native.assert_text(subject).map(|_| ()),
        InputIntent::Query => native.compile_query_text(subject).map(|_| ()),
    };
    assert_eq!(
        native_result.is_ok(),
        expected,
        "native expectation: {subject}\n{native_result:?}"
    );
    let check = checker(subject, intent);
    assert!(
        verdict(&check, "checker_complete(\"program:0\")."),
        "analysis incomplete: {subject}"
    );
    let accepted = verdict(&check, "checker_accepts(\"program:0\").");
    assert_eq!(
        accepted, expected,
        "checker parity: {subject}\nnative: {native_result:?}"
    );
    assert_eq!(
        verdict(&check, "sc_has_violation(\"program:0\")."),
        !expected
    );
    if let Some(category) = category {
        assert!(
            verdict(
                &check,
                &format!("violation_kind(\"program:0\", \"{category}\").")
            ),
            "missing {category} for {subject}"
        );
    }
}

#[test]
fn basic_differential() {
    for (source, good, kind) in [
        ("person(Zed).", true, None),
        ("never_declared_probe(Zed).", false, Some("vocabulary")),
        (
            "derived_only(\"prisoner\"). prisoner(Zed).",
            false,
            Some("derived_only"),
        ),
        (
            "admits(\"person\"). prisoner(Zed).",
            false,
            Some("vocabulary"),
        ),
        (
            "person(Zed). admits(\"person\").",
            false,
            Some("declaration_order"),
        ),
        ("person(Zed, Adam).", false, Some("arity")),
        ("person(missing: Zed).", false, Some("place")),
        (
            "all $x: person($x) & ~eats($x) -> prisoner($x). all $x: prisoner($x) -> eats($x).",
            false,
            Some("stratification"),
        ),
    ] {
        compare(source, InputIntent::Assertion, good, kind);
    }
}

#[test]
fn stage_one_self_check() {
    let check = checker(CHECKER, InputIntent::Assertion);
    assert!(verdict(&check, "checker_complete(\"program:0\")."));
    assert!(verdict(&check, "checker_accepts(\"program:0\")."));
    for query in [
        "sc_has_violation(\"program:0\").",
        "advisory_kind(\"program:0\", \"range_restriction\").",
        "advisory_kind(\"program:0\", \"schema_conflict\").",
    ] {
        assert!(!verdict(&check, query), "self-check violation: {query}");
    }
}

#[test]
fn language_profiles() {
    let accepted = [
        "",
        "admits(\"person\"). derived_only(\"person\").",
        "admits(\"person\"). all $x: eats($x) -> prisoner($x).",
        "admits(\"person\") & prisoner(Zed).",
        "derived_only(\"prisoner\") & prisoner(Zed).",
        "all $x, $y: person($x) & ~eats($y) -> prisoner($x).",
        "all $x, $y: person($x) -> prisoner($y).",
        "all $x, $unused: person($x) -> prisoner($x).",
        "all $x: person($x) -> prisoner($x). all $x: prisoner($x) -> person($x).",
        "all $x: person($x) | animal($x) -> prisoner($x).",
        "all $x: person($x) -> (animal($x) | prisoner($x)).",
        "all $x: person($x) -> must prisoner($x).",
        "all $x: past person($x) -> prisoner($x).",
        "person(Zed). ~prisoner(Zed).",
        "admits(\"person\"). ~prisoner(Zed).",
        "person(Zed) | ~prisoner(Zed).",
        "person(Zed) & (prisoner(Zed) | eats(Zed)).",
        "person(Zed) -> prisoner(Zed).",
        "person(Zed) <-> prisoner(Zed).",
        "eats(some person).",
        "eats(every person).",
        "every person $x: eats($x).",
        "some person $x: eats($x).",
        "the person $x: eats($x).",
        "eats(every the person).",
        "every the person $x: eats($x).",
        "entitled(every person, event { eats(it_a) }).",
        "believe(Adam, event { greater(3, 1) }).",
        "believe(Adam, fact { eats(exactly 2 person) }).",
        "believe(Adam, property { eats(slot) }).",
        "eats(the person where prisoner).",
        "eats(Adam where person).",
        "eats(some loves(loved: it, lover: Adam)).",
        "eats(some loves.loved).",
        "owns(owned: House, owner: Adam).",
        "owned(House, Adam).",
        "[big fast] dog(Rex).",
        "computer+user(Adam).",
        "greater(Adam, Bob).",
        "person($x) & prisoner($x).",
    ];
    let mut failures = Vec::new();
    for source in accepted {
        if std::panic::catch_unwind(|| compare(source, InputIntent::Assertion, true, None)).is_err()
        {
            failures.push(source);
        }
    }
    assert!(failures.is_empty(), "accepted mismatches: {failures:#?}");
}

#[test]
fn static_refusals() {
    let refused = [
        (
            "person(Zed). derived_only(\"person\").",
            "declaration_order",
        ),
        ("person(it).", "position"),
        ("person(slot).", "position"),
        ("person(Me).", "position"),
        ("person(Zed, x1: Adam).", "place"),
        ("eats(some loves(Adam, Bob)).", "arity"),
        ("eats(some loves(lover: Adam)).", "position"),
        ("eats(some loves(lover: it, loved: it)).", "position"),
        ("eats(some loves(it)).", "position"),
        ("eats(some loves.missing).", "place"),
        ("eats(Adam) via person(Bob).", "arity"),
        ("eats(Adam) via never_declared_probe(Bob).", "vocabulary"),
        (
            "believe(Adam, event { never_declared_probe(Bob) }).",
            "vocabulary",
        ),
        ("person($x) & ~prisoner($x).", "scope"),
        ("person($x) & past prisoner($x).", "scope"),
        ("person($x) & eats($x, ?).", "scope"),
        ("person($x) & eats(every animal, $x).", "scope"),
        ("eats(exactly 2 person).", "query_only"),
        ("exactly 2 person $x: eats($x).", "query_only"),
        ("product(6, 2, 3).", "query_only"),
        ("exponential(4, 2, 2).", "query_only"),
        ("greater(3, 1).", "query_only"),
        (
            "all $x: person($x) & greater($x, Bob) -> prisoner($x).",
            "query_only",
        ),
        ("past eats(every person).", "assertion_form"),
        ("person(Zed) | prisoner(Zed).", "assertion_form"),
        ("person(Zed) ^ prisoner(Zed).", "assertion_form"),
        ("all $x: person($x).", "assertion_form"),
        ("all $x: person($x) -> ~prisoner($x).", "assertion_form"),
        (
            "all $x: person($x) & ~eats($x) -> (animal($x) | prisoner($x)).",
            "assertion_form",
        ),
        (
            "all $x: eats(every person) -> prisoner($x).",
            "assertion_form",
        ),
    ];
    let mut failures = Vec::new();
    for (source, category) in refused {
        if std::panic::catch_unwind(|| {
            compare(source, InputIntent::Assertion, false, Some(category))
        })
        .is_err()
        {
            failures.push(source);
        }
    }
    assert!(failures.is_empty(), "refused mismatches: {failures:#?}");
}

#[test]
fn stage_two_shipped_programs() {
    for (name, text) in [
        ("utopia", nibli_verify::corpora::UTOPIA),
        ("gdpr", nibli_verify::corpora::GDPR),
        ("drug interactions", nibli_verify::corpora::DDI),
        (
            "Lucy constitution",
            include_str!("../../lucy-cli/constitution/lucy.nibli"),
        ),
        (
            "adjudication policy",
            include_str!("../../examples/adjudication/policy.nibli"),
        ),
    ] {
        eprintln!("corpus: {name}");
        compare(text, InputIntent::Assertion, true, None);
    }
}

#[test]
fn query_intent() {
    for text in [
        "eats(exactly 2 person).",
        "exactly 2 person $x: eats($x).",
        "product(6, 2, 3).",
        "exponential(4, 2, 2).",
        "greater(3, 1).",
        "all $x: person($x).",
        "person(Zed) | prisoner(Zed).",
        "all $x: person($x) -> ~person($x).",
    ] {
        compare(text, InputIntent::Query, true, None);
    }
    compare("person(it).", InputIntent::Query, false, Some("position"));
    compare(
        "person($x) & ~person($x).",
        InputIntent::Query,
        false,
        Some("scope"),
    );
    compare(
        "unknown_checker_probe(Zed).",
        InputIntent::Query,
        false,
        Some("vocabulary"),
    );
}

#[test]
fn stronger_safety_is_advisory() {
    for (text, advisory) in [
        (
            "admits(\"person\"). derived_only(\"person\").",
            "schema_conflict",
        ),
        (
            "all $x, $y: person($x) & ~eats($y) -> prisoner($x).",
            "range_restriction",
        ),
        (
            "all $x, $y: person($x) -> prisoner($y).",
            "range_restriction",
        ),
        (
            "all $x, $y: person($x) & ~($x = $y) -> prisoner($x).",
            "range_restriction",
        ),
    ] {
        CoreSession::new().assert_text(text).unwrap();
        let check = checker(text, InputIntent::Assertion);
        assert!(verdict(&check, "checker_accepts(\"program:0\")."));
        assert!(verdict(
            &check,
            &format!("advisory_kind(\"program:0\", \"{advisory}\").")
        ));
    }
}

#[test]
fn entire_surface_inventory() {
    let mut failures = Vec::new();
    for case in nibli_verify::nibli_kr_battery::CONSTRUCT_INVENTORY {
        let expected = CoreSession::new().assert_text(case.nibli_kr).is_ok();
        for intent in [InputIntent::Assertion, InputIntent::Query] {
            let good = expected || intent == InputIntent::Query;
            if std::panic::catch_unwind(|| compare(case.nibli_kr, intent, good, None)).is_err() {
                failures.push((case.nibli_kr, intent));
            }
        }
    }
    assert!(failures.is_empty(), "construct mismatches: {failures:#?}");
}

#[test]
fn declaration_and_scope_edges() {
    let cases = [
        "past admits(\"person\"). prisoner(Zed).",
        "past derived_only(\"prisoner\"). prisoner(Zed).",
        "derived_only(\"prisoner\"). past prisoner(Zed).",
        "past person(Zed). admits(\"person\").",
        "derived_only(\"person_x1\"). person(Zed).",
        "person(Zed). derived_only(\"person_x1\").",
        "derived_only(\"owned\"). owns(House, Adam).",
        "derived_only(\"owns\"). owned(House, Adam).",
        "derived_only(\"prisoner\"). eats(some prisoner).",
        "derived_only(\"prisoner\"). eats(the prisoner).",
        "derived_only(\"prisoner\"). eats(Zed where prisoner).",
        "derived_only(\"prisoner\"). some person $x: prisoner($x).",
        "admits(\"eats\"). eats(some person).",
        "admits(\"eats\"). eats(the person).",
        "person($x) & (prisoner($x) & eats($x)).",
        "person($x) & eats($x, some animal).",
        "person($x) & eats(some animal, $x).",
        "person($x) & eats(x2: $x, x1: some animal).",
        "person($x) & eats(x2: some animal, x1: $x).",
        "desires($x, event { person($x) }).",
        "all $x: person($x) -> desires($x, event { person($x) }).",
        "all $x: person($x) -> person($x) -> eats($x).",
        "all $x: person($x) -> eats(every animal).",
        "all $x: person($x) -> (prisoner($x) | ~eats($x)).",
        "all $x: person($x) & ~eats(some animal) -> prisoner($x).",
        "all $x: person($x) & ~eats(?) -> prisoner($x).",
        "all $x: person($x) & ~eats($y) -> prisoner($x).",
        "all $x, $y: person($x) & ~eats($y) -> prisoner($x).",
        "all $x: person($x) -> prisoner($x). all $x: prisoner($x) & ~($x = Adam) -> animal($x).",
        "all $x: person($x) -> $x = Adam.",
        "all $x: $x = $x.",
        "past believe(Adam, event { must eats(Bob) }).",
        "believe(Adam, event { past person(Bob) & now eats(Bob) }).",
        "eats(every loves(loved: Adam where person)).",
        "eats(some loves(loved: Adam where person)).",
        "eats(every the person). all $x: ~eats($x) -> person($x).",
        "entitled(every person, event { eats(it_a) }). all $x: person($x) & ~eats($x) -> prisoner($x). all $x: prisoner($x) -> person($x).",
        "eats(every person where ~prisoner). all $x: eats($x) -> prisoner($x).",
        "eats(every person also prisoner). all $x: eats($x) & ~prisoner($x) -> person($x).",
    ];
    let mut failures = Vec::new();
    for source in cases {
        let expected = CoreSession::new().assert_text(source).is_ok();
        if std::panic::catch_unwind(|| compare(source, InputIntent::Assertion, expected, None))
            .is_err()
        {
            failures.push(source);
        }
    }
    assert!(failures.is_empty(), "edge mismatches: {failures:#?}");
}

#[test]
fn generated_dependency_graphs_and_dnf_boundary() {
    let names = [
        "person", "prisoner", "eats", "animal", "dog", "cat", "fit", "rotten",
    ];
    for seed in 0..24u64 {
        let mut state = seed.wrapping_add(1);
        let mut program = String::new();
        for edge in 0..8 {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let a = names[(state >> 32) as usize % names.len()];
            let b = names[(state >> 48) as usize % names.len()];
            let sign = if edge % 3 == 0 { "~" } else { "" };
            program.push_str(&format!("all $x: person($x) & {sign}{a}($x) -> {b}($x).\n"));
        }
        let expected = CoreSession::new().assert_text(&program).is_ok();
        compare(
            &program,
            InputIntent::Assertion,
            expected,
            (!expected).then_some("stratification"),
        );
    }
    for source in [
        "all $x: person($x) & ~dog($x) -> cat($x). all $x: person($x) & ~cat($x) -> dog($x).",
        "all $x: person($x) -> dog($x). all $x: dog($x) -> person($x). all $x: ~dog($x) -> cat($x).",
        "all $x: person($x) & ~owned($x, House) -> owns($x, House).",
    ] {
        let expected = CoreSession::new().assert_text(source).is_ok();
        compare(
            source,
            InputIntent::Assertion,
            expected,
            (!expected).then_some("stratification"),
        );
    }
    for (factors, valid) in [(5, true), (6, false)] {
        let body = vec!["(person($x) | animal($x))"; factors].join(" & ");
        compare(
            &format!("all $x: {body} -> prisoner($x)."),
            InputIntent::Assertion,
            valid,
            (!valid).then_some("assertion_form"),
        );
    }
}

#[test]
fn effective_operands_and_opaque_descriptions() {
    let mut failures = Vec::new();
    for source in [
        "greater(some person, Bob).",
        "greater(the person, Bob).",
        "greater(?, Bob).",
        "greater(event { person(Bob) }, Bob).",
        "eats(some greater).",
        "eats(the product).",
        "eats(every the greater).",
        "eats(the greater(x2: 3)).",
        "eats(the product where person).",
        "the person $x: greater($x, Bob).",
        "eats(Adam) via greater(3).",
        "all $x: eats($x) via greater(Adam) -> prisoner($x).",
        "eats(some greater(x3: it, x1: Adam, x2: Bob)).",
        "eats(some greater.x3).",
        "eats(some greater.x1).",
    ] {
        let expected = CoreSession::new().assert_text(source).is_ok();
        if std::panic::catch_unwind(|| compare(source, InputIntent::Assertion, expected, None))
            .is_err()
        {
            failures.push(source);
        }
    }
    assert!(failures.is_empty(), "operand mismatches: {failures:#?}");
}

#[test]
fn quoted_dependencies_and_locks() {
    let mut failures = Vec::new();
    for source in [
        "admits(\"believe\"). believe(Adam, event { person(Bob) }).",
        "admits(\"believe\"). admits(\"event\"). believe(Adam, event { person(Bob) }).",
        "derived_only(\"event\"). believe(Adam, event { person(Bob) }).",
        "derived_only(\"person\"). believe(Adam, event { person(Bob) }).",
        "all $x: person($x) -> entitled($x, event { eats(Bob) }).",
        "all $x: person($x) -> entitled($x, event { eats(Bob) -> prisoner(Bob) }).",
        "all $x: person($x) -> entitled($x, event { all $y: person($y) -> eats($y) }).",
        "all $x: person($x) -> entitled($x, event { eats(exactly 2 person) }).",
        "all $x: person($x) -> entitled($x, event { eats(Bob) | prisoner(Bob) }).",
        "all $x: believe($x, event { prisoner(Bob) }) -> eats($x). all $x: ~eats($x) -> prisoner($x).",
        "all $x: believe($x, event { prisoner(Bob) | person(Bob) }) -> eats($x).",
        "all $x: believe($x, event { prisoner(Bob) & person(Bob) }) -> eats($x).",
        "eats(every person also ~prisoner).",
    ] {
        let expected = CoreSession::new().assert_text(source).is_ok();
        if std::panic::catch_unwind(|| compare(source, InputIntent::Assertion, expected, None))
            .is_err()
        {
            failures.push(source);
        }
    }
    assert!(failures.is_empty(), "quotation mismatches: {failures:#?}");
}

#[test]
fn unresolved_generated_identities_cannot_receive_a_clean_verdict() {
    let subject = "derived_only(\"__abs_sentinel\"). believe(Adam, event { person(Bob) }).";
    CoreSession::new().assert_text(subject).unwrap();
    let check = checker(subject, InputIntent::Assertion);
    assert!(!verdict(&check, "checker_complete(\"program:0\")."));
    assert!(!verdict(&check, "checker_accepts(\"program:0\")."));
    assert!(verdict(
        &check,
        "checker_incomplete(\"program:0\", \"quotation_identity_declaration\")."
    ));
}

#[test]
fn nested_binders_and_relative_clause_boundaries() {
    let subjects = [
        "every the person $x: eats($x). all $x: ~eats($x) -> person($x).",
        "every person $x: eats($x). all $x: ~eats($x) -> person($x).",
        "every the person where prisoner $x: eats($x). all $x: ~eats($x) -> prisoner($x).",
        "some person $x: eats($x).",
        "some person $x: eats($x) & prisoner($x).",
        "the person $x: eats($x) & prisoner($x).",
        "some person $x: person($x) -> prisoner($x).",
        "the person $x: person($x) -> prisoner($x).",
        "every person $x: every animal $y: eats($x, $y).",
        "every person $x: every animal $y: eats($x, $y). all $x: ~eats($x) -> animal($x).",
        "all $x: person($x) -> (animal($x) <-> prisoner($x)).",
        "all $x: person($x) -> (animal($x) & (prisoner($x) -> eats($x))).",
        "all $x: person($x) -> (animal($x) & (all $y: eats($x, $y))).",
        "all $x: person($x) -> (animal($x) & (prisoner($x) <-> eats($x))).",
        "all $x: person($x) -> (animal($x) & (some dog $y: eats($x, $y))).",
        "eats(some loves(every animal)).",
        "eats(the loves(every animal)).",
        "eats(every loves(some animal)).",
        "eats(every loves(every animal)).",
        "eats(Bob where (person(it) & eats(Adam, it))).",
        "eats(Bob where eats(some loves(lover: it, loved: Adam))).",
        "eats(Bob where (eats(some loves(lover: it, loved: Adam)) & person(_))).",
        "eats(Bob where (eats(some loves(lover: it, loved: Adam)) & person(_) & animal(_))).",
        "eats(Bob where eats(it, Bob where person(it))).",
        "eats(Bob where (person(every animal) & person(it))).",
        "eats(the loves(exactly 1 animal)).",
        "all $x: person($x) -> eats(the loves(exactly 1 animal)).",
    ];
    let mut failed = Vec::new();
    for source in subjects {
        let native = CoreSession::new().assert_text(source);
        if std::panic::catch_unwind(|| {
            compare(source, InputIntent::Assertion, native.is_ok(), None)
        })
        .is_err()
        {
            failed.push((source, format!("{native:?}")));
        }
    }
    assert!(failed.is_empty(), "{failed:#?}");
}
