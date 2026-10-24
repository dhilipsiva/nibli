//! Static semantic verification over reified parser trees. The subject is never
//! asserted into the checker: only its structural facts are admitted.
use nibli_kr::{
    parser::parse_statements,
    reify::{self, InputIntent},
};
use nibli_session::CoreSession;
use nibli_types::logic::{LogicBuffer, LogicalTerm, QueryResult};
use std::sync::OnceLock;

/// The shipped meta-circular specification.
pub const SPEC: &str = include_str!("../spec/nibli_checker.nibli");
const CHECKER: &str = SPEC;

/// Build an isolated checker. A refusal or incomplete analysis is an error,
/// never evidence that the subject passed.
pub fn session(subject: &str, intent: InputIntent) -> Result<CoreSession, String> {
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
    let tree = parse_statements(subject).map_err(|e| format!("{e:?}"))?;
    let facts = reify::reify(&tree, intent).map_err(|e| format!("{e:?}"))?;
    for fact in facts.facts {
        let args = fact
            .arguments
            .into_iter()
            .map(LogicalTerm::Constant)
            .collect::<Vec<_>>();
        let buffer = nibli_semantics::compile_injected_fact(fact.relation, &args)
            .map_err(|e| format!("{e:?}"))?;
        compiled.push((buffer, format!("reified {}", fact.relation)));
    }
    let (kb, _) =
        nibli_reason::KnowledgeBase::from_compiled_batch(compiled).map_err(|e| format!("{e:?}"))?;
    Ok(CoreSession::with_kb(kb))
}

/// Require a complete Boolean result from a checker relation.
pub fn verdict(session: &CoreSession, query: &str) -> Result<bool, String> {
    let result = session.query_text(query).map_err(|e| format!("{e:?}"))?;
    let (complete, refused) = session
        .materialization_report()
        .map_err(|e| format!("{e:?}"))?;
    let relation = query.split('(').next().ok_or("missing relation")?;
    if !complete.iter().any(|r| r == relation) {
        return Err(format!("incomplete {relation}: {refused:?}"));
    }
    match result {
        QueryResult::True => Ok(true),
        QueryResult::False => Ok(false),
        other => Err(format!("incomplete verdict: {other:?}")),
    }
}
