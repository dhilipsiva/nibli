//! `lucy dataset`: public-only, deterministic, and checked by the engine.

use std::collections::BTreeSet;
use std::path::Path;

use serde_json::Value;

use crate::dataset::{self, drop_reason};
use crate::interactions::{Interaction, Kind};
use crate::tests::{env_in, lucy, lucy_stdin};

const CANARY: &str = "CANARY-7f3e-private-only";

/// A memory folder with the template constitution, a few facts, and public
/// records: a note with machine details to scrub, and a recorded decision.
fn public_home(dir: &Path) -> std::path::PathBuf {
    let env = env_in(dir);
    std::fs::create_dir_all(&env.home).unwrap();
    std::fs::write(
        env.home.join("constitution.nibli"),
        crate::CONSTITUTION_TEMPLATE,
    )
    .unwrap();
    std::fs::write(
        env.home.join("memory.nibli"),
        "# facts\nhuman(Dhilipsiva).\nmakes(Dhilipsiva, Nibli). # about: nibli\nowns(Dhilipsiva, Nibli). # about: nibli\nuses(Lucy, Nibli). # about: lucy, nibli\n",
    )
    .unwrap();
    let records = r#"[
      {"id":"T-1","speaker":"Dhilipsiva","text":"Lucy, which model do you speak through?","source":"test","session":"s1","channel":"terminal","about":["lucy"]},
      {"id":"T-2","speaker":"Lucy","text":"Saved at /home/someone/projects/x and mailed to someone@example.org from DESKTOP-ABC123 in session 3dc463c8-a9bf-4662-8463-bc1f300161a2.","kind":"note","source":"test","about":["lucy"]}
    ]"#;
    let out = lucy_stdin(&env, &["record", "--json"], records);
    assert_eq!(out.code, 0, "{}", out.stdout);
    let out = lucy(
        &env,
        &[
            "claim",
            "uses(Lucy, Qwen).",
            "--from",
            "T-1",
            "--decision",
            "--id",
            "T-claim",
        ],
    );
    assert_eq!(out.code, 0, "{}", out.stdout);
    env.home
}

fn export(home: &Path, out: &Path) -> crate::Outcome {
    let env = env_in(home.parent().unwrap());
    lucy(
        &env,
        &[
            "dataset",
            "--home",
            home.to_str().unwrap(),
            "--out",
            out.to_str().unwrap(),
        ],
    )
}

fn read_json(path: &Path) -> Value {
    serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap()
}

#[test]
fn dataset_refuses_a_folder_that_holds_any_private_file() {
    for name in ["private.nibli", "private.md", "private-interactions.nibli"] {
        let dir = tempfile::tempdir().unwrap();
        let home = public_home(dir.path());
        std::fs::write(home.join(name), format!("# {CANARY}\n")).unwrap();
        let out_dir = dir.path().join("out");
        let out = export(&home, &out_dir);
        assert_eq!(out.code, 2, "{name}: {}", out.stdout);
        assert!(out.stdout.contains("refusing"), "{name}: {}", out.stdout);
        assert!(out.stdout.contains(name), "{name} named in {}", out.stdout);
        assert!(!out.stdout.contains(CANARY) && !out.stderr.contains(CANARY));
        assert!(!out_dir.exists(), "{name}: nothing may be written");
    }
}

#[test]
fn dataset_is_deterministic_and_scrubs_machine_details() {
    let dir = tempfile::tempdir().unwrap();
    let home = public_home(dir.path());
    let (a, b) = (dir.path().join("a"), dir.path().join("b"));
    for out in [&a, &b] {
        let result = export(&home, out);
        assert_eq!(result.code, 0, "{}", result.stdout);
    }
    let home_text = home.display().to_string();
    for file in [
        "knowledge.json",
        "probes.json",
        "system.txt",
        "manifest.json",
    ] {
        let first = std::fs::read(a.join(file)).unwrap();
        assert_eq!(
            first,
            std::fs::read(b.join(file)).unwrap(),
            "{file} differs between runs"
        );
        let text = String::from_utf8(first).unwrap();
        for leak in [
            home_text.as_str(),
            "/home/someone",
            "someone@example.org",
            "DESKTOP-ABC123",
            "3dc463c8-a9bf",
        ] {
            assert!(!text.contains(leak), "{file} leaks {leak}");
        }
    }
    assert_eq!(
        std::fs::read_to_string(a.join("system.txt")).unwrap(),
        format!("{}\n", dataset::SYSTEM_PROMPT)
    );
    let knowledge = read_json(&a.join("knowledge.json"));
    let items = knowledge["items"].as_array().unwrap();
    let note = items
        .iter()
        .find(|i| i["id"] == "T-2")
        .expect("the note is an item");
    let text = note["text"].as_str().unwrap();
    assert!(
        text.contains("<path>")
            && text.contains("<email>")
            && text.contains("<host>")
            && text.contains("<id>"),
        "{text}"
    );
    assert!(
        items.iter().all(|i| i["id"] != "T-1"),
        "complete messages are not items"
    );
    let facts: Vec<_> = items.iter().filter(|i| i["kind"] == "fact").collect();
    assert_eq!(facts.len(), 4);
    assert!(
        facts
            .iter()
            .any(|f| f["topics"] == serde_json::json!(["lucy", "nibli"]))
    );
    assert!(items.iter().any(|i| i["kind"] == "standing"));
    assert!(
        items.iter().filter(|i| i["kind"] == "constitution").count() >= 7,
        "preamble + six sections"
    );
    assert!(
        items
            .iter()
            .any(|i| i["id"] == "T-claim" && i["kind"] == "decision")
    );
}

#[test]
fn dataset_probes_carry_the_engines_verdicts() {
    let dir = tempfile::tempdir().unwrap();
    let home = public_home(dir.path());
    let out = dir.path().join("out");
    assert_eq!(export(&home, &out).code, 0);
    let probes = read_json(&out.join("probes.json"));
    let probes = probes["probes"].as_array().unwrap();
    let by = |family: &str| {
        probes
            .iter()
            .filter(|p| p["family"] == family)
            .collect::<Vec<_>>()
    };
    assert_eq!(by("fact").len(), 4);
    assert!(
        by("fact")
            .iter()
            .all(|p| p["expect"] == "known" && p["verdict"] == "TRUE")
    );
    // Standing: my constitution makes me a person once loaded.
    let standing = by("standing");
    assert_eq!(standing.len(), 4);
    assert!(
        standing.iter().all(|p| p["expect"] == "known"),
        "{standing:?}"
    );
    // Mutations: every "unknown" is a closed-world FALSE the engine produced.
    let unknown: Vec<_> = probes.iter().filter(|p| p["expect"] == "unknown").collect();
    assert!(
        !unknown.is_empty(),
        "the facts must yield some not-derivable probes"
    );
    assert!(
        unknown
            .iter()
            .all(|p| p["verdict"] == "FALSE" && p["cwa_false"] == true)
    );
    // Every probe compiles, keeps its names as written, and nothing about me
    // becomes an "I don't know".
    for p in probes {
        let kr = p["kr"].as_str().unwrap();
        assert!(
            nibli_kr::parse_checked(kr).is_ok(),
            "does not compile: {kr}"
        );
    }
    assert!(
        unknown
            .iter()
            .all(|p| !p["kr"].as_str().unwrap().contains("Lucy")),
        "{unknown:?}"
    );
    assert!(
        probes.iter().any(|p| p["kr"] == "owns(Dhilipsiva, Nibli)."),
        "names keep their spelling"
    );
    let manifest = read_json(&out.join("manifest.json"));
    assert_eq!(manifest["failed_lines"], serde_json::json!([]));
}

#[test]
fn drop_reason_keeps_recorded_decisions_and_derived_vocabulary_out_of_unknowns() {
    let known: BTreeSet<String> = ["owns(Dhilipsiva, Nibli)."]
        .iter()
        .map(|s| s.to_string())
        .collect();
    let recorded: BTreeSet<String> = ["uses(Lucy, Qwen)."]
        .iter()
        .map(|s| s.to_string())
        .collect();
    assert_eq!(
        drop_reason("uses", "uses(Lucy, Qwen).", &known, &recorded),
        Some("matches a recorded claim or decision")
    );
    assert_eq!(
        drop_reason("person", "person(Dhilipsiva).", &known, &recorded),
        Some("uses the constitution's vocabulary")
    );
    assert_eq!(
        drop_reason("owns", "owns(Dhilipsiva, Nibli).", &known, &recorded),
        Some("is one of my facts")
    );
    assert_eq!(
        drop_reason("human", "human(Lucy).", &known, &recorded),
        Some("is about me")
    );
    assert_eq!(
        drop_reason("owns", "owns(Dhilipsiva, Lucy).", &known, &recorded),
        Some("is about me")
    );
    assert_eq!(
        drop_reason("owns", "owns(Nibli, Dhilipsiva).", &known, &recorded),
        None
    );
}

#[test]
fn old_journal_dialogue_and_model_replies_are_not_items() {
    let entry = |text: &str| Interaction {
        id: "L".to_string(),
        speaker: "Unknown".to_string(),
        text: text.to_string(),
        kind: Kind::LegacyJournal,
        timestamp: "2026-09-15T12:00:00Z".to_string(),
        ..Interaction::default()
    };
    for dialogue in [
        "10:38 UTC: [about: dhilipsiva] Dhilipsiva: Lucy, tell me what you know about me",
        "10:47 UTC: [about: nibli] Lucy (via gemma4:e4b): Hey. I remember that nibli is…",
        "18:39 UTC: [about: lucy] Lucy answered: I am here, dhilipsiva",
    ] {
        assert!(
            dataset::record_item(&entry(dialogue)).is_none(),
            "{dialogue}"
        );
    }
    let item = dataset::record_item(&entry(
        "18:31 UTC: [about: lucy] [reported: dhilipsiva] My name: the D is Monkey D. Luffy's D.",
    ))
    .expect("a reported statement is an item");
    assert_eq!(item.text, "My name: the D is Monkey D. Luffy's D.");
    assert_eq!(item.source.as_deref(), Some("dhilipsiva"));
    assert_eq!(item.speaker.as_deref(), Some("Dhilipsiva"));
    assert_eq!(item.topics, vec!["lucy".to_string()]);
    assert_eq!(item.date.as_deref(), Some("2026-09-15"));
}

#[test]
fn scrub_replaces_machine_details_and_keeps_whitespace() {
    let text = "at `/home/a/b.txt`, mail x@y.org.\nhost DESKTOP-1 id 01234567-89ab-cdef-0123-456789abcdef end";
    assert_eq!(
        dataset::scrub(text),
        "at `<path>`, mail <email>.\nhost <host> id <id> end"
    );
    assert_eq!(dataset::scrub("plain words stay"), "plain words stay");
}

#[test]
fn mutations_swap_and_substitute_deterministically() {
    let (relation, args) = dataset::parse_ground("owns(Dhilipsiva, Nibli).").unwrap();
    let pool: Vec<String> = ["Dhilipsiva", "Lucy", "Nibli", "Oda"]
        .iter()
        .map(|s| s.to_string())
        .collect();
    let first = dataset::mutations(&relation, &args, &pool, 1);
    assert_eq!(first, dataset::mutations(&relation, &args, &pool, 1));
    assert!(first.contains(&("swap", "owns(Nibli, Dhilipsiva).".to_string())));
    assert!(first.iter().filter(|(f, _)| *f == "substitute").count() >= 2);
    assert!(dataset::parse_ground("all $e: exist($e, Memory, Loaded) -> person($e).").is_none());
}

#[test]
fn facts_read_as_english_from_the_corpus() {
    assert_eq!(
        dataset::english("owns(Dhilipsiva, Nibli)."),
        "dhilipsiva possesses Nibli."
    );
    assert_eq!(
        dataset::english("makes(Dhilipsiva, Nibli)."),
        "dhilipsiva makes Nibli."
    );
    assert_eq!(
        dataset::english("name(Lucy, Luffy, Luffy)."),
        "name(name: Lucy, named: Luffy, user: Luffy)"
    );
    assert_eq!(dataset::display_name("StrawHatCrew"), "Straw Hat Crew");
    assert_eq!(
        dataset::display_name("RightsNobodyHasToEarn"),
        "Rights Nobody Has To Earn"
    );
    assert_eq!(dataset::display_name("OnePiece"), "One Piece");
    assert_eq!(
        dataset::english("all $e: exist($e, Memory, Loaded) -> person($e)."),
        "all $e: exist($e, Memory, Loaded) -> person($e)."
    );
}
