use std::io::Write;
use std::process::{Command, Stdio};

fn export(source: &str, query: bool) -> std::process::Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_nibli-ast"));
    command.args(["--emit-ast-facts", "-"]);
    if query {
        command.arg("--query");
    }
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(source.as_bytes())
        .unwrap();
    child.wait_with_output().unwrap()
}

#[test]
fn cli_exports_invalid_but_parseable_subjects_deterministically() {
    let source = include_str!("../../nibli-kr/tests/fixtures/reify_subject.nibli");
    let first = export(source, false);
    assert!(
        first.status.success(),
        "{}",
        String::from_utf8_lossy(&first.stderr)
    );
    assert_eq!(first.stdout, export(source, false).stdout);
    let text = String::from_utf8(first.stdout).unwrap();
    nibli_kr::parse_checked(&text).unwrap();
    assert_eq!(
        text,
        nibli_kr::reify::ast_to_nibli(
            &nibli_kr::parser::parse_statements(source).unwrap(),
            nibli_kr::reify::InputIntent::Assertion
        )
        .unwrap()
    );
    let query = export("person(Zed).", true);
    assert!(query.status.success());
    assert!(
        String::from_utf8(query.stdout)
            .unwrap()
            .contains("\"query\"")
    );
}

#[test]
fn parse_failure_emits_no_partial_facts() {
    let output = export("person(Zed). person(.", false);
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert!(!output.stderr.is_empty());
}
