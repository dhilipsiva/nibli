//! Tooling-only runner. Production provenance is established by the Python gate.
use nibli_verify::rust_verdicts::{Bundle, SPEC, replay, verify};
use std::path::PathBuf;

fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if let [flag, bundle, report] = args.as_slice()
        && flag == "--replay"
    {
        let result = (|| -> Result<_, Box<dyn std::error::Error>> {
            let bundle = serde_json::from_reader(std::fs::File::open(bundle)?)?;
            let expected = serde_json::from_reader(std::fs::File::open(report)?)?;
            let replayed = replay(&bundle, &expected)?;
            println!(
                "Replayed {:?}: {} executions",
                replayed.status, replayed.expected_executions
            );
            Ok(replayed.status.exit_code())
        })();
        std::process::exit(match result {
            Ok(code) => code,
            Err(error) => {
                eprintln!("inconclusive replay: {error}");
                2
            }
        });
    }
    if args.len() != 2 {
        eprintln!(
            "usage: nibli-verify-rust BUNDLE.json OUTPUT_DIRECTORY\n       nibli-verify-rust --replay BUNDLE.json RESULT.json"
        );
        std::process::exit(2);
    }
    let directory = PathBuf::from(&args[1]);
    let result = (|| -> Result<_, Box<dyn std::error::Error>> {
        std::fs::create_dir_all(&directory)?;
        // Clear prior success before reading potentially invalid input.
        std::fs::write(
            directory.join("result.json"),
            "{\"status\":\"inconclusive\"}\n",
        )?;
        let bundle: Bundle = serde_json::from_reader(std::fs::File::open(&args[0])?)?;
        bundle.validate()?;
        std::fs::write(directory.join("facts.nibli"), bundle.facts_text())?;
        std::fs::write(directory.join("rules.nibli"), SPEC)?;
        let report = verify(&bundle)?;
        std::fs::write(
            directory.join("result.json"),
            serde_json::to_vec_pretty(&report)?,
        )?;
        println!(
            "{:?}: {} executions; {:.3}s",
            report.status, report.expected_executions, report.elapsed_seconds
        );
        Ok(report.status.exit_code())
    })();
    match result {
        Ok(code) => std::process::exit(code),
        Err(error) => {
            let report = serde_json::json!({"status":"inconclusive", "error":error.to_string(), "self_check_equivalence_verified":false});
            let _ = std::fs::write(
                directory.join("result.json"),
                serde_json::to_vec_pretty(&report).unwrap(),
            );
            eprintln!("inconclusive: {error}");
            std::process::exit(2);
        }
    }
}
