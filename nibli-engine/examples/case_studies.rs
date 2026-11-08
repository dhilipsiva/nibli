//! Run the source-linked case studies: cargo run -p nibli-engine --example case_studies -- gdpr [--capture] [--no-materialize]
mod support {
    pub mod case_studies;
}
fn main() -> Result<(), String> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    let name = args.first().map(String::as_str).unwrap_or("gdpr");
    if !matches!(name, "gdpr" | "drug") {
        return Err("choose gdpr or drug".into());
    }
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap();
    let value = support::case_studies::run(
        root,
        name,
        !args.iter().any(|a| a == "--no-materialize"),
        args.iter().any(|a| a == "--capture"),
    )?;
    println!(
        "{}",
        serde_json::to_string_pretty(&value).map_err(|e| e.to_string())?
    );
    Ok(())
}
