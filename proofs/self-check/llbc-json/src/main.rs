//! Use Charon's pinned, typed reader rather than duplicating its sharing codec.
use serde::Deserialize;
use std::io::{BufReader, BufWriter};

fn main() {
    if let Err(error) = run() {
        eprintln!("nibli-llbc-json: {error}");
        std::process::exit(2);
    }
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let path = std::env::args().nth(1).ok_or("expected an LLBC file")?;
    let mut decoder =
        serde_json::Deserializer::from_reader(BufReader::new(std::fs::File::open(path)?));
    decoder.disable_recursion_limit();
    let mut data =
        charon_lib::export::CrateData::deserialize(serde_stacker::Deserializer::new(&mut decoder))?;
    decoder.end()?;
    if data.has_errors {
        return Err("incomplete Charon extraction".into());
    }
    data.translated.options.no_dedup_serialized_ast = true;
    serde_json::to_writer(BufWriter::new(std::io::stdout().lock()), &data)?;
    Ok(())
}
