//! TEMPORARY batch converter for THE DROP test-port (deleted before commit).
//! Reads candidate Lojban strings (one per line) from the file in argv[1] and
//! prints TSV:
//!   OK\t<input>\t<klaro>        — converted AND round-trip canonically EQUAL
//!   FAIL\t<input>\t<reason>     — unparseable / unrenderable / NOT EQUAL
//! Multi-statement renders are joined with a single space; equality is checked
//! on the whole multi-root buffer, so `.i`-joined inputs are fully verified.

use nibli_verify::klaro_battery::{canonical, kompile};

fn kompile_lojban(text: &str) -> Result<nibli_types::logic::LogicBuffer, String> {
    let ast = gerna::parse_checked(text).map_err(|e| format!("gerna: {e}"))?;
    let mut buf = smuni::compile_from_gerna_ast(ast).map_err(|e| format!("smuni: {e}"))?;
    logji::transform_compute_nodes(&mut buf, &logji::default_compute_predicates());
    Ok(buf)
}

fn convert(line: &str) -> Result<String, String> {
    let ast = gerna::parse_checked(line).map_err(|e| {
        format!("gerna: {e}")
            .replace('\n', " | ")
            .replace('\t', " ")
    })?;
    let rendered = klaro::render::render(&ast).map_err(|e| format!("render: {e}"))?;
    let one_line = rendered.replace('\n', " ");
    let lojban_buf = kompile_lojban(line)?;
    let klaro_buf = kompile(&one_line).map_err(|e| format!("reparse: {e}"))?;
    if canonical(&lojban_buf) != canonical(&klaro_buf) {
        return Err(format!("NOT EQUAL after round-trip (rendered: {one_line})"));
    }
    Ok(one_line)
}

fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("usage: l2k_batch <candidates.txt>");
    let source = std::fs::read_to_string(&path).expect("read candidates");
    for line in source.lines() {
        if line.trim().is_empty() {
            continue;
        }
        match convert(line) {
            Ok(klaro) => println!("OK\t{line}\t{klaro}"),
            Err(e) => println!("FAIL\t{line}\t{e}"),
        }
    }
}
