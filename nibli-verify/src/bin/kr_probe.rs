//! TEMPORARY KR compile probe for THE DROP test-port (deleted before commit).
//! For each line of argv[1]:
//!   `<kr>`            — kompile and print OK\t<line>\t<canonical prefix>
//!                       or ERR\t<line>\t<error>.
//!   `<kr>\t<lojban>`  — compile BOTH sides, print EQUAL / DIFFER / errors.

use nibli_verify::klaro_battery::{canonical, kompile};

fn kompile_lojban(text: &str) -> Result<nibli_types::logic::LogicBuffer, String> {
    let ast = gerna::parse_checked(text).map_err(|e| format!("gerna: {e}"))?;
    let mut buf = smuni::compile_from_gerna_ast(ast).map_err(|e| format!("smuni: {e}"))?;
    logji::transform_compute_nodes(&mut buf, &logji::default_compute_predicates());
    Ok(buf)
}

fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("usage: kr_probe <lines.txt>");
    let source = std::fs::read_to_string(&path).expect("read lines");
    for line in source.lines() {
        if line.trim().is_empty() {
            continue;
        }
        if let Some((kr, lojban)) = line.split_once('\t') {
            let k = kompile(kr).map(|b| canonical(&b));
            let l = kompile_lojban(lojban).map(|b| canonical(&b));
            match (k, l) {
                (Ok(kc), Ok(lc)) if kc == lc => println!("EQUAL\t{kr}\t{lojban}"),
                (Ok(kc), Ok(lc)) => {
                    println!("DIFFER\t{kr}\t{lojban}");
                    println!("  kr:     {}", &kc.chars().take(200).collect::<String>());
                    println!("  lojban: {}", &lc.chars().take(200).collect::<String>());
                }
                (Err(e), _) => println!("KR-ERR\t{kr}\t{}", e.replace('\n', " | ")),
                (_, Err(e)) => println!("LOJBAN-ERR\t{lojban}\t{}", e.replace('\n', " | ")),
            }
            continue;
        }
        match kompile(line) {
            Ok(buf) => {
                let c = canonical(&buf);
                let prefix: String = c.chars().take(220).collect();
                println!("OK\t{line}\t{prefix}");
            }
            Err(e) => {
                let msg = e.replace('\n', " | ");
                println!("ERR\t{line}\t{msg}");
            }
        }
    }
}
