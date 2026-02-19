use std::env;
use std::fs;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

fn main() {
    println!("cargo:rerun-if-changed=../jbovlaste-en.xml");

    let xml_path = "../jbovlaste-en.xml";
    let content = fs::read_to_string(xml_path).expect("Failed to read jbovlaste-en.xml");

    let mut map = phf_codegen::Map::new();

    // Iterate through every <valsi> block, completely bypassing XML strictness
    for block in content.split("<valsi ") {
        let word = extract_attribute(block, "word=\"");
        let typ = extract_attribute(block, "type=\"");

        if (typ == "gismu" || typ == "lujvo") && !word.is_empty() {
            if let Some(def_start) = block.find("<definition>") {
                if let Some(def_end) = block[def_start..].find("</definition>") {
                    // Extract the definition string (12 is the length of "<definition>")
                    let definition = &block[def_start + 12..def_start + def_end];

                    let arity = extract_arity(definition);
                    let arity_str = match arity {
                        5 => "5",
                        4 => "4",
                        3 => "3",
                        2 => "2",
                        _ => "1",
                    };

                    map.entry(word.to_string(), arity_str);
                }
            }
        }
    }

    let out_dir = env::var("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join("generated_dictionary.rs");
    let mut file = BufWriter::new(File::create(&dest_path).unwrap());

    writeln!(
        &mut file,
        "pub static JBOVLASTE_ARITIES: phf::Map<&'static str, usize> = \n{};",
        map.build()
    )
    .unwrap();
}

/// Helper to fast-forward through string bytes to extract attribute values
fn extract_attribute<'a>(block: &'a str, attr: &str) -> &'a str {
    if let Some(start) = block.find(attr) {
        let after_attr = &block[start + attr.len()..];
        if let Some(end) = after_attr.find('"') {
            return &after_attr[..end];
        }
    }
    ""
}

fn extract_arity(definition: &str) -> usize {
    let def = definition
        .replace(" ", "")
        .replace("_", "")
        .replace("<sub>", "")
        .replace("</sub>", "")
        .replace("{", "")
        .replace("}", "");

    if def.contains("x5") {
        5
    } else if def.contains("x4") {
        4
    } else if def.contains("x3") {
        3
    } else if def.contains("x2") {
        2
    } else {
        1
    }
}
