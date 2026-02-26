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
    let mut gismu_count: usize = 0;
    let mut lujvo_count: usize = 0;
    let mut override_count: usize = 0;

    // Iterate through every <valsi> block, bypassing XML strictness
    // (jbovlaste XML is riddled with formatting errors that crash strict parsers)
    for block in content.split("<valsi ") {
        let word = extract_attribute(block, "word=\"");
        let typ = extract_attribute(block, "type=\"");

        if word.is_empty() || (typ != "gismu" && typ != "lujvo") {
            continue;
        }

        // Check hardcoded overrides first (authoritative for core gismu)
        let arity = if let Some(&known) = CORE_GISMU_ARITIES.iter().find(|(w, _)| *w == word) {
            override_count += 1;
            known.1
        } else if let Some(definition) = extract_definition(block) {
            extract_arity(definition)
        } else {
            // No definition found — default to 2 (most common arity)
            2
        };

        let arity_str = match arity {
            5 => "5",
            4 => "4",
            3 => "3",
            2 => "2",
            _ => "1",
        };

        map.entry(word.to_string(), arity_str);

        match typ {
            "gismu" => gismu_count += 1,
            "lujvo" => lujvo_count += 1,
            _ => {}
        }
    }

    // Build-time diagnostics
    let total = gismu_count + lujvo_count;
    println!(
        "cargo:warning=jbovlaste: {} entries ({} gismu, {} lujvo, {} from hardcoded overrides)",
        total, gismu_count, lujvo_count, override_count
    );

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

/// Extracts an XML attribute value from a block using string scanning.
fn extract_attribute<'a>(block: &'a str, attr: &str) -> &'a str {
    if let Some(start) = block.find(attr) {
        let after_attr = &block[start + attr.len()..];
        if let Some(end) = after_attr.find('"') {
            return &after_attr[..end];
        }
    }
    ""
}

/// Extracts the <definition> text from a valsi block.
fn extract_definition(block: &str) -> Option<&str> {
    let start = block.find("<definition>")?;
    let rest = &block[start + 12..]; // 12 = "<definition>".len()
    let end = rest.find("</definition>")?;
    Some(&rest[..end])
}

/// Extracts the highest place variable (x1..x5) from a jbovlaste definition.
///
/// Handles all known formats in jbovlaste:
///   - `$x_1$`          (LaTeX)
///   - `{x1}` / `{x2}`  (braces)
///   - `x1` / `x2`      (plain)
///   - `x<sub>1</sub>`   (HTML subscript)
///   - `x_1`             (underscore)
fn extract_arity(definition: &str) -> usize {
    let mut max_place: usize = 0;
    let bytes = definition.as_bytes();
    let len = bytes.len();
    let mut i = 0;

    while i < len {
        if bytes[i] == b'x' || bytes[i] == b'X' {
            // Word boundary check: 'x' must not be inside a word like "approximately"
            let has_boundary = i == 0 || !bytes[i - 1].is_ascii_alphanumeric();
            if has_boundary {
                let mut j = i + 1;

                // Skip optional formatting between 'x' and the digit:
                //   '_', '$', '{', '}', ' '  →  wrappers/separators
                //   '<...>'                   →  HTML tags like <sub>
                while j < len {
                    match bytes[j] {
                        b'_' | b'$' | b'{' | b'}' | b' ' => j += 1,
                        b'<' => {
                            if let Some(close) = definition[j..].find('>') {
                                j += close + 1;
                            } else {
                                break;
                            }
                        }
                        _ => break,
                    }
                }

                if j < len && bytes[j].is_ascii_digit() {
                    let digit = (bytes[j] - b'0') as usize;
                    if digit >= 1 && digit <= 5 {
                        max_place = max_place.max(digit);
                    }
                }
            }
        }
        i += 1;
    }

    // Every predicate has at least 1 place
    max_place.max(1)
}

/// Hardcoded arities for core gismu where definition text is unreliable.
///
/// Source: CLL Chapter 2 & official gismu list.
/// Only includes gismu commonly misdetected by definition parsing.
const CORE_GISMU_ARITIES: &[(&str, usize)] = &[
    // 5-place gismu
    ("klama", 5), // x1 goes to x2 from x3 via x4 by x5
    ("ctuca", 5), // x1 teaches x2 to x3 about x4 by method x5
    ("ciska", 5), // x1 inscribes x2 on x3 with instrument x4 in x5
    ("mrilu", 5), // x1 mails x2 to x3 from x4 by x5
    ("bevri", 5), // x1 carries x2 to x3 from x4 over path x5
    ("vecnu", 4), // x1 sells x2 to x3 for x4
    ("dunda", 3), // x1 gives x2 to x3
    ("prami", 2), // x1 loves x2
    ("gerku", 2), // x1 is a dog of breed x2
    ("mlatu", 2), // x1 is a cat of breed x2
    ("cmene", 3), // x1 is a name for x2 used by x3
    ("cusku", 3), // x1 expresses x2 to x3
    ("djuno", 4), // x1 knows x2 about x3 by epistemology x4
    ("jimpe", 2), // x1 understands x2
    ("gasnu", 2), // x1 does x2
    ("penmi", 3), // x1 meets x2 at x3
    ("tavla", 4), // x1 talks to x2 about x3 in language x4
    ("catra", 2), // x1 kills x2
    ("citka", 2), // x1 eats x2
    ("pinxe", 2), // x1 drinks x2
    ("cadzu", 3), // x1 walks on x2 using x3
    ("bajra", 4), // x1 runs on x2 using x3 with gait x4
    ("viska", 3), // x1 sees x2 under conditions x3
    ("tirna", 3), // x1 hears x2 from source x3
    ("nelci", 2), // x1 likes x2
    ("djica", 3), // x1 desires x2 for purpose x3
    ("nitcu", 3), // x1 needs x2 for purpose x3
    ("kakne", 2), // x1 is able to do x2
    ("ckana", 2), // x1 is a bed for x2
    ("zdani", 2), // x1 is a home of x2
    ("zarci", 3), // x1 is a market for x2 operated by x3
    ("bridi", 3), // x1 is a predicate with relation x2 among x3
    ("jbena", 4), // x1 is born to x2 at x3 in x4
    ("morsi", 1), // x1 is dead
    ("sutra", 2), // x1 is fast at x2
    ("melbi", 3), // x1 is beautiful to x2 by standard x3
    ("barda", 3), // x1 is big in x2 by standard x3
    ("cmalu", 3), // x1 is small in x2 by standard x3
    ("xamgu", 3), // x1 is good for x2 by standard x3
    ("xlali", 3), // x1 is bad for x2 by standard x3
    ("blanu", 1), // x1 is blue
    ("xunre", 1), // x1 is red
    ("pelxu", 1), // x1 is yellow
    ("crino", 1), // x1 is green
];
