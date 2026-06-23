use std::env;
use std::fs;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

fn main() {
    println!("cargo:rerun-if-changed=../jbovlaste-en.xml");

    let xml_path = "../jbovlaste-en.xml";
    let content = fs::read_to_string(xml_path).ok();

    // Collect entries first (phf_codegen borrows value strings for the map's lifetime)
    let mut entries: Vec<(String, String)> = Vec::new();
    let mut gismu_count: usize = 0;
    let mut lujvo_count: usize = 0;
    let mut cmavo_count: usize = 0;

    if let Some(content) = content {
        for block in content.split("<valsi ") {
            let word = extract_attribute(block, "word=\"");
            let typ = extract_attribute(block, "type=\"");

            if word.is_empty() {
                continue;
            }

            match typ {
                "gismu" | "lujvo" => {
                    let arity = if let Some(&(_, a)) =
                        CORE_GISMU_ARITIES.iter().find(|(w, _)| *w == word)
                    {
                        a
                    } else if let Some(definition) = extract_definition(block) {
                        extract_arity(definition)
                    } else {
                        2
                    };

                    let gloss = if let Some(&(_, g)) =
                        GISMU_GLOSS_OVERRIDES.iter().find(|(w, _)| *w == word)
                    {
                        g
                    } else if let Some(&(_, _, g)) =
                        FALLBACK_GISMU_ENTRIES.iter().find(|(w, _, _)| *w == word)
                    {
                        g
                    } else {
                        extract_glossword(block).unwrap_or(word)
                    };
                    let escaped_gloss = escape_str(gloss);
                    let template = lookup_template(word);
                    let value = format!(
                        "DictEntry {{ arity: Some({}), gloss: \"{}\", template: \"{}\" }}",
                        arity,
                        escaped_gloss,
                        escape_str(template)
                    );
                    entries.push((word.to_string(), value));

                    match typ {
                        "gismu" => gismu_count += 1,
                        "lujvo" => lujvo_count += 1,
                        _ => {}
                    }
                }
                "cmavo" | "cmavo-compound" => {
                    let gloss = if let Some(&(_, g)) =
                        CMAVO_GLOSS_OVERRIDES.iter().find(|(w, _)| *w == word)
                    {
                        g
                    } else {
                        extract_glossword(block).unwrap_or(word)
                    };
                    let escaped_gloss = escape_str(gloss);
                    let value = format!(
                        "DictEntry {{ arity: None, gloss: \"{}\", template: \"\" }}",
                        escaped_gloss
                    );
                    entries.push((word.to_string(), value));
                    cmavo_count += 1;
                }
                _ => continue,
            }
        }
    } else {
        println!("cargo:warning=jbovlaste-en.xml not found, using fallback dictionary entries");
        for (word, arity, gloss) in FALLBACK_GISMU_ENTRIES {
            let value = format!(
                "DictEntry {{ arity: Some({}), gloss: \"{}\", template: \"{}\" }}",
                arity,
                escape_str(gloss),
                escape_str(lookup_template(word))
            );
            entries.push(((*word).to_string(), value));
            gismu_count += 1;
        }
        // Tier-1 curated gloss overrides (e.g. bilga->must, curmi->permit) win over
        // the jbovlaste glossword in the XML branch above; reproduce them here so the
        // no-XML build exposes the same glosses (the 3-tier chain documented in the
        // dictionary). Skip any word the fallback list already provides to avoid a
        // phf duplicate key; arity mirrors the XML branch's default (CORE or 2).
        for (word, gloss) in GISMU_GLOSS_OVERRIDES {
            if FALLBACK_GISMU_ENTRIES.iter().any(|(w, _, _)| w == word) {
                continue;
            }
            let arity = CORE_GISMU_ARITIES
                .iter()
                .find(|(w, _)| w == word)
                .map(|(_, a)| *a)
                .unwrap_or(2);
            let value = format!(
                "DictEntry {{ arity: Some({}), gloss: \"{}\", template: \"{}\" }}",
                arity,
                escape_str(gloss),
                escape_str(lookup_template(word))
            );
            entries.push(((*word).to_string(), value));
            gismu_count += 1;
        }
        for (word, gloss) in CMAVO_GLOSS_OVERRIDES {
            let value = format!(
                "DictEntry {{ arity: None, gloss: \"{}\", template: \"\" }}",
                escape_str(gloss)
            );
            entries.push(((*word).to_string(), value));
            cmavo_count += 1;
        }
    }

    let mut map = phf_codegen::Map::new();
    for (key, value) in &entries {
        map.entry(key.clone(), value.as_str());
    }

    let total = gismu_count + lujvo_count + cmavo_count;
    println!(
        "cargo:warning=dictionary: {} entries ({} gismu, {} lujvo, {} cmavo)",
        total, gismu_count, lujvo_count, cmavo_count
    );

    let out_dir = env::var("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join("generated_dictionary.rs");
    let mut file = BufWriter::new(File::create(&dest_path).unwrap());

    writeln!(
        &mut file,
        "pub static DICTIONARY: phf::Map<&'static str, DictEntry> = \n{};",
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
    let rest = &block[start + 12..];
    let end = rest.find("</definition>")?;
    Some(&rest[..end])
}

/// Extracts the first <glossword word="..."> value from a valsi block.
fn extract_glossword<'a>(block: &'a str) -> Option<&'a str> {
    let attr = "<glossword word=\"";
    let start = block.find(attr)?;
    let rest = &block[start + attr.len()..];
    let end = rest.find('"')?;
    let gloss = &rest[..end];
    if gloss.is_empty() { None } else { Some(gloss) }
}

/// Extracts the highest place variable (x1..x5) from a jbovlaste definition.
fn extract_arity(definition: &str) -> usize {
    let mut max_place: usize = 0;
    let bytes = definition.as_bytes();
    let len = bytes.len();
    let mut i = 0;

    while i < len {
        if bytes[i] == b'x' || bytes[i] == b'X' {
            let has_boundary = i == 0 || !bytes[i - 1].is_ascii_alphanumeric();
            if has_boundary {
                let mut j = i + 1;
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

    max_place.max(1)
}

/// Look up a curated English place-frame template for a gismu/lujvo.
/// Returns "" when none is curated (the renderer falls back to a generic frame).
fn lookup_template(word: &str) -> &'static str {
    GISMU_PLACE_TEMPLATES
        .iter()
        .find(|(w, _)| *w == word)
        .map(|(_, t)| *t)
        .unwrap_or("")
}

/// Escape a string for embedding in a Rust string literal.
/// Decodes XML entities first, then escapes for Rust.
fn escape_str(s: &str) -> String {
    // 1. Decode XML entities
    let decoded = s
        .replace("&amp;", "&")
        .replace("&apos;", "'")
        .replace("&lt;", "<")
        .replace("&gt;", ">")
        .replace("&quot;", "\"");
    // 2. Escape for Rust string literal
    decoded
        .replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
}

/// Hardcoded arities for core gismu where definition text is unreliable.
const CORE_GISMU_ARITIES: &[(&str, usize)] = &[
    ("klama", 5),
    ("ctuca", 5),
    ("ciska", 5),
    ("mrilu", 5),
    ("bevri", 5),
    ("vecnu", 4),
    ("dunda", 3),
    ("prami", 2),
    ("gerku", 2),
    ("mlatu", 2),
    ("cmene", 3),
    ("cusku", 3),
    ("djuno", 4),
    ("jimpe", 2),
    ("gasnu", 2),
    ("penmi", 3),
    ("tavla", 4),
    ("catra", 2),
    ("citka", 2),
    ("pinxe", 2),
    ("cadzu", 3),
    ("bajra", 4),
    ("viska", 3),
    ("tirna", 3),
    ("nelci", 2),
    ("djica", 3),
    ("nitcu", 3),
    ("kakne", 2),
    ("ckana", 2),
    ("zdani", 2),
    ("zarci", 3),
    ("bridi", 3),
    ("jbena", 4),
    ("morsi", 1),
    ("sutra", 2),
    ("melbi", 3),
    ("barda", 3),
    ("cmalu", 3),
    ("xamgu", 3),
    ("xlali", 3),
    ("blanu", 1),
    ("xunre", 1),
    ("pelxu", 1),
    ("crino", 1),
];

/// Minimal fallback when the jbovlaste XML export is absent locally.
const FALLBACK_GISMU_ENTRIES: &[(&str, usize, &str)] = &[
    ("klama", 5, "come"),
    ("ctuca", 5, "teach"),
    ("ciska", 5, "write"),
    ("mrilu", 5, "mail"),
    ("bevri", 5, "carry"),
    ("vecnu", 4, "sell"),
    ("dunda", 3, "give"),
    ("prami", 2, "love"),
    ("gerku", 2, "dog"),
    ("mlatu", 2, "cat"),
    ("cmene", 3, "name"),
    ("cusku", 3, "express"),
    ("djuno", 4, "know"),
    ("jimpe", 2, "understand"),
    ("gasnu", 2, "do"),
    ("penmi", 3, "meet"),
    ("tavla", 4, "talk"),
    ("catra", 2, "kill"),
    ("citka", 2, "eat"),
    ("pinxe", 2, "drink"),
    ("cadzu", 3, "walk"),
    ("bajra", 4, "run"),
    ("viska", 3, "see"),
    ("tirna", 3, "hear"),
    ("nelci", 2, "like"),
    ("djica", 3, "desire"),
    ("nitcu", 3, "need"),
    ("kakne", 2, "can"),
    ("ckana", 2, "bed"),
    ("zdani", 2, "home"),
    ("zarci", 3, "market"),
    ("bridi", 3, "predicate"),
    ("jbena", 4, "born"),
    ("morsi", 1, "dead"),
    ("sutra", 2, "fast"),
    ("melbi", 3, "beautiful"),
    ("barda", 3, "big"),
    ("cmalu", 3, "small"),
    ("xamgu", 3, "good"),
    ("xlali", 3, "bad"),
    ("blanu", 1, "blue"),
    ("xunre", 1, "red"),
    ("pelxu", 1, "yellow"),
    ("crino", 1, "green"),
    ("prenu", 1, "person"),
    ("pilji", 3, "multiply"),
    ("sumji", 3, "sum"),
    ("dilcu", 3, "divide"),
    ("danlu", 2, "animal"),
    ("jmive", 1, "live"),
];

/// Curated gloss overrides for gismu where the first jbovlaste glossword
/// is alphabetically accidental rather than canonical (e.g. gerku's
/// glosswords are bitch/canine/dog — "dog" is the right back-translation).
/// Consulted before FALLBACK_GISMU_ENTRIES and extract_glossword.
const GISMU_GLOSS_OVERRIDES: &[(&str, &str)] = &[("bilga", "must"), ("curmi", "permit")];

/// Curated English place-frame templates, keyed by gismu/lujvo, using `{x1}`..`{x5}`
/// placeholders. Covers the predicates the shipped corpora (`readme.lojban`,
/// `gdpr.lojban`, `drug-interactions.lojban`) actually use; everything else falls
/// back to a generic gloss-based frame in the renderer. Templates are written so
/// the filled form reads as a complete English clause. Keep to 1-/2-place frames
/// where the reading is unambiguous; higher-arity frames spell every place so the
/// renderer can drop trailing unfilled (`zo'e`) places cleanly.
///
/// NOTE: templates are keyed on the bare predicate name. `se`/`te`/… conversion is
/// already reflected in the IR's argument order, so the same template renders both
/// `prami` and `se prami` correctly (the swapped sumti land in the swapped `{xN}`).
const GISMU_PLACE_TEMPLATES: &[(&str, &str)] = &[
    // ── Motion / action verbs ──
    ("klama", "{x1} goes to {x2} from {x3} via {x4} using {x5}"),
    ("bevri", "{x1} carries {x2} to {x3} from {x4} via {x5}"),
    ("cadzu", "{x1} walks on {x2} using {x3}"),
    ("bajra", "{x1} runs on {x2} to {x3} from {x4}"),
    ("citka", "{x1} eats {x2}"),
    ("pinxe", "{x1} drinks {x2}"),
    ("catra", "{x1} kills {x2}"),
    ("gasnu", "{x1} does {x2}"),
    ("zukte", "{x1} acts toward goal {x2}"),
    ("zbasu", "{x1} makes {x2} from {x3}"),
    // ── Mental / communicative ──
    ("prami", "{x1} loves {x2}"),
    ("nelci", "{x1} likes {x2}"),
    ("djica", "{x1} desires {x2}"),
    ("djuno", "{x1} knows {x2}"),
    ("jimpe", "{x1} understands {x2}"),
    ("viska", "{x1} sees {x2}"),
    ("tirna", "{x1} hears {x2}"),
    ("tavla", "{x1} talks to {x2} about {x3}"),
    ("cusku", "{x1} expresses {x2} to {x3}"),
    ("ctuca", "{x1} teaches {x2} to {x3}"),
    ("tadni", "{x1} studies {x2}"),
    ("nitcu", "{x1} needs {x2}"),
    ("kakne", "{x1} is able to {x2}"),
    ("kurji", "{x1} takes care of {x2}"),
    ("ponse", "{x1} possesses {x2}"),
    ("penmi", "{x1} meets {x2}"),
    // ── Deontic / regulatory (incl. corpus proxy vocabulary) ──
    ("bilga", "{x1} is obligated to {x2}"),
    ("curmi", "{x1} permits {x2}"),
    ("fanta", "{x1} prevents {x2}"),
    ("kajde", "{x1} warns about {x2}"),
    ("flalu", "{x1} is a law about {x2}"),
    ("javni", "{x1} is a rule about {x2}"),
    ("nibli", "{x1} logically entails {x2}"),
    ("krinu", "{x1} is the reason for {x2}"),
    // ── Class predicates (x1 is a …) ──
    ("danlu", "{x1} is an animal"),
    ("gerku", "{x1} is a dog"),
    ("mlatu", "{x1} is a cat"),
    ("cipni", "{x1} is a bird"),
    ("finpe", "{x1} is a fish"),
    ("prenu", "{x1} is a person"),
    ("nanmu", "{x1} is a man"),
    ("ninmu", "{x1} is a woman"),
    ("verba", "{x1} is a child"),
    ("remna", "{x1} is a human"),
    ("xukmi", "{x1} is a chemical"),
    ("dinju", "{x1} is a building"),
    ("zdani", "{x1} is a home"),
    ("zarci", "{x1} is a market"),
    ("marce", "{x1} is a vehicle"),
    ("cidja", "{x1} is food"),
    ("litki", "{x1} is a liquid"),
    ("datni", "{x1} is data"),
    ("ciste", "{x1} is a system"),
    ("logji", "{x1} is logical"),
    // ── Property predicates (x1 is …) ──
    ("jmive", "{x1} is alive"),
    ("morsi", "{x1} is dead"),
    ("barda", "{x1} is big"),
    ("cmalu", "{x1} is small"),
    ("sutra", "{x1} is fast"),
    ("masno", "{x1} is slow"),
    ("xamgu", "{x1} is good"),
    ("xlali", "{x1} is bad"),
    ("kanro", "{x1} is healthy"),
    ("melbi", "{x1} is beautiful"),
    ("birti", "{x1} is certain"),
    ("xanri", "{x1} is imaginary"),
    // ── Numeric / compute (arithmetic relations) ──
    ("pilji", "{x1} is the product of {x2} and {x3}"),
    ("sumji", "{x1} is the sum of {x2} and {x3}"),
    ("dilcu", "{x1} is the quotient of {x2} and {x3}"),
    ("zmadu", "{x1} is greater than {x2}"),
    ("mleca", "{x1} is less than {x2}"),
    ("dunli", "{x1} equals {x2}"),
];

/// Hardcoded gloss overrides for common cmavo where jbovlaste glosses
/// are too technical for readable back-translation.
const CMAVO_GLOSS_OVERRIDES: &[(&str, &str)] = &[
    // Gadri (articles)
    ("lo", "the"),
    ("le", "the"),
    ("la", ""),
    // Structural terminators (suppress in output)
    ("cu", ""),
    ("ku", ""),
    ("ku'o", ""),
    ("kei", ""),
    ("ke'e", ""),
    ("vau", ""),
    ("li'u", ""),
    ("be'o", ""),
    ("fe'u", ""),
    // Negation
    ("na", "not"),
    ("nai", "not"),
    // Conversion
    ("se", "(swap-2)"),
    ("te", "(swap-3)"),
    ("ve", "(swap-4)"),
    ("xe", "(swap-5)"),
    // Tense
    ("pu", "[past]"),
    ("ca", "[present]"),
    ("ba", "[future]"),
    // Quantifiers
    ("ro", "all"),
    ("su'o", "some"),
    ("pa", "one"),
    ("re", "two"),
    ("ci", "three"),
    ("vo", "four"),
    ("mu", "five"),
    // Sentence separator
    (".i", "."),
    // Relative clauses
    ("poi", "which"),
    ("noi", ", which"),
    ("voi", "the-said"),
    ("ke'a", "(it)"),
    // Abstractions
    ("nu", "event-of"),
    ("du'u", "that"),
    ("ka", "property-of"),
    ("ni", "amount-of"),
    ("si'o", "concept-of"),
    // Pro-sumti
    ("mi", "I"),
    ("do", "you"),
    ("ti", "this"),
    ("ta", "that"),
    ("tu", "yonder"),
    ("zo'e", "(something)"),
    ("ri", "(it)"),
    // Logic variables
    ("da", "X"),
    ("de", "Y"),
    ("di", "Z"),
    // Questions
    ("ma", "what?"),
    ("mo", "is-what?"),
    ("xu", "is-it-true?"),
    // Place tags
    ("fa", "(x1=)"),
    ("fe", "(x2=)"),
    ("fi", "(x3=)"),
    ("fo", "(x4=)"),
    ("fu", "(x5=)"),
    // Forethought connectives
    ("ge", "both"),
    ("gi", "and"),
    ("ga", "either"),
    ("ganai", "if"),
    // Afterthought connectives
    ("je", "and"),
    ("ja", "or"),
    ("jo", "iff"),
    ("ju", "whether-or-not"),
    // Attitudinals
    ("ei", "[should]"),
    ("e'e", "[may]"),
    // Modal tags
    ("ri'a", "because"),
    ("ni'i", "logically-because"),
    ("mu'i", "motivated-by"),
    ("ki'u", "justified-by"),
    ("pi'o", "using"),
    ("ba'i", "instead-of"),
    // Misc
    ("be", "with"),
    ("bei", "and-with"),
    ("pe", "associated-with"),
    ("lu", "\""),
    ("li", "#"),
    ("ce'u", "(lambda)"),
    ("go'i", "(previous)"),
];
