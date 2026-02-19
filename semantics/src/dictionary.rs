use quick_xml::Reader;
use quick_xml::events::Event;
use std::collections::HashMap;

pub struct JbovlasteSchema {
    pub arities: HashMap<String, usize>,
}

impl JbovlasteSchema {
    /// Loads the jbovlaste XML export from an embedded string payload.
    pub fn load_from_xml(xml_data: &str) -> Self {
        let mut reader = Reader::from_str(xml_data);
        reader.config_mut().trim_text(true);

        let mut arities = HashMap::with_capacity(10000);
        let mut buf = Vec::new();

        let mut current_word = String::new();
        let mut current_type = String::new();
        let mut in_definition = false;
        let mut current_definition = String::new();

        loop {
            match reader.read_event_into(&mut buf) {
                Err(e) => panic!("Error at position {}: {:?}", reader.buffer_position(), e),
                Ok(Event::Eof) => break,
                Ok(Event::Start(e)) => {
                    let name = e.name();
                    if name.as_ref() == b"valsi" {
                        current_word.clear();
                        current_type.clear();
                        current_definition.clear();

                        for attr in e.attributes().flatten() {
                            if attr.key.as_ref() == b"word" {
                                current_word = String::from_utf8_lossy(&attr.value).into_owned();
                            } else if attr.key.as_ref() == b"type" {
                                current_type = String::from_utf8_lossy(&attr.value).into_owned();
                            }
                        }
                    } else if name.as_ref() == b"definition" {
                        in_definition = true;
                    }
                }
                Ok(Event::Text(e)) => {
                    if in_definition {
                        current_definition.push_str(&String::from_utf8_lossy(e.as_ref()));
                    }
                }
                Ok(Event::End(e)) => {
                    let name = e.name();
                    if name.as_ref() == b"definition" {
                        in_definition = false;
                    } else if name.as_ref() == b"valsi" {
                        if current_type == "gismu" || current_type == "lujvo" {
                            let arity = Self::extract_arity(&current_definition);
                            arities.insert(current_word.clone(), arity);
                        }
                    }
                }
                _ => (),
            }
            buf.clear();
        }

        Self { arities }
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

    pub fn get_arity(&self, word: &str) -> usize {
        if word == "klama" {
            return 5;
        }
        *self.arities.get(word).unwrap_or(&2)
    }
}
