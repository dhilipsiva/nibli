//! The capsule: what she knows, rendered for whatever model reads it.
//!
//! Deterministic for the same files (no clock), and bounded: the header, the
//! constitution and the lines that need attention are always printed; the
//! journal (most recent first) and the formal memory (most recent first) are
//! cut to the byte budget with a note saying how much was left out.

use crate::env::Env;
use crate::load::Loaded;

/// How many formal memory lines the capsule shows at most.
pub const MEMORY_LINES_SHOWN: usize = 40;

/// Renders the capsule.
pub fn render(loaded: &Loaded, env: &Env) -> String {
    let mut head = String::new();
    head.push_str("# Lucy D\n");
    head.push_str(&format!("- host: {}\n", env.host));
    head.push_str(&format!("- home: {}\n", env.home.display()));
    let files: Vec<String> = loaded
        .counts
        .iter()
        .map(|c| {
            if !c.present {
                format!("{} absent", c.file)
            } else if c.failed > 0 {
                format!(
                    "{} {} statements ({} failing)",
                    c.file, c.asserted, c.failed
                )
            } else {
                format!("{} {} statements", c.file, c.asserted)
            }
        })
        .collect();
    let (public_entries, private_entries) =
        loaded.journal.iter().fold((0usize, 0usize), |(p, q), e| {
            if e.private { (p, q + 1) } else { (p + 1, q) }
        });
    head.push_str(&format!(
        "- files: {}; journal {} entries; private journal {} entries\n",
        files.join("; "),
        public_entries,
        private_entries
    ));
    head.push_str(&format!(
        "- standing: {}\n",
        if loaded.standing {
            "loaded (exist(Lucy, Memory, Loaded) asserted)"
        } else {
            "NOT asserted; see attention"
        }
    ));

    let mut constitution = String::from("\n## Constitution\n");
    for line in &loaded.preamble {
        if !line.is_empty() {
            constitution.push_str(&format!("{line}\n"));
        }
    }
    for line in &loaded.standing_lines {
        constitution.push_str(line);
        constitution.push('\n');
    }
    constitution.push_str("The rules, as written:\n");
    for line in &loaded.constitution_lines {
        constitution.push_str("    ");
        constitution.push_str(line);
        constitution.push('\n');
    }

    let mut attention = String::from("\n## Needs attention\n");
    if loaded.failures.is_empty() {
        attention.push_str("- nothing; every line compiles\n");
    } else {
        for f in &loaded.failures {
            attention.push_str(&format!(
                "- {}:{} `{}` — {}\n",
                f.file, f.line, f.text, f.error
            ));
        }
    }

    let fixed_len = head.len() + constitution.len() + attention.len();
    let budget = env.capsule_max_bytes.saturating_sub(fixed_len);

    let journal_lines: Vec<String> = loaded
        .journal
        .iter()
        .rev()
        .map(|e| {
            let text = e.text.replace('\n', "\n  ");
            if e.private {
                format!("- {} {} (private): {}\n", e.date, e.host, text)
            } else {
                format!("- {} {}: {}\n", e.date, e.host, text)
            }
        })
        .collect();
    let memory_lines: Vec<String> = loaded
        .memory
        .iter()
        .rev()
        .filter(|m| {
            m.ok && !matches!(
                m.file.as_str(),
                "interactions.nibli" | "private-interactions.nibli"
            )
        })
        .take(MEMORY_LINES_SHOWN)
        .map(|m| {
            if m.private {
                format!("- {}:{} (private) {}\n", m.file, m.line, m.text)
            } else {
                format!("- {}:{} {}\n", m.file, m.line, m.text)
            }
        })
        .collect();

    let journal_title = "\n## Journal (most recent first)\n";
    let memory_title = "\n## Memory (most recent first)\n";
    let overhead = journal_title.len() + memory_title.len() + 120;
    let mut remaining = budget.saturating_sub(overhead);
    // Split the budget: the journal gets what it needs up to two thirds, the
    // memory gets the rest, then the journal takes any leftover.
    let journal_cap = remaining * 2 / 3;
    let (journal_shown, journal_used) = take_within(&journal_lines, journal_cap);
    remaining = remaining.saturating_sub(journal_used);
    let (memory_shown, memory_used) = take_within(&memory_lines, remaining);
    remaining = remaining.saturating_sub(memory_used);
    let (journal_more, _) = take_within(&journal_lines[journal_shown..], remaining);
    let journal_shown = journal_shown + journal_more;

    let mut out = head;
    out.push_str(&constitution);
    out.push_str(journal_title);
    if journal_lines.is_empty() {
        out.push_str("- nothing yet\n");
    }
    for line in &journal_lines[..journal_shown] {
        out.push_str(line);
    }
    out.push_str(memory_title);
    if memory_lines.is_empty() {
        out.push_str("- nothing yet\n");
    }
    for line in &memory_lines[..memory_shown] {
        out.push_str(line);
    }
    let journal_hidden = journal_lines.len() - journal_shown;
    let memory_hidden = loaded
        .memory
        .iter()
        .filter(|m| {
            m.ok && !matches!(
                m.file.as_str(),
                "interactions.nibli" | "private-interactions.nibli"
            )
        })
        .count()
        - memory_shown;
    if journal_hidden > 0 || memory_hidden > 0 {
        out.push_str(&format!(
            "\n_{journal_hidden} journal entries and {memory_hidden} memory lines not shown (budget {} bytes; see `lucy audit` and the files)_\n",
            env.capsule_max_bytes
        ));
    }
    out.push_str(&attention);
    out
}

/// Takes leading lines while their total stays within `budget` bytes.
fn take_within(lines: &[String], budget: usize) -> (usize, usize) {
    let mut used = 0;
    let mut count = 0;
    for line in lines {
        if used + line.len() > budget {
            break;
        }
        used += line.len();
        count += 1;
    }
    (count, used)
}
