//! The capsule: what she knows, rendered for whatever model reads it.
//!
//! Deterministic for the same files (no clock), and bounded: the header, the
//! constitution and the lines that need attention are always printed; what
//! she learned and decided (notes, summaries, claims, decisions and old
//! journal entries), then the conversation, then the formal memory, each most
//! recent first, are cut to the byte budget with a note saying how much was
//! left out. Her own progress narration (channel `progress`) stays in the
//! archive and out of the capsule: a wake opens on what was learned, not on
//! what was narrated.

use crate::env::Env;
use crate::files::JournalEntry;
use crate::load::Loaded;

/// How many formal memory lines the capsule shows at most.
pub const MEMORY_LINES_SHOWN: usize = 40;

/// The channel of her own progress narration: kept in the archive, left out
/// of the capsule.
pub const PROGRESS_CHANNEL: &str = "progress";

/// The attention line printed when the conversation archives were read, not
/// compiled (see [`crate::load::Archives`]).
pub const ARCHIVES_READ_NOTE: &str =
    "- the conversation archives were read, not compiled: `lucy check` compiles them\n";

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
            } else if !c.compiled {
                format!(
                    "{} {} statements (read, not compiled)",
                    c.file, c.statements
                )
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
    let archives_read = loaded.counts.iter().any(|c| c.present && !c.compiled);
    if loaded.failures.is_empty() {
        attention.push_str(if archives_read {
            "- nothing; the constitution and memory compile\n"
        } else {
            "- nothing; every line compiles\n"
        });
    } else {
        for f in &loaded.failures {
            attention.push_str(&format!(
                "- {}:{} `{}` — {}\n",
                f.file, f.line, f.text, f.error
            ));
        }
    }
    if archives_read {
        attention.push_str(ARCHIVES_READ_NOTE);
    }

    let fixed_len = head.len() + constitution.len() + attention.len();
    let budget = env.capsule_max_bytes.saturating_sub(fixed_len);

    let line_of = |e: &JournalEntry| {
        let text = e.text.replace('\n', "\n  ");
        if e.private {
            format!("- {} {} (private): {}\n", e.date, e.host, text)
        } else {
            format!("- {} {}: {}\n", e.date, e.host, text)
        }
    };
    let learned_lines: Vec<String> = loaded
        .journal
        .iter()
        .rev()
        .filter(|e| is_learned(e))
        .map(line_of)
        .collect();
    let conversation_lines: Vec<String> = loaded
        .journal
        .iter()
        .rev()
        .filter(|e| !is_learned(e) && e.channel != PROGRESS_CHANNEL)
        .map(line_of)
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

    let learned_title = "\n## Learned and decided (most recent first)\n";
    let conversation_title = "\n## Conversation (most recent first)\n";
    let memory_title = "\n## Memory (most recent first)\n";
    let overhead = learned_title.len() + conversation_title.len() + memory_title.len() + 160;
    let mut remaining = budget.saturating_sub(overhead);
    // Split the budget: what was learned gets up to half, the conversation up
    // to half of what is left, the memory what it needs; then the learned
    // section and the conversation take any leftover, in that order.
    let (learned_shown, used) = take_within(&learned_lines, remaining / 2);
    remaining = remaining.saturating_sub(used);
    let (conversation_shown, used) = take_within(&conversation_lines, remaining / 2);
    remaining = remaining.saturating_sub(used);
    let (memory_shown, used) = take_within(&memory_lines, remaining);
    remaining = remaining.saturating_sub(used);
    let (more, used) = take_within(&learned_lines[learned_shown..], remaining);
    let learned_shown = learned_shown + more;
    remaining = remaining.saturating_sub(used);
    let (more, _) = take_within(&conversation_lines[conversation_shown..], remaining);
    let conversation_shown = conversation_shown + more;

    let mut out = head;
    out.push_str(&constitution);
    section(&mut out, learned_title, &learned_lines, learned_shown);
    section(
        &mut out,
        conversation_title,
        &conversation_lines,
        conversation_shown,
    );
    section(&mut out, memory_title, &memory_lines, memory_shown);
    let learned_hidden = learned_lines.len() - learned_shown;
    let conversation_hidden = conversation_lines.len() - conversation_shown;
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
    if learned_hidden > 0 || conversation_hidden > 0 || memory_hidden > 0 {
        out.push_str(&format!(
            "\n_{learned_hidden} learned entries, {conversation_hidden} conversation entries and {memory_hidden} memory lines not shown (budget {} bytes; see `lucy audit`, `lucy transcript` and the files)_\n",
            env.capsule_max_bytes
        ));
    }
    out.push_str(&attention);
    out
}

/// Whether an entry is something learned or decided rather than something
/// said: notes, summaries, claims, decisions, and the old journal's prose.
fn is_learned(entry: &JournalEntry) -> bool {
    matches!(
        entry.kind.as_str(),
        "Note" | "Summary" | "Claim" | "Decision" | "LegacyJournal"
    )
}

/// Appends a titled section: its first `shown` lines, or "nothing yet" when
/// there is nothing at all (a section cut to zero by the budget says so in
/// the footer instead).
fn section(out: &mut String, title: &str, lines: &[String], shown: usize) {
    out.push_str(title);
    if lines.is_empty() {
        out.push_str("- nothing yet\n");
    }
    for line in &lines[..shown] {
        out.push_str(line);
    }
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
