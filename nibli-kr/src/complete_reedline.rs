//! Reedline [`Completer`] adapter over [`crate::complete`] — shared by
//! nibli-host and the native `nibli` REPL (feature `reedline`).

use crate::complete::{CompleteOpts, complete};
use reedline::{
    ColumnarMenu, Completer, Emacs, KeyCode, KeyModifiers, MenuBuilder, Reedline, ReedlineEvent,
    ReedlineMenu, Span, Suggestion, default_emacs_keybindings,
};

/// Tab-completion engine for the console: KR vocabulary + REPL commands.
pub struct KrCompleter {
    pub limit: usize,
}

impl Default for KrCompleter {
    fn default() -> Self {
        Self { limit: 40 }
    }
}

impl Completer for KrCompleter {
    fn complete(&mut self, line: &str, pos: usize) -> Vec<Suggestion> {
        let result = complete(
            line,
            pos,
            CompleteOpts {
                include_repl_commands: true,
                limit: self.limit,
                min_prefix: 1,
                extra: &[],
            },
        );
        // Allow place completion with empty / short prefix inside a call.
        let result = if result.items.is_empty() {
            complete(
                line,
                pos,
                CompleteOpts {
                    include_repl_commands: true,
                    limit: self.limit,
                    min_prefix: 0,
                    extra: &[],
                },
            )
        } else {
            result
        };

        let span = Span {
            start: result.span_start,
            end: result.span_end,
        };
        result
            .items
            .into_iter()
            .map(|c| {
                let description = c.description.or_else(|| Some(c.kind.label().into()));
                Suggestion {
                    value: c.value,
                    description,
                    style: None,
                    extra: None,
                    span,
                    append_whitespace: false,
                    match_indices: None,
                }
            })
            .collect()
    }
}

/// Wire the shared completer + Tab completion menu onto a [`Reedline`].
///
/// Call after any highlighter/hinter setup so both REPLs share one binding
/// policy (Tab opens the engine menu, then cycles).
pub fn with_completion(editor: Reedline) -> Reedline {
    let completer = Box::new(KrCompleter::default());
    let menu = Box::new(ColumnarMenu::default().with_name("completion_menu"));
    let mut keybindings = default_emacs_keybindings();
    keybindings.add_binding(
        KeyModifiers::NONE,
        KeyCode::Tab,
        ReedlineEvent::UntilFound(vec![
            ReedlineEvent::Menu("completion_menu".to_string()),
            ReedlineEvent::MenuNext,
        ]),
    );
    let edit_mode = Box::new(Emacs::new(keybindings));
    editor
        .with_completer(completer)
        .with_menu(ReedlineMenu::EngineCompleter(menu))
        .with_edit_mode(edit_mode)
}
