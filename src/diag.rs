//! Source locations and diagnostics.

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Span {
    pub line: u32,
    pub col: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diag {
    pub span: Span,
    pub message: String,
}

impl Diag {
    pub fn new(span: Span, message: impl Into<String>) -> Self {
        Diag { span, message: message.into() }
    }

    /// Render as `file:line:col: error: msg` followed by the source line and a caret.
    pub fn render(&self, src: &str, file: &str) -> String {
        let mut out = format!("{}:{}:{}: error: {}\n", file, self.span.line, self.span.col, self.message);
        if let Some(l) = src.lines().nth((self.span.line as usize).saturating_sub(1)) {
            out.push_str(&format!("  | {}\n  | {}^\n", l, " ".repeat((self.span.col as usize).saturating_sub(1))));
        }
        out
    }
}
