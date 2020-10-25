use std::fmt;
use std::sync::Arc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyntaxKind {
    Whitespace,
    Eof,
    Error,
    IntLit,
    Ident,
    Symbol,
    Primitive,
    Operator(Operator),
    Application,
    ExprRoot,
}

impl fmt::Display for SyntaxKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use SyntaxKind::*;

        match self {
            Whitespace => write!(f, "WS"),
            Eof => write!(f, "EOF"),
            Error => write!(f, "ERROR"),
            IntLit => write!(f, "INTEGER"),
            Ident => write!(f, "IDENT"),
            Symbol => write!(f, "SYM"),
            Primitive => write!(f, "PRIM"),
            Operator(_op) => write!(f, "OP"),
            Application => write!(f, "APP"),
            ExprRoot => write!(f, "EXPR"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token<'a> {
    kind: SyntaxKind,
    value: &'a str,
}

impl<'a> fmt::Display for Token<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.kind {
            SyntaxKind::Error => write!(f, "ERROR"),
            SyntaxKind::Eof => write!(f, "EOF"),
            _ => write!(f, "{}", self.value),
        }
    }
}

impl<'a> Token<'a> {
    fn error() -> Self {
        Token {
            kind: SyntaxKind::Error,
            value: "",
        }
    }

    fn text_width(&self) -> usize {
        self.value.len()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NodeOrToken<'a> {
    Token(Arc<Token<'a>>),
    Node(Arc<GreenNode<'a>>),
}

impl<'a> NodeOrToken<'a> {
    fn text_width(&self) -> usize {
        match self {
            NodeOrToken::Token(token) => token.value.len(),
            NodeOrToken::Node(node) => node.text_width,
        }
    }

    fn kind(&self) -> SyntaxKind {
        match self {
            NodeOrToken::Token(token) => token.kind.clone(),
            NodeOrToken::Node(node) => node.kind.clone(),
        }
    }

    fn children(&self) -> impl Iterator<Item = &NodeOrToken<'a>> {
        let children = match self {
            NodeOrToken::Token(_) => &[],
            NodeOrToken::Node(node) => node.children.as_slice(),
        };
        children.iter()
    }
}

impl fmt::Display for NodeOrToken<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            NodeOrToken::Token(token) => write!(f, "{}", token),
            NodeOrToken::Node(node) => write!(f, "{}", node),
        }
    }
}

impl<'a> From<Token<'a>> for NodeOrToken<'a> {
    fn from(token: Token<'a>) -> Self {
        NodeOrToken::Token(Arc::new(token))
    }
}

impl<'a> From<GreenNode<'a>> for NodeOrToken<'a> {
    fn from(node: GreenNode<'a>) -> Self {
        NodeOrToken::Node(Arc::new(node))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GreenNode<'a> {
    kind: SyntaxKind,
    text_width: usize,
    children: Vec<NodeOrToken<'a>>,
}

impl<'a> GreenNode<'a> {
    pub fn new(kind: SyntaxKind, children: Vec<NodeOrToken<'a>>) -> Self {
        let text_width = children.iter().map(NodeOrToken::text_width).sum();
        Self {
            kind,
            text_width,
            children,
        }
    }

    pub fn non_trivial(&self) -> impl Iterator<Item = &NodeOrToken<'a>> + '_ {
        self.children
            .iter()
            .filter(|child| child.kind() != SyntaxKind::Whitespace)
    }
}

impl fmt::Display for GreenNode<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}", self.kind)?;
        for child in self.non_trivial() {
            write!(f, " {}", child)?;
        }
        write!(f, ")")
    }
}

pub type RedNode<'a> = Arc<RedNodeData<'a>>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RedNodeData<'a> {
    offset: usize,
    parent: Option<RedNode<'a>>,
    green: NodeOrToken<'a>,
}

impl<'a> RedNodeData<'a> {
    pub fn root(root: NodeOrToken<'a>) -> RedNode<'a> {
        Arc::new(RedNodeData {
            offset: 0,
            parent: None,
            green: root,
        })
    }

    pub fn parent(&self) -> Option<RedNode<'a>> {
        self.parent.clone()
    }

    // elision seems not working
    pub fn children<'s>(self: &'s RedNode<'a>) -> impl Iterator<Item = RedNode<'a>> + 's {
        let mut offset = self.offset;
        self.green.children().map(move |child| {
            let child_offset = offset;
            offset += child.text_width();
            Arc::new(RedNodeData {
                offset: child_offset,
                parent: Some(self.clone()),
                green: child.clone(),
            })
        })
    }

    pub fn pretty_print<'s>(self: &'s RedNode<'a>) -> impl fmt::Display + 's {
        ShowRedNode::<'s, 'a>(self, 0)
    }
}

#[derive(Debug)]
struct ShowRedNode<'s, 'a>(&'s RedNode<'a>, usize);

impl<'s, 'a> fmt::Display for ShowRedNode<'s, 'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let node = &self.0;
        let level = self.1;
        for _ in 0..level {
            write!(f, "  ")?;
        }
        writeln!(
            f,
            "{}@{}..{}",
            node.green.kind(),
            node.offset,
            node.offset + node.green.text_width()
        )?;
        for child in node.children() {
            ShowRedNode(&child, level + 1).fmt(f)?;
        }

        Ok(())
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Fixity {
    InfixL { bp: u16 },
    InfixR { bp: u16 },
    Prefix { right_bp: u16 },
    Postfix { left_bp: u16 },
    Closed,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum PlaceholderKind {
    Ident,
    Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Placeholder {
    pub kind: PlaceholderKind,
    pub name: String,
}

// c.f. "Parsing Mixfix Operators"
// parts.len() == placeholders.len() + 1
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Operator {
    fix: Fixity,
    parts: Vec<String>,
    placeholders: Vec<Placeholder>,
}

#[derive(Debug, Clone, Default)]
pub struct Language {
    pub operators: Vec<Operator>,
}

#[derive(Debug, Clone)]
pub struct ParseError {
    position: usize,
    message: String,
}

#[derive(Debug, Clone)]
pub struct Parser<'a> {
    input: &'a str,
    language: Language,
    position: usize,
    errors: Vec<ParseError>,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str, language: Language) -> Self {
        Self {
            input,
            language,
            position: 0,
            errors: vec![],
        }
    }

    pub fn remaining(&self) -> &'a str {
        &self.input[self.position..]
    }

    fn advance(&mut self, len: usize) {
        assert!(self.remaining().len() >= len, "input is too short");
        tracing::debug!("advance: {}", &self.remaining()[0..len]);
        self.position += len;
    }

    fn push_error(&mut self, message: String) {
        tracing::debug!("pushing error: {}", message);
        self.errors.push(ParseError {
            position: self.position,
            message,
        });
    }

    fn peek_token_at(&self, position: usize) -> Token<'a> {
        assert!(
            self.remaining().is_char_boundary(position),
            "invalid position: {}, remaining = {}",
            position,
            self.remaining()
        );

        let input = &self.remaining()[position..];
        tracing::trace!(position, input, "peek_token_at");

        if input.is_empty() {
            return Token {
                kind: SyntaxKind::Eof,
                value: "",
            };
        }

        match input.chars().next().unwrap() {
            '0'..='9' => {
                let value = input.split(|c| c < '0' || c > '9').next().unwrap();

                Token {
                    kind: SyntaxKind::IntLit,
                    value,
                }
            }
            c if c.is_whitespace() => {
                let value = input.split(|c: char| !c.is_whitespace()).next().unwrap();

                Token {
                    kind: SyntaxKind::Whitespace,
                    value,
                }
            }
            c if c.is_alphabetic() => {
                let value = input
                    .split(|c: char| !(c == '_' || c.is_alphanumeric()))
                    .next()
                    .unwrap();

                Token {
                    kind: SyntaxKind::Ident,
                    value,
                }
            }
            c => Token {
                kind: SyntaxKind::Symbol,
                value: &input[0..c.len_utf8()],
            },
        }
    }

    fn peek_token(&self) -> Token<'a> {
        self.peek_token_at(0)
    }

    fn expect_token(&mut self, token: Token<'a>, children: &mut Vec<NodeOrToken<'a>>) {
        let peeked = self.peek_token();
        if peeked == token {
            self.next_token(children);
        } else {
            self.push_error(format!("expected {:?}, got {:?}", token, peeked));
            children.push(Token::error().into());
        }
    }

    fn next_token(&mut self, children: &mut Vec<NodeOrToken<'a>>) {
        let token = self.peek_token();
        self.advance(token.value.len());
        children.push(token.into());
    }

    fn next_ident(&mut self, children: &mut Vec<NodeOrToken<'a>>) {
        let token = self.peek_token();
        match token.kind {
            SyntaxKind::Ident => {
                self.advance(token.value.len());
                children.push(token.into());
            }
            _ => {
                self.push_error(format!("expected identifier, got {:?}", token));
                children.push(Token::error().into());
            }
        }
    }

    fn skip_ws(&mut self, children: &mut Vec<NodeOrToken<'a>>) {
        let token = self.peek_token();
        if token.kind == SyntaxKind::Whitespace {
            self.expect_token(token, children);
        }
    }

    fn expect(&mut self, target: &str, children: &mut Vec<NodeOrToken<'a>>) {
        if self.remaining().starts_with(target) {
            let token = Token {
                kind: SyntaxKind::Symbol,
                value: &self.remaining()[0..target.len()],
            };
            children.push(token.into());
            self.advance(target.len());
        } else {
            self.push_error(format!("expected {}, got {}", target, self.remaining()));
            children.push(Token::error().into());
        }
    }

    fn primary_expr(&mut self) -> GreenNode<'a> {
        match self.peek_token() {
            token if token.kind == SyntaxKind::IntLit || token.kind == SyntaxKind::Ident => {
                let mut children = vec![];
                self.expect_token(token, &mut children);
                GreenNode::new(SyntaxKind::Primitive, children)
            }
            token => {
                self.push_error(format!("expected primary expr, got {:?}", token));
                GreenNode::new(SyntaxKind::Error, vec![])
            }
        }
    }

    fn parse_operator(&mut self, op: &Operator, children: &mut Vec<NodeOrToken<'a>>) {
        for i in 0..op.parts.len() {
            self.expect(&op.parts[i], children);
            self.skip_ws(children);

            if i < op.placeholders.len() {
                match &op.placeholders[i].kind {
                    PlaceholderKind::Expr => {
                        let node = self.expr_bp(0);
                        children.push(node.into());
                        self.skip_ws(children);
                    }
                    PlaceholderKind::Ident => {
                        self.next_ident(children);
                        self.skip_ws(children);
                    }
                }
            }
        }
    }

    fn expr_bp(&mut self, min_bp: u16) -> GreenNode<'a> {
        let span = tracing::span!(
            tracing::Level::DEBUG,
            "expr call",
            min_bp,
            remaining = self.remaining()
        );
        let _enter = span.enter();

        // prefix
        let mut lhs = if let Some(op) = self.peek_operator(0, |op| match op.fix {
            Fixity::Prefix { .. } | Fixity::Closed => true,
            _ => false,
        }) {
            let mut children = vec![];

            self.parse_operator(&op, &mut children);

            match op.fix {
                Fixity::Prefix { right_bp } => {
                    let node = self.expr_bp(right_bp);
                    children.push(node.into());
                }
                Fixity::Closed => {}
                _ => unreachable!(),
            }

            GreenNode::new(SyntaxKind::Operator(op), children)
        } else {
            self.primary_expr()
        };

        loop {
            let span = tracing::span!(
                tracing::Level::DEBUG,
                "expr loop",
                min_bp,
                remaining = self.remaining()
            );
            let _enter = span.enter();
            tracing::debug!(%lhs);

            let token = match self.peek_token() {
                token if token.kind == SyntaxKind::Eof => break,
                token
                    if token.kind == SyntaxKind::Whitespace
                        && token.text_width() == self.remaining().len() =>
                {
                    break;
                }
                token => token,
            };
            // peek next token after whitespaces
            let skip_width = if token.kind == SyntaxKind::Whitespace {
                token.text_width()
            } else {
                0
            };

            if let Some(op) = self.peek_operator(skip_width, |op| match op.fix {
                Fixity::InfixL { .. } | Fixity::InfixR { .. } | Fixity::Postfix { .. } => true,
                _ => false,
            }) {
                tracing::debug!(?op, "hit op");
                match op.fix {
                    Fixity::InfixL { bp } => {
                        if bp <= min_bp {
                            break;
                        }
                    }
                    Fixity::InfixR { bp } => {
                        if bp < min_bp {
                            break;
                        }
                    }
                    Fixity::Postfix { left_bp } => {
                        if left_bp < min_bp {
                            break;
                        }
                    }
                    _ => unreachable!(),
                }

                let mut children = vec![];
                children.push(lhs.into());
                self.skip_ws(&mut children);

                self.parse_operator(&op, &mut children);

                match op.fix {
                    Fixity::Postfix { .. } => {
                        lhs = GreenNode::new(SyntaxKind::Operator(op.clone()), children);
                        continue;
                    }
                    Fixity::InfixL { bp } | Fixity::InfixR { bp } => {
                        self.skip_ws(&mut children);
                        let rhs = self.expr_bp(bp);
                        children.push(rhs.into());
                        lhs = GreenNode::new(SyntaxKind::Operator(op.clone()), children);
                        continue;
                    }
                    _ => unreachable!(),
                }
            }

            // function application
            if lhs.kind != SyntaxKind::Error {
                // application is left associative
                const APP_BP: u16 = 10000;

                if APP_BP <= min_bp {
                    break;
                }

                tracing::debug!("trying function application");
                let backtrack = self.clone();
                let mut children = vec![];
                self.skip_ws(&mut children);
                let rhs = self.expr_bp(APP_BP);
                let consumed = rhs.text_width != 0;
                children.push(rhs.into());
                if consumed {
                    children.insert(0, lhs.into());
                    lhs = GreenNode::new(SyntaxKind::Application, children);
                    continue;
                } else {
                    *self = backtrack;
                }
            }

            break;
        }

        lhs
    }

    pub fn expr(&mut self) -> GreenNode<'a> {
        self.expr_bp(0)
    }

    // The following functions traverse input token by token to support operators
    // with alphabets and numerals in them.
    // For example, "⊢t xyz" is tokenized as ['⊢', 't', ' ', 'xyz'], while "⊢txyz" is ['⊢', 'txyz'].
    fn peek(&self, mut symbols: &str, mut position: usize) -> bool {
        loop {
            if symbols.is_empty() {
                return true;
            }

            match self.peek_token_at(position) {
                token if token.kind == SyntaxKind::Eof || token.kind == SyntaxKind::Error => {
                    return false
                }
                token if symbols.starts_with(token.value) => {
                    symbols = &symbols[token.value.len()..];
                    position += token.value.len();
                }
                _ => return false,
            }
        }
    }

    fn peek_operator<P>(&self, position: usize, mut pred: P) -> Option<Operator>
    where
        P: FnMut(&Operator) -> bool,
    {
        for op in self.language.operators.iter() {
            if pred(op) && self.peek(&op.parts[0], position) {
                return Some(op.clone());
            }
        }
        None
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn common_language() -> Language {
        Language {
            operators: vec![
                Operator {
                    fix: Fixity::InfixL { bp: 20 },
                    parts: vec!["=".into()],
                    placeholders: vec![],
                },
                Operator {
                    fix: Fixity::InfixL { bp: 50 },
                    parts: vec!["+".into()],
                    placeholders: vec![],
                },
                Operator {
                    fix: Fixity::InfixL { bp: 50 },
                    parts: vec!["-".into()],
                    placeholders: vec![],
                },
                Operator {
                    fix: Fixity::InfixR { bp: 80 },
                    parts: vec!["^".into()],
                    placeholders: vec![],
                },
                Operator {
                    fix: Fixity::Prefix { right_bp: 60 },
                    parts: vec!["-".into()],
                    placeholders: vec![],
                },
                Operator {
                    fix: Fixity::Postfix { left_bp: 70 },
                    parts: vec!["!".into()],
                    placeholders: vec![],
                },
                Operator {
                    fix: Fixity::Closed,
                    parts: vec!["(".into(), ")".into()],
                    placeholders: vec![Placeholder {
                        kind: PlaceholderKind::Expr,
                        name: "expr".into(),
                    }],
                },
                Operator {
                    fix: Fixity::Prefix { right_bp: 10 },
                    parts: vec!["∀".into(), ".".into()],
                    placeholders: vec![Placeholder {
                        kind: PlaceholderKind::Ident,
                        name: "var".into(),
                    }],
                },
                Operator {
                    fix: Fixity::Prefix { right_bp: 0 },
                    parts: vec!["fun".into(), "->".into()],
                    placeholders: vec![Placeholder {
                        kind: PlaceholderKind::Ident,
                        name: "var".into(),
                    }],
                },
                Operator {
                    fix: Fixity::Closed,
                    parts: vec!["{".into(), ".".into(), "}".into()],
                    placeholders: vec![
                        Placeholder {
                            kind: PlaceholderKind::Ident,
                            name: "var".into(),
                        },
                        Placeholder {
                            kind: PlaceholderKind::Expr,
                            name: "pred".into(),
                        },
                    ],
                },
                Operator {
                    fix: Fixity::Prefix { right_bp: 0 },
                    parts: vec!["let".into(), "=".into(), ";".into()],
                    placeholders: vec![
                        Placeholder {
                            kind: PlaceholderKind::Ident,
                            name: "var".into(),
                        },
                        Placeholder {
                            kind: PlaceholderKind::Expr,
                            name: "pred".into(),
                        },
                    ],
                },
            ],
        }
    }

    fn success_complete(language: Language, input: &str, expected: &str) {
        let _ = tracing_subscriber::fmt::try_init();

        let mut parser = Parser::new(input, language);
        let e = parser.expr();
        let text_width = e.text_width;
        let red = RedNodeData::root(e.clone().into());
        tracing::debug!(%e);
        tracing::debug!(pretty = %red.pretty_print());
        assert_eq!(
            e.to_string(),
            expected,
            "parse result doesn't match: \n{}",
            red.pretty_print()
        );
        assert!(parser.errors.is_empty());
        assert!(
            parser.remaining().is_empty(),
            "input must be consumed, remaining: {}",
            parser.remaining()
        );
        assert_eq!(text_width, input.len());
    }

    fn error_complete(language: Language, input: &str, expected: &str) {
        let _ = tracing_subscriber::fmt::try_init();

        let mut parser = Parser::new(input, language);
        let e = parser.expr();
        let text_width = e.text_width;
        let red = RedNodeData::root(e.clone().into());
        tracing::debug!(%e);
        tracing::debug!(pretty = %red.pretty_print());
        assert_eq!(
            e.to_string(),
            expected,
            "parse result doesn't match: \n{}",
            red.pretty_print()
        );
        assert!(!parser.errors.is_empty());
        assert!(
            parser.remaining().is_empty(),
            "input must be consumed, remaining: {}",
            parser.remaining()
        );
        assert_eq!(text_width, input.len());
    }

    #[test]
    fn test_intlit() {
        success_complete(common_language(), "12345", "(PRIM 12345)");
    }

    #[test]
    fn test_binop() {
        success_complete(common_language(), "123 + 45", "(OP (PRIM 123) + (PRIM 45))");
    }

    #[test]
    fn test_prec_left() {
        success_complete(
            common_language(),
            "123 ^ 45 + 67",
            "(OP (OP (PRIM 123) ^ (PRIM 45)) + (PRIM 67))",
        );
    }

    #[test]
    fn test_prec_right() {
        success_complete(
            common_language(),
            "123 + 45 ^ 67",
            "(OP (PRIM 123) + (OP (PRIM 45) ^ (PRIM 67)))",
        );
    }

    #[test]
    fn test_left_assoc() {
        success_complete(
            common_language(),
            "123 + 45 + 67",
            "(OP (OP (PRIM 123) + (PRIM 45)) + (PRIM 67))",
        );
    }

    #[test]
    fn test_right_assoc() {
        success_complete(
            common_language(),
            "2^3^4",
            "(OP (PRIM 2) ^ (OP (PRIM 3) ^ (PRIM 4)))",
        );
    }

    #[test]
    fn test_prefix() {
        success_complete(
            common_language(),
            "-2 + 5 + -4 ^ 2",
            "(OP (OP (OP - (PRIM 2)) + (PRIM 5)) + (OP - (OP (PRIM 4) ^ (PRIM 2))))",
        );
    }

    #[test]
    fn test_postfix() {
        success_complete(
            common_language(),
            "1 - -2! + 3",
            "(OP (OP (PRIM 1) - (OP - (OP (PRIM 2) !))) + (PRIM 3))",
        );
    }

    #[test]
    fn test_paren() {
        success_complete(
            common_language(),
            "-(2 + 5 + -4)^2",
            "(OP - (OP (OP ( (OP (OP (PRIM 2) + (PRIM 5)) + (OP - (PRIM 4))) )) ^ (PRIM 2)))",
        );
    }

    #[test]
    fn test_ident() {
        success_complete(
            common_language(),
            "a^3 + b^3 - c^3",
            "(OP (OP (OP (PRIM a) ^ (PRIM 3)) + (OP (PRIM b) ^ (PRIM 3))) - (OP (PRIM c) ^ (PRIM 3)))",
        )
    }

    #[test]
    fn test_ident_underscore() {
        success_complete(
            common_language(),
            "a_1 + b__",
            "(OP (PRIM a_1) + (PRIM b__))",
        )
    }

    #[test]
    fn test_equal_op() {
        success_complete(
            common_language(),
            "a^3 + b^3 = c^3",
            "(OP (OP (OP (PRIM a) ^ (PRIM 3)) + (OP (PRIM b) ^ (PRIM 3))) = (OP (PRIM c) ^ (PRIM 3)))",
        )
    }

    #[test]
    fn test_confusing_op() {
        let language = Language {
            operators: vec![Operator {
                fix: Fixity::InfixL { bp: 100 },
                parts: vec!["⊢t".into(), "->".into()],
                placeholders: vec![Placeholder {
                    kind: PlaceholderKind::Expr,
                    name: "pre".into(),
                }],
            }],
        };
        success_complete(
            language,
            "Γ ⊢t pre -> post",
            "(OP (PRIM Γ) ⊢t (PRIM pre) -> (PRIM post))",
        )
    }

    #[test]
    fn test_parens() {
        let language = Language {
            operators: vec![
                Operator {
                    fix: Fixity::InfixL { bp: 20 },
                    parts: vec!["=".into()],
                    placeholders: vec![],
                },
                Operator {
                    fix: Fixity::Closed,
                    parts: vec!["[|".into(), "|]".into()],
                    placeholders: vec![Placeholder {
                        kind: PlaceholderKind::Expr,
                        name: "term".into(),
                    }],
                },
            ],
        };
        success_complete(
            language,
            "[| t |] = 100",
            "(OP (OP [| (PRIM t) |]) = (PRIM 100))",
        )
    }

    #[test]
    fn test_quantifier() {
        success_complete(
            common_language(),
            "∀y. (fun x -> y) = fun z -> y",
            "(OP ∀ y . (OP (OP ( (OP fun x -> (PRIM y)) )) = (OP fun z -> (PRIM y))))",
        )
    }

    #[test]
    fn test_missing_ident() {
        error_complete(
            common_language(),
            "∀. x = x",
            "(OP ∀ ERROR . (OP (PRIM x) = (PRIM x)))",
        )
    }

    #[test]
    fn test_missing() {
        error_complete(
            common_language(),
            "∀. (3 + = ^2)",
            "(OP ∀ ERROR . (OP ( (OP (OP (PRIM 3) + (ERROR)) = (OP (ERROR) ^ (PRIM 2))) )))",
        )
    }

    #[test]
    fn test_simple() {
        success_complete(common_language(), "(x)", "(OP ( (PRIM x) ))")
    }

    #[test]
    fn test_fn_app() {
        success_complete(
            common_language(),
            "f x y",
            "(APP (APP (PRIM f) (PRIM x)) (PRIM y))",
        )
    }

    #[test]
    fn test_app_precedence() {
        success_complete(
            common_language(),
            "f x + g (y - z)",
            "(OP (APP (PRIM f) (PRIM x)) + (APP (PRIM g) (OP ( (OP (PRIM y) - (PRIM z)) ))))",
        )
    }

    #[test]
    fn test_unbalanced_paren() {
        error_complete(
            common_language(),
            "((((4",
            "(OP ( (OP ( (OP ( (OP ( (PRIM 4) ERROR) ERROR) ERROR) ERROR)",
        )
    }

    #[test]
    fn test_empty_error() {
        error_complete(common_language(), "", "(ERROR)")
    }

    #[test]
    fn test_comprehension() {
        success_complete(
            common_language(),
            "{f. ∀x. f (f x) = f}",
            "(OP { f . (OP ∀ x . (OP (APP (PRIM f) (OP ( (APP (PRIM f) (PRIM x)) ))) = (PRIM f))) })",
        )
    }

    #[test]
    fn test_let() {
        // TODO: let-in syntax
        success_complete(
            common_language(),
            "let f = fun x -> x; f 100 - 200",
            "(OP let f = (OP fun x -> (PRIM x)) ; (OP (APP (PRIM f) (PRIM 100)) - (PRIM 200)))",
        )
    }
}
