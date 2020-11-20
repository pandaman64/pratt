use std::fmt;
use std::sync::Arc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, num_derive::FromPrimitive)]
pub enum SyntaxKind {
    Whitespace,
    Eof,
    Error,
    IntLit,
    Ident,
    Symbol,
    Primitive,
    Operator,
    Application,
    ExprRoot,
}

impl SyntaxKind {
    fn trivial(&self) -> bool {
        use SyntaxKind::*;

        match self {
            Whitespace | Eof => true,
            _ => false,
        }
    }

    fn non_trivial(&self) -> bool {
        !self.trivial()
    }
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
            Operator => write!(f, "OP"),
            Application => write!(f, "APP"),
            ExprRoot => write!(f, "EXPR"),
        }
    }
}

impl From<SyntaxKind> for rowan::SyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
        rowan::SyntaxKind(kind as u16)
    }
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
struct PrattLanguage;

impl rowan::Language for PrattLanguage {
    type Kind = SyntaxKind;

    fn kind_from_raw(kind: rowan::SyntaxKind) -> Self::Kind {
        use num_traits::FromPrimitive;
        SyntaxKind::from_u16(kind.0).unwrap()
    }

    fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
        kind.into()
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
            NodeOrToken::Token(token) => token.kind,
            NodeOrToken::Node(node) => node.kind,
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

#[derive(Debug)]
pub struct PrintSyntaxNode<'a>(&'a rowan::SyntaxNode<PrattLanguage>);

impl fmt::Display for PrintSyntaxNode<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let node = self.0;
        write!(f, "({}", node.kind())?;
        for child in node.children_with_tokens() {
            match child {
                rowan::SyntaxElement::Node(node) => write!(f, " {}", PrintSyntaxNode(&node))?,
                rowan::SyntaxElement::Token(token) => {
                    if token.kind().non_trivial() {
                        write!(f, " {}", token)?
                    }
                }
            }
        }
        write!(f, ")")
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ExprStart {
    Prefix { right_bp: u16 },
    Closed,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ExprAfter {
    InfixL { bp: u16 },
    InfixR { bp: u16 },
    Postfix { left_bp: u16 },
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
pub struct Operator<F> {
    fix: F,
    parts: Vec<String>,
    placeholders: Vec<Placeholder>,
}

#[derive(Debug, Clone, Default)]
pub struct Language {
    pub expr_start: Vec<Operator<ExprStart>>,
    pub expr_after: Vec<Operator<ExprAfter>>,
}

#[derive(Debug, Clone)]
pub struct ParseError {
    position: usize,
    message: String,
}

#[derive(Debug)]
pub struct Parser<'a> {
    input: &'a str,
    language: Language,
    position: usize,
    errors: Vec<ParseError>,
    builder: rowan::GreenNodeBuilder<'static>,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str, language: Language) -> Self {
        Self {
            input,
            language,
            position: 0,
            errors: vec![],
            builder: rowan::GreenNodeBuilder::new(),
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
        self.builder.token(token.kind.into(), token.value.into());
        children.push(token.into());
    }

    fn next_ident(&mut self, children: &mut Vec<NodeOrToken<'a>>) {
        let token = self.peek_token();
        match token.kind {
            SyntaxKind::Ident => {
                self.advance(token.value.len());
                self.builder.token(token.kind.into(), token.value.into());
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
            self.builder
                .token(SyntaxKind::Symbol.into(), token.value.into());
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

    fn parse_operator<F>(&mut self, op: &Operator<F>, children: &mut Vec<NodeOrToken<'a>>) {
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

        let checkpoint = self.builder.checkpoint();
        let mut lhs = if let Some(op) = self.peek_op_expr_start(0, |_| true) {
            let mut children = vec![];

            self.builder.start_node(SyntaxKind::Operator.into());
            self.parse_operator(&op, &mut children);

            match op.fix {
                ExprStart::Prefix { right_bp } => {
                    let node = self.expr_bp(right_bp);
                    children.push(node.into());
                }
                ExprStart::Closed => {}
            }

            self.builder.finish_node();
            GreenNode::new(SyntaxKind::Operator, children)
        } else {
            self.builder.start_node(SyntaxKind::Primitive.into());
            let lhs = self.primary_expr();
            self.builder.finish_node();
            lhs
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

            if let Some(op) = self.peek_op_expr_after(skip_width, |_| true) {
                tracing::debug!(?op, "hit op");
                match op.fix {
                    ExprAfter::InfixL { bp } => {
                        if bp <= min_bp {
                            break;
                        }
                    }
                    ExprAfter::InfixR { bp } => {
                        if bp < min_bp {
                            break;
                        }
                    }
                    ExprAfter::Postfix { left_bp } => {
                        if left_bp < min_bp {
                            break;
                        }
                    }
                }

                self.builder
                    .start_node_at(checkpoint, SyntaxKind::Operator.into());
                let mut children = vec![];
                children.push(lhs.into());
                self.skip_ws(&mut children);

                self.parse_operator(&op, &mut children);

                match op.fix {
                    ExprAfter::Postfix { .. } => {
                        lhs = GreenNode::new(SyntaxKind::Operator, children);
                        self.builder.finish_node();
                        continue;
                    }
                    ExprAfter::InfixL { bp } | ExprAfter::InfixR { bp } => {
                        self.skip_ws(&mut children);
                        let rhs = self.expr_bp(bp);
                        children.push(rhs.into());
                        lhs = GreenNode::new(SyntaxKind::Operator, children);
                        self.builder.finish_node();
                        continue;
                    }
                }
            }

            // parse function application if the next non-trivial token can start another expr
            if lhs.kind != SyntaxKind::Error && self.starts_with_expr(skip_width) {
                // application is left associative
                const APP_BP: u16 = 10000;

                if APP_BP <= min_bp {
                    break;
                }

                tracing::debug!("function application");
                self.builder
                    .start_node_at(checkpoint, SyntaxKind::Application.into());
                let mut children = vec![];
                children.push(lhs.into());
                self.skip_ws(&mut children);
                let rhs = self.expr_bp(APP_BP);
                // parsing of the argument must consume at least one token
                assert_ne!(rhs.text_width, 0);
                children.push(rhs.into());
                lhs = GreenNode::new(SyntaxKind::Application, children);
                self.builder.finish_node();
                continue;
            }

            break;
        }

        lhs
    }

    pub fn expr(&mut self) -> GreenNode<'a> {
        self.builder.start_node(SyntaxKind::ExprRoot.into());
        let node = self.expr_bp(0);
        self.builder.finish_node();
        node
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

    fn peek_op_expr_start<P>(&self, position: usize, pred: P) -> Option<Operator<ExprStart>>
    where
        P: FnMut(&Operator<ExprStart>) -> bool,
    {
        self.peek_operator(&self.language.expr_start, position, pred)
    }

    fn peek_op_expr_after<P>(&self, position: usize, pred: P) -> Option<Operator<ExprAfter>>
    where
        P: FnMut(&Operator<ExprAfter>) -> bool,
    {
        self.peek_operator(&self.language.expr_after, position, pred)
    }

    fn peek_operator<F, P>(
        &self,
        operators: &[Operator<F>],
        position: usize,
        mut pred: P,
    ) -> Option<Operator<F>>
    where
        P: FnMut(&Operator<F>) -> bool,
        Operator<F>: Clone,
    {
        for op in operators.iter() {
            if pred(op) && self.peek(&op.parts[0], position) {
                return Some(op.clone());
            }
        }
        None
    }

    fn starts_with_expr(&self, position: usize) -> bool {
        if self.peek_op_expr_start(position, |_| true).is_some() {
            true
        } else {
            match self.peek_token_at(position).kind {
                SyntaxKind::Ident | SyntaxKind::IntLit => true,
                _ => false,
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn common_language() -> Language {
        Language {
            expr_start: vec![
                Operator {
                    fix: ExprStart::Prefix { right_bp: 60 },
                    parts: vec!["-".into()],
                    placeholders: vec![],
                },
                Operator {
                    fix: ExprStart::Closed,
                    parts: vec!["(".into(), ")".into()],
                    placeholders: vec![Placeholder {
                        kind: PlaceholderKind::Expr,
                        name: "expr".into(),
                    }],
                },
                Operator {
                    fix: ExprStart::Prefix { right_bp: 10 },
                    parts: vec!["∀".into(), ".".into()],
                    placeholders: vec![Placeholder {
                        kind: PlaceholderKind::Ident,
                        name: "var".into(),
                    }],
                },
                Operator {
                    fix: ExprStart::Prefix { right_bp: 0 },
                    parts: vec!["fun".into(), "->".into()],
                    placeholders: vec![Placeholder {
                        kind: PlaceholderKind::Ident,
                        name: "var".into(),
                    }],
                },
                Operator {
                    fix: ExprStart::Closed,
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
                    fix: ExprStart::Prefix { right_bp: 0 },
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
            expr_after: vec![
                Operator {
                    fix: ExprAfter::InfixL { bp: 20 },
                    parts: vec!["=".into()],
                    placeholders: vec![],
                },
                Operator {
                    fix: ExprAfter::InfixL { bp: 50 },
                    parts: vec!["+".into()],
                    placeholders: vec![],
                },
                Operator {
                    fix: ExprAfter::InfixL { bp: 50 },
                    parts: vec!["-".into()],
                    placeholders: vec![],
                },
                Operator {
                    fix: ExprAfter::InfixR { bp: 80 },
                    parts: vec!["^".into()],
                    placeholders: vec![],
                },
                Operator {
                    fix: ExprAfter::Postfix { left_bp: 70 },
                    parts: vec!["!".into()],
                    placeholders: vec![],
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
        tracing::info!(%e);
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

        let root: rowan::SyntaxNode<PrattLanguage> =
            rowan::SyntaxNode::new_root(parser.builder.finish());
        tracing::debug!("{:#?}", root);
        let printer = PrintSyntaxNode(&root);
        assert_eq!(
            printer.to_string(),
            format!("(EXPR {})", expected),
            "parse reslt doesn't match: \n{:#?}",
            root
        );
    }

    fn error_complete(language: Language, input: &str, expected: &str) {
        let _ = tracing_subscriber::fmt::try_init();

        let mut parser = Parser::new(input, language);
        let e = parser.expr();
        let text_width = e.text_width;
        let red = RedNodeData::root(e.clone().into());
        tracing::info!(%e);
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

        let root: rowan::SyntaxNode<PrattLanguage> =
            rowan::SyntaxNode::new_root(parser.builder.finish());
        tracing::debug!("{:#?}", root);
        let _printer = PrintSyntaxNode(&root);
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
            expr_start: vec![],
            expr_after: vec![Operator {
                fix: ExprAfter::InfixL { bp: 100 },
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
            expr_start: vec![Operator {
                fix: ExprStart::Closed,
                parts: vec!["[|".into(), "|]".into()],
                placeholders: vec![Placeholder {
                    kind: PlaceholderKind::Expr,
                    name: "term".into(),
                }],
            }],
            expr_after: vec![Operator {
                fix: ExprAfter::InfixL { bp: 20 },
                parts: vec!["=".into()],
                placeholders: vec![],
            }],
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
    fn test_app_paren() {
        success_complete(
            common_language(),
            "f (x)",
            "(APP (PRIM f) (OP ( (PRIM x) )))",
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
