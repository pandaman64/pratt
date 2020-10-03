use anyhow::*;
use std::sync::Arc;

use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyntaxKind {
    Whitespace,
    IntLit,
    Ident,
    Symbol,
    Primitive,
    PrefixOp(UnaryOp),
    PostfixOp(UnaryOp),
    BinOp(BinOp),
    ParenOp(ParenOp),
    QuantifierOp(QuantifierOp),
    ExprRoot,
}

impl fmt::Display for SyntaxKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use SyntaxKind::*;

        match self {
            Whitespace => write!(f, "WS"),
            IntLit => write!(f, "INTEGER"),
            Ident => write!(f, "IDENT"),
            Symbol => write!(f, "SYM"),
            Primitive => write!(f, "PRIM"),
            PrefixOp(_op) => write!(f, "PREFIX"),
            PostfixOp(_op) => write!(f, "POSTFIX"),
            BinOp(_op) => write!(f, "BINARY"),
            ParenOp(_op) => write!(f, "PAREN"),
            QuantifierOp(_op) => write!(f, "QUANTIFIER"),
            ExprRoot => write!(f, "EXPR"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token<'a> {
    kind: SyntaxKind,
    value: &'a str,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnaryOp {
    pub symbols: &'static str,
    pub bp: u16,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinOp {
    pub symbols: &'static str,
    pub bp: u16,
    pub left_assoc: bool,
}

impl BinOp {
    fn lbp(&self) -> u16 {
        if self.left_assoc {
            self.bp
        } else {
            self.bp + 1
        }
    }

    fn rbp(&self) -> u16 {
        if self.left_assoc {
            self.bp + 1
        } else {
            self.bp
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ParenOp {
    pub op: &'static str,
    pub open_symbols: &'static str,
    pub close_symbols: &'static str,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct QuantifierOp {
    pub quantifier: &'static str,
    pub separator: &'static str,
    pub bp: u16,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NodeOrToken<'a> {
    Token(Arc<Token<'a>>),
    Node(Arc<GreenNode<'a>>),
}

impl NodeOrToken<'_> {
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
}

impl fmt::Display for NodeOrToken<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            NodeOrToken::Token(token) => write!(f, "{}", token.value),
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

// TODO: fix
impl fmt::Display for GreenNode<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}", self.kind)?;
        for child in self.non_trivial() {
            write!(f, " {}", child)?;
        }
        write!(f, ")")
    }
}

#[derive(Debug, Clone, Default)]
pub struct Language {
    pub infix_table: Vec<BinOp>,
    pub prefix_table: Vec<UnaryOp>,
    pub postfix_table: Vec<UnaryOp>,
    pub parenfix_table: Vec<ParenOp>,
    pub quantifierfix_table: Vec<QuantifierOp>,
}

pub struct Parser<'a> {
    input: &'a str,
    language: Language,
    position: usize,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str, language: Language) -> Self {
        Self {
            input,
            language,
            position: 0,
        }
    }

    pub fn remaining(&self) -> &'a str {
        &self.input[self.position..]
    }

    fn advance(&mut self, len: usize) {
        assert!(self.remaining().len() >= len, "input is too short");
        self.position += len;
    }

    fn peek_token_at(&self, position: usize) -> Result<Token<'a>> {
        ensure!(
            self.remaining().is_char_boundary(position),
            "invalid position"
        );
        let input = &self.remaining()[position..];
        ensure!(!input.is_empty(), "input is empty");

        let token = match input.chars().next().unwrap() {
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
        };

        Ok(token)
    }

    fn peek_token(&self) -> Result<Token<'a>> {
        self.peek_token_at(0)
    }

    fn expect_token(
        &mut self,
        token: Token<'a>,
        children: &mut Vec<NodeOrToken<'a>>,
    ) -> Result<()> {
        ensure!(
            matches!(self.peek_token(), Ok(t) if token == t),
            "expected {:?}, got {}",
            token,
            self.remaining()
        );
        self.next_token(children).unwrap();
        Ok(())
    }

    fn next_token(&mut self, children: &mut Vec<NodeOrToken<'a>>) -> Result<()> {
        let token = self.peek_token()?;
        self.advance(token.value.len());
        children.push(token.into());
        Ok(())
    }

    fn next_ident(&mut self, children: &mut Vec<NodeOrToken<'a>>) -> Result<()> {
        let token = self.peek_token()?;
        ensure!(
            token.kind == SyntaxKind::Ident,
            "expected identifier, got {:?}",
            token
        );
        self.advance(token.value.len());
        children.push(token.into());
        Ok(())
    }

    fn skip_ws(&mut self, children: &mut Vec<NodeOrToken<'a>>) {
        if let Ok(token) = self.peek_token() {
            if token.kind == SyntaxKind::Whitespace {
                self.expect_token(token, children).unwrap();
            }
        }
    }

    fn expect(&mut self, target: &str, children: &mut Vec<NodeOrToken<'a>>) -> Result<()> {
        ensure!(
            self.remaining().starts_with(target),
            "expected {}, got {}",
            target,
            self.remaining(),
        );

        let token = Token {
            kind: SyntaxKind::Symbol,
            value: &self.remaining()[0..target.len()],
        };
        children.push(token.into());

        self.advance(target.len());
        Ok(())
    }

    fn primary_expr(&mut self) -> Result<GreenNode<'a>> {
        match self.peek_token()? {
            token if token.kind == SyntaxKind::IntLit || token.kind == SyntaxKind::Ident => {
                let mut children = vec![];
                self.expect_token(token, &mut children).unwrap();
                Ok(GreenNode::new(SyntaxKind::Primitive, children))
            }
            token => bail!("expected primary expr, got {:?}", token),
        }
    }

    pub fn expr(&mut self, min_bp: u16) -> Result<GreenNode<'a>> {
        // prefix
        let mut lhs = if let Some(op) = self.peek_quantifierfix() {
            let mut children = vec![];
            self.expect(op.quantifier, &mut children).unwrap();
            self.skip_ws(&mut children);

            self.next_ident(&mut children)?;
            self.skip_ws(&mut children);

            self.expect(op.separator, &mut children)?;
            self.skip_ws(&mut children);

            let node = self.expr(op.bp)?;
            children.push(node.into());

            GreenNode::new(SyntaxKind::QuantifierOp(op), children)
        } else if let Some(op) = self.peek_prefix() {
            let mut children = vec![];

            self.expect(op.symbols, &mut children).unwrap();
            self.skip_ws(&mut children);

            let node = self.expr(op.bp)?;
            children.push(node.into());

            GreenNode::new(SyntaxKind::PrefixOp(op), children)
        } else if let Some(op) = self.peek_parenfix() {
            let mut children = vec![];

            self.expect(op.open_symbols, &mut children).unwrap();
            self.skip_ws(&mut children);

            let node = self.expr(0)?;
            children.push(node.into());
            self.skip_ws(&mut children);

            self.expect(op.close_symbols, &mut children)?;
            GreenNode::new(SyntaxKind::ParenOp(op), children)
        } else {
            self.primary_expr()?
        };

        loop {
            let mut spaces = vec![];
            self.skip_ws(&mut spaces);

            if self.remaining().is_empty() {
                break;
            }

            if let Some(op) = self.peek_postfix() {
                if op.bp < min_bp {
                    break;
                }

                let mut children = vec![];
                children.push(lhs.into());
                children.extend(spaces);
                self.expect(op.symbols, &mut children).unwrap();
                self.skip_ws(&mut children);
                lhs = GreenNode::new(SyntaxKind::PostfixOp(op), children);
                continue;
            }

            if let Some(op) = self.peek_infix() {
                if op.lbp() < min_bp {
                    break;
                }

                let mut children = vec![];
                children.push(lhs.into());
                children.extend(spaces);
                self.expect(&op.symbols, &mut children).unwrap();
                self.skip_ws(&mut children);
                let rhs = self.expr(op.rbp())?;
                children.push(rhs.into());
                lhs = GreenNode::new(SyntaxKind::BinOp(op), children);
                continue;
            }

            break;
        }

        Ok(lhs)
    }

    // The following functions traverse input token by token to support operators
    // with alphabets and numerals in them.
    // For example, "⊢t xyz" is tokenized as ['⊢', 't', ' ', 'xyz'], while "⊢txyz" is ['⊢', 'txyz'].
    fn peek(&self, mut symbols: &str) -> bool {
        let mut position = 0;
        loop {
            if symbols.is_empty() {
                return true;
            }

            match self.peek_token_at(position) {
                Ok(token) if symbols.starts_with(token.value) => {
                    symbols = &symbols[token.value.len()..];
                    position += token.value.len();
                }
                _ => return false,
            }
        }
    }

    fn peek_infix(&self) -> Option<BinOp> {
        for op in self.language.infix_table.iter() {
            if self.peek(op.symbols) {
                return Some(*op);
            }
        }
        None
    }

    fn peek_prefix(&self) -> Option<UnaryOp> {
        for op in self.language.prefix_table.iter() {
            if self.peek(op.symbols) {
                return Some(*op);
            }
        }
        None
    }

    fn peek_postfix(&self) -> Option<UnaryOp> {
        for op in self.language.postfix_table.iter() {
            if self.peek(op.symbols) {
                return Some(*op);
            }
        }
        None
    }

    fn peek_parenfix(&self) -> Option<ParenOp> {
        for op in self.language.parenfix_table.iter() {
            if self.peek(op.open_symbols) {
                return Some(*op);
            }
        }
        None
    }

    fn peek_quantifierfix(&self) -> Option<QuantifierOp> {
        for op in self.language.quantifierfix_table.iter() {
            if self.peek(op.quantifier) {
                return Some(*op);
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
            infix_table: vec![
                BinOp {
                    symbols: "=",
                    bp: 20,
                    left_assoc: true,
                },
                BinOp {
                    symbols: "+",
                    bp: 50,
                    left_assoc: true,
                },
                BinOp {
                    symbols: "-",
                    bp: 50,
                    left_assoc: true,
                },
                BinOp {
                    symbols: "^",
                    bp: 80,
                    left_assoc: false,
                },
            ],
            prefix_table: vec![UnaryOp {
                symbols: "-",
                bp: 60,
            }],
            postfix_table: vec![UnaryOp {
                symbols: "!",
                bp: 70,
            }],
            parenfix_table: vec![ParenOp {
                op: "paren",
                open_symbols: "(",
                close_symbols: ")",
            }],
            quantifierfix_table: vec![
                QuantifierOp {
                    quantifier: "∀",
                    separator: ".",
                    bp: 10,
                },
                QuantifierOp {
                    quantifier: "fun",
                    separator: "->",
                    bp: 10,
                },
            ],
        }
    }

    fn success_complete(language: Language, input: &str, expected: &str) {
        let _ = tracing_subscriber::fmt::try_init();

        let mut parser = Parser::new(input, language);
        let e = parser.expr(0).unwrap();
        tracing::debug!(%e);
        assert_eq!(
            e.to_string(),
            expected,
            "parse result doesn't match: {:?}",
            e
        );
        assert!(
            parser.remaining().is_empty(),
            "input must be consumed, remaining: {}",
            parser.remaining()
        );
        // assert_eq!(e.text_width, input.len(),);
    }

    #[test]
    fn test_intlit() {
        success_complete(common_language(), "12345", "(PRIM 12345)");
    }

    #[test]
    fn test_binop() {
        success_complete(
            common_language(),
            "123 + 45",
            "(BINARY (PRIM 123) + (PRIM 45))",
        );
    }

    #[test]
    fn test_left_assoc() {
        success_complete(
            common_language(),
            "123 + 45 + 67",
            "(BINARY (BINARY (PRIM 123) + (PRIM 45)) + (PRIM 67))",
        );
    }

    #[test]
    fn test_right_assoc() {
        success_complete(
            common_language(),
            "2^3^4",
            "(BINARY (PRIM 2) ^ (BINARY (PRIM 3) ^ (PRIM 4)))",
        );
    }

    #[test]
    fn test_prefix() {
        success_complete(
            common_language(),
            "-2 + 5 + -4 ^ 2",
            "(BINARY (BINARY (PREFIX - (PRIM 2)) + (PRIM 5)) + (PREFIX - (BINARY (PRIM 4) ^ (PRIM 2))))"
        );
    }

    #[test]
    fn test_postfix() {
        success_complete(
            common_language(),
            "1 - -2! + 3",
            "(BINARY (BINARY (PRIM 1) - (PREFIX - (POSTFIX (PRIM 2) !))) + (PRIM 3))",
        );
    }

    #[test]
    fn test_paren() {
        success_complete(
            common_language(),
            "-(2 + 5 + -4)^2",
            "(PREFIX - (BINARY (PAREN ( (BINARY (BINARY (PRIM 2) + (PRIM 5)) + (PREFIX - (PRIM 4))) )) ^ (PRIM 2)))"
        );
    }

    #[test]
    fn test_ident() {
        success_complete(
            common_language(),
            "a^3 + b^3 - c^3",
            "(BINARY (BINARY (BINARY (PRIM a) ^ (PRIM 3)) + (BINARY (PRIM b) ^ (PRIM 3))) - (BINARY (PRIM c) ^ (PRIM 3)))",
        )
    }

    #[test]
    fn test_ident_underscore() {
        success_complete(
            common_language(),
            "a_1 + b__",
            "(BINARY (PRIM a_1) + (PRIM b__))",
        )
    }

    #[test]
    fn test_equal_op() {
        success_complete(
            common_language(),
            "a^3 + b^3 = c^3",
            "(BINARY (BINARY (BINARY (PRIM a) ^ (PRIM 3)) + (BINARY (PRIM b) ^ (PRIM 3))) = (BINARY (PRIM c) ^ (PRIM 3)))",
        )
    }

    #[test]
    fn test_confusing_op() {
        let language = Language {
            infix_table: vec![
                BinOp {
                    symbols: "⊢t",
                    bp: 100,
                    left_assoc: true,
                },
                BinOp {
                    symbols: "->",
                    bp: 200,
                    left_assoc: false,
                },
            ],
            ..Language::default()
        };
        success_complete(
            language,
            "Γ ⊢t pre -> post",
            "(BINARY (PRIM Γ) ⊢t (BINARY (PRIM pre) -> (PRIM post)))",
        )
    }

    #[test]
    fn test_parens() {
        let language = Language {
            infix_table: vec![BinOp {
                symbols: "=",
                bp: 20,
                left_assoc: true,
            }],
            parenfix_table: vec![ParenOp {
                op: "denotation",
                open_symbols: "[|",
                close_symbols: "|]",
            }],
            ..Language::default()
        };
        success_complete(
            language,
            "[| t |] = 100",
            "(BINARY (PAREN [| (PRIM t) |]) = (PRIM 100))",
        )
    }

    #[test]
    fn test_quantifier() {
        success_complete(
            common_language(),
            "∀y. (fun x -> y) = fun z -> y",
            "(QUANTIFIER ∀ y . (BINARY (PAREN ( (QUANTIFIER fun x -> (PRIM y)) )) = (QUANTIFIER fun z -> (PRIM y))))",
        )
    }
}
