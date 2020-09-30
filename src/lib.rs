use anyhow::*;

use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    Whitespace,
    IntLit,
    Ident,
    Symbol,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token<'a> {
    kind: TokenKind,
    position: usize,
    value: &'a str,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnaryOp {
    symbols: &'static str,
    bp: u16,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinOp {
    symbols: &'static str,
    bp: u16,
    left_assoc: bool,
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
    op: &'static str,
    open_symbols: &'static str,
    close_symbols: &'static str,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct QuantifierOp {
    quantifier: &'static str,
    separator: &'static str,
    bp: u16,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TreeKind<'a> {
    IntLit(Token<'a>),
    Ident(Token<'a>),
    Symbol(Token<'a>),
    PrefixOp(UnaryOp),
    PostfixOp(UnaryOp),
    BinOp(BinOp),
    ParenOp(ParenOp),
    QuantifierOp(QuantifierOp),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CST<'a> {
    kind: TreeKind<'a>,
    // position: usize,
    // len: usize,
    children: Vec<CST<'a>>,
}

impl fmt::Display for CST<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.kind {
            TreeKind::IntLit(token) | TreeKind::Ident(token) | TreeKind::Symbol(token) => {
                assert!(self.children.is_empty());
                write!(f, "{}", token.value)
            }
            TreeKind::PrefixOp(op) | TreeKind::PostfixOp(op) => {
                assert_eq!(self.children.len(), 1);
                write!(f, "({} {})", op.symbols, self.children[0])
            }
            TreeKind::BinOp(op) => {
                assert_eq!(self.children.len(), 2);
                write!(
                    f,
                    "({} {} {})",
                    op.symbols, self.children[0], self.children[1]
                )
            }
            TreeKind::ParenOp(op) => {
                assert_eq!(self.children.len(), 1);
                write!(f, "({} {})", op.op, self.children[0])
            }
            TreeKind::QuantifierOp(op) => {
                assert_eq!(self.children.len(), 2);
                write!(
                    f,
                    "({} {} {})",
                    op.quantifier, self.children[0], self.children[1]
                )
            }
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct Language {
    infix_table: Vec<BinOp>,
    prefix_table: Vec<UnaryOp>,
    postfix_table: Vec<UnaryOp>,
    parenfix_table: Vec<ParenOp>,
    quantifierfix_table: Vec<QuantifierOp>,
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
                    kind: TokenKind::IntLit,
                    value,
                    position: self.position,
                }
            }
            c if c.is_whitespace() => {
                let value = input.split(|c: char| !c.is_whitespace()).next().unwrap();

                Token {
                    kind: TokenKind::Whitespace,
                    value,
                    position: self.position,
                }
            }
            c if c.is_alphabetic() => {
                let value = input
                    .split(|c: char| !(c == '_' || c.is_alphanumeric()))
                    .next()
                    .unwrap();

                Token {
                    kind: TokenKind::Ident,
                    value,
                    position: self.position,
                }
            }
            c => Token {
                kind: TokenKind::Symbol,
                value: &input[0..c.len_utf8()],
                position: self.position,
            },
        };

        Ok(token)
    }

    fn peek_token(&self) -> Result<Token<'a>> {
        self.peek_token_at(0)
    }

    fn expect_token(&mut self, token: Token<'a>) -> Result<()> {
        ensure!(
            matches!(self.peek_token(), Ok(t) if token == t),
            "expected {:?}, got {}",
            token,
            self.remaining()
        );
        self.next_token().unwrap();
        Ok(())
    }

    fn next_token(&mut self) -> Result<Token<'a>> {
        let token = self.peek_token()?;
        self.advance(token.value.len());
        Ok(token)
    }

    fn skip_ws(&mut self) {
        if let Ok(token) = self.peek_token() {
            if token.kind == TokenKind::Whitespace {
                self.expect_token(token).unwrap();
            }
        }
    }

    fn expect(&mut self, target: &str) -> Result<Token<'a>> {
        ensure!(
            self.remaining().starts_with(target),
            "expected {}, got {}",
            target,
            self.remaining(),
        );
        let token = Token {
            kind: TokenKind::Symbol,
            position: self.position,
            value: &self.remaining()[0..target.len()],
        };
        self.advance(target.len());
        Ok(token)
    }

    fn primary_expr(&mut self) -> Result<CST<'a>> {
        match self.peek_token()? {
            token if token.kind == TokenKind::IntLit => {
                self.expect_token(token).unwrap();
                Ok(CST {
                    kind: TreeKind::IntLit(token),
                    // position: token.position,
                    // len: token.value.len(),
                    children: vec![],
                })
            }
            token if token.kind == TokenKind::Ident => {
                self.expect_token(token).unwrap();
                Ok(CST {
                    kind: TreeKind::Ident(token),
                    // position: token.position,
                    // len: token.value.len(),
                    children: vec![],
                })
            }
            token => bail!("expected primary expr, got {:?}", token),
        }
    }

    pub fn expr(&mut self, min_bp: u16) -> Result<CST<'a>> {
        // prefix
        let mut lhs = if let Some(op) = self.peek_quantifierfix() {
            self.expect(op.quantifier).unwrap();
            self.skip_ws();

            let token = self.next_token()?;
            ensure!(
                token.kind == TokenKind::Ident,
                "expected ident, got {:?}",
                token
            );
            let ident = CST {
                kind: TreeKind::Ident(token),
                children: vec![],
            };
            self.skip_ws();

            self.expect(op.separator)?;
            self.skip_ws();

            let inner = self.expr(op.bp)?;

            CST {
                kind: TreeKind::QuantifierOp(op),
                children: vec![ident, inner],
            }
        } else if let Some(op) = self.peek_prefix() {
            self.expect(op.symbols).unwrap();
            self.skip_ws();
            let inner = self.expr(op.bp)?;

            CST {
                kind: TreeKind::PrefixOp(op),
                children: vec![inner],
            }
        } else if let Some(op) = self.peek_parenfix() {
            self.expect(op.open_symbols).unwrap();
            self.skip_ws();
            let inner = self.expr(0)?;
            self.skip_ws();
            self.expect(op.close_symbols)?;
            CST {
                kind: TreeKind::ParenOp(op),
                children: vec![inner],
            }
        } else {
            self.primary_expr()?
        };

        loop {
            self.skip_ws();

            if self.remaining().is_empty() {
                break;
            }

            if let Some(op) = self.peek_postfix() {
                if op.bp < min_bp {
                    break;
                }

                self.expect(op.symbols).unwrap();
                self.skip_ws();
                lhs = CST {
                    kind: TreeKind::PostfixOp(op),
                    children: vec![lhs],
                };
                continue;
            }

            if let Some(op) = self.peek_infix() {
                if op.lbp() < min_bp {
                    break;
                }

                // consume only if parsing the right hand side
                self.expect(&op.symbols).unwrap();
                self.skip_ws();
                let rhs = self.expr(op.rbp())?;
                lhs = CST {
                    kind: TreeKind::BinOp(op),
                    children: vec![lhs, rhs],
                };
                continue;
            }

            break;
        }

        Ok(lhs)
    }

    // The following functions traverse input token by token to support operators
    // with alphabets and numerals in them.
    // For example, "⊢t xyz" is tokenized as ['⊢', 't', ' ', 'xyz'], while "⊢txyz" is ['⊢', 'txyz'].
    fn peek(&self, symbols: &str) -> bool {
        for (idx, c) in symbols.char_indices() {
            let mut buf: [u8; 4] = [0, 0, 0, 0];
            let buf: &mut [u8] = &mut buf;
            if !matches!(self.peek_token_at(idx), Ok(t) if c.encode_utf8(buf) == t.value) {
                return false;
            }
        }
        true
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

    fn success_complete(input: &str, expected: &str) {
        let language = Language {
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
            quantifierfix_table: vec![QuantifierOp {
                quantifier: "∀",
                separator: ".",
                bp: 10,
            }],
        };
        let mut parser = Parser::new(input, language);
        let e = parser.expr(0).unwrap();
        eprintln!("{}", e.to_string());
        assert_eq!(e.to_string(), expected);
        assert!(
            parser.remaining().is_empty(),
            "input must be consumed, remaining: {}",
            parser.remaining()
        );
    }

    #[test]
    fn test_intlit() {
        success_complete("12345", "12345");
    }

    #[test]
    fn test_binop() {
        success_complete("123 + 45", "(+ 123 45)");
    }

    #[test]
    fn test_left_assoc() {
        success_complete("123 + 45 + 67", "(+ (+ 123 45) 67)");
    }

    #[test]
    fn test_right_assoc() {
        success_complete("2^3^4", "(^ 2 (^ 3 4))");
    }

    #[test]
    fn test_prefix() {
        success_complete("-2 + 5 + -4 ^ 2", "(+ (+ (- 2) 5) (- (^ 4 2)))");
    }

    #[test]
    fn test_postfix() {
        success_complete("1 - -2! + 3", "(+ (- 1 (- (! 2))) 3)");
    }

    #[test]
    fn test_paren() {
        success_complete("-(2 + 5 + -4)^2", "(- (^ (paren (+ (+ 2 5) (- 4))) 2))");
    }

    #[test]
    fn test_ident() {
        success_complete("a^3 + b^3 - c^3", "(- (+ (^ a 3) (^ b 3)) (^ c 3))")
    }

    #[test]
    fn test_ident_underscore() {
        success_complete("a_1 + b__", "(+ a_1 b__)")
    }

    #[test]
    fn test_multichar_op() {
        success_complete("a^3 + b^3 = c^3", "(= (+ (^ a 3) (^ b 3)) (^ c 3))")
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
        let mut parser = Parser::new("Γ ⊢t pre -> post", language);
        let e = parser.expr(0).unwrap();
        assert_eq!(e.to_string(), "(⊢t Γ (-> pre post))");
        assert!(parser.remaining().is_empty());
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
        let mut parser = Parser::new("[| t |] = 100", language);
        let e = parser.expr(0).unwrap();
        assert_eq!(e.to_string(), "(= (denotation t) 100)");
        assert!(parser.remaining().is_empty());
    }

    #[test]
    fn test_quantifier() {
        success_complete("∀x. ∀y. x = y", "(∀ x (∀ y (= x y)))")
    }
}
