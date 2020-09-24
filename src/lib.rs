use anyhow::*;

use std::fmt;

pub enum SExpr {
    Atom(String),
    Cons { head: String, tail: Vec<SExpr> },
}

impl fmt::Display for SExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SExpr::Atom(s) => write!(f, "{}", s),
            SExpr::Cons { head, tail } => {
                write!(f, "({}", head)?;
                for x in tail.iter() {
                    write!(f, " {}", x)?;
                }
                write!(f, ")")
            }
        }
    }
}

pub enum Expr {
    UnaryOp(String, Box<Expr>),
    BinOp(Box<Expr>, String, Box<Expr>),
    IntLit(u64),
    Ident(String),
}

impl Expr {
    pub fn as_sexpr(&self) -> SExpr {
        match self {
            Expr::UnaryOp(op, v) => SExpr::Cons {
                head: op.clone(),
                tail: vec![v.as_sexpr()],
            },
            Expr::BinOp(lhs, op, rhs) => SExpr::Cons {
                head: op.clone(),
                tail: vec![lhs.as_sexpr(), rhs.as_sexpr()],
            },
            Expr::IntLit(v) => SExpr::Atom(v.to_string()),
            Expr::Ident(x) => SExpr::Atom(x.to_string()),
        }
    }
}

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

pub struct Parser<'a> {
    input: &'a str,
    position: usize,
    infix_table: Vec<BinOp>,
    prefix_table: Vec<UnaryOp>,
    postfix_table: Vec<UnaryOp>,
}
impl<'a> Parser<'a> {
    pub fn new(
        input: &'a str,
        infix_table: Vec<BinOp>,
        prefix_table: Vec<UnaryOp>,
        postfix_table: Vec<UnaryOp>,
    ) -> Self {
        Self {
            input,
            position: 0,
            infix_table,
            prefix_table,
            postfix_table,
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

    fn expect(&mut self, target: &str) -> Result<()> {
        ensure!(
            self.remaining().starts_with(target),
            "expected {}, got {}",
            target,
            self.remaining(),
        );
        self.advance(target.len());
        Ok(())
    }

    fn primary_expr(&mut self) -> Result<Expr> {
        match self.peek_token()? {
            token if token.kind == TokenKind::IntLit => {
                let v = token.value.parse()?;
                self.expect_token(token).unwrap();
                Ok(Expr::IntLit(v))
            }
            token if token.kind == TokenKind::Ident => {
                self.expect_token(token).unwrap();
                Ok(Expr::Ident(token.value.to_string()))
            }
            token => bail!("expected primary expr, got {:?}", token),
        }
    }

    pub fn expr(&mut self, min_bp: u16) -> Result<Expr> {
        // prefix
        let mut lhs = if let Some(op) = self.peek_prefix() {
            self.expect(op.symbols)?;
            self.skip_ws();
            let inner = self.expr(op.bp)?;

            Expr::UnaryOp(op.symbols.to_string(), Box::new(inner))
        } else if self.remaining().starts_with('(') {
            // TODO: generic handling
            self.expect("(")?;
            self.skip_ws();
            let inner = self.expr(0)?;
            self.skip_ws();
            self.expect(")")?;
            inner
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

                self.expect(op.symbols)?;
                self.skip_ws();
                lhs = Expr::UnaryOp(op.symbols.to_string(), Box::new(lhs));
                continue;
            }

            if let Some(binop) = self.peek_infix() {
                if binop.lbp() < min_bp {
                    break;
                }

                // consume only if parsing the right hand side
                self.expect(&binop.symbols)?;
                self.skip_ws();
                let rhs = self.expr(binop.rbp())?;
                lhs = Expr::BinOp(Box::new(lhs), binop.symbols.to_string(), Box::new(rhs));
                continue;
            }

            break;
        }

        Ok(lhs)
    }

    // The following functions traverse input token by token to support operators
    // with alphabets and numerals in them.
    // For example, "⊢t xyz" is tokenized as ['⊢', 't', ' ', 'xyz'], while "⊢txyz" is ['⊢', 'txyz'].
    fn peek_infix(&self) -> Option<BinOp> {
        'ops: for op in self.infix_table.iter() {
            for (idx, c) in op.symbols.char_indices() {
                let mut buf: [u8; 4] = [0, 0, 0, 0];
                let buf: &mut [u8] = &mut buf;
                if !matches!(self.peek_token_at(idx), Ok(t) if c.encode_utf8(buf) == t.value) {
                    continue 'ops;
                }
            }
            return Some(*op);
        }
        None
    }

    fn peek_prefix(&self) -> Option<UnaryOp> {
        'ops: for op in self.prefix_table.iter() {
            for (idx, c) in op.symbols.char_indices() {
                let mut buf: [u8; 4] = [0, 0, 0, 0];
                let buf: &mut [u8] = &mut buf;
                if !matches!(self.peek_token_at(idx), Ok(t) if c.encode_utf8(buf) == t.value) {
                    continue 'ops;
                }
            }
            return Some(*op);
        }
        None
    }

    fn peek_postfix(&self) -> Option<UnaryOp> {
        'ops: for op in self.postfix_table.iter() {
            for (idx, c) in op.symbols.char_indices() {
                let mut buf: [u8; 4] = [0, 0, 0, 0];
                let buf: &mut [u8] = &mut buf;
                if !matches!(self.peek_token_at(idx), Ok(t) if c.encode_utf8(buf) == t.value) {
                    continue 'ops;
                }
            }
            return Some(*op);
        }
        None
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn success_complete(input: &str, expected: &str) {
        let infix_table = vec![
            BinOp {
                symbols: "==",
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
        ];
        let prefix_table = vec![UnaryOp {
            symbols: "-",
            bp: 60,
        }];
        let postfix_table = vec![UnaryOp {
            symbols: "!",
            bp: 70,
        }];
        let mut parser = Parser::new(input, infix_table, prefix_table, postfix_table);
        let e = parser.expr(0).unwrap();
        assert!(parser.remaining().is_empty());
        assert_eq!(e.as_sexpr().to_string(), expected);
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
        success_complete("-(2 + 5 + -4)^2", "(- (^ (+ (+ 2 5) (- 4)) 2))");
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
        success_complete("a^3 + b^3 == c^3", "(== (+ (^ a 3) (^ b 3)) (^ c 3))")
    }

    #[test]
    fn test_confusing_op() {
        let infix_table = vec![
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
        ];
        let prefix_table = vec![];
        let postfix_table = vec![];
        let mut parser = Parser::new("Γ ⊢t pre -> post", infix_table, prefix_table, postfix_table);
        let e = parser.expr(0).unwrap();
        assert!(parser.remaining().is_empty());
        assert_eq!(e.as_sexpr().to_string(), "(⊢t Γ (-> pre post))");
    }
}
