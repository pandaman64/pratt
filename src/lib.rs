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
        }
    }
}

pub struct Parser<'a> {
    input: &'a str,
    position: usize,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str) -> Self {
        Self { input, position: 0 }
    }

    pub fn remaining(&self) -> &'a str {
        &self.input[self.position..]
    }

    fn skip_ws(&mut self) {
        for (idx, c) in self.remaining().char_indices() {
            if !c.is_whitespace() {
                self.advance(idx).unwrap();
                return;
            }
        }
        self.advance(self.remaining().len()).unwrap();
    }

    fn expect(&mut self, target: &str) -> Result<()> {
        ensure!(
            self.remaining().starts_with(target),
            "expected {}, got {}",
            target,
            self.remaining(),
        );
        self.advance(target.len())
    }

    fn advance(&mut self, len: usize) -> Result<()> {
        ensure!(self.remaining().len() >= len, "input is too short");
        self.position += len;
        Ok(())
    }

    fn intlit(&mut self) -> Result<Expr> {
        let len = self
            .remaining()
            .split(|c| c < '0' || c > '9')
            .next()
            .ok_or_else(|| anyhow!("not an integer"))?
            .len();

        let v = self.remaining()[..len].parse()?;
        self.advance(len).unwrap();

        Ok(Expr::IntLit(v))
    }

    pub fn expr(&mut self, min_bp: u16) -> Result<Expr> {
        // prefix
        let mut lhs = if let Some((op, bp)) = self.peek_prefix() {
            self.expect(op)?;
            self.skip_ws();
            let inner = self.expr(bp)?;

            Expr::UnaryOp(op.to_string(), Box::new(inner))
        } else if self.remaining().starts_with('(') {
            // TODO: generic handling
            self.expect("(")?;
            self.skip_ws();
            let inner = self.expr(0)?;
            self.skip_ws();
            self.expect(")")?;
            inner
        } else {
            match self.remaining().chars().next().context("unexpceted EOF")? {
                c if '0' <= c && c <= '9' => self.intlit()?,
                c => bail!("unexpected primary expr: {}", c),
            }
        };

        loop {
            self.skip_ws();

            if self.remaining().is_empty() {
                break;
            }

            if let Some((op, bp)) = self.peek_postfix() {
                if bp < min_bp {
                    break;
                }

                self.expect(op)?;
                self.skip_ws();
                lhs = Expr::UnaryOp(op.to_string(), Box::new(lhs));
                continue;
            }

            if let Some((op, lbp, rbp)) = self.peek_infix() {
                if lbp < min_bp {
                    break;
                }

                // consume only if parsing the right hand side
                self.expect(op)?;
                self.skip_ws();
                let rhs = self.expr(rbp)?;
                lhs = Expr::BinOp(Box::new(lhs), op.to_string(), Box::new(rhs));
                continue;
            }

            break;
        }

        Ok(lhs)
    }

    fn peek_prefix(&self) -> Option<(&'a str, u16)> {
        match self.remaining() {
            s if s.starts_with('-') => Some(("-", 60)),
            _ => None,
        }
    }

    fn peek_infix(&self) -> Option<(&'a str, u16, u16)> {
        match self.remaining() {
            s if s.starts_with('+') => Some(("+", 50, 51)),
            s if s.starts_with('-') => Some(("-", 50, 51)),
            s if s.starts_with('^') => Some(("^", 81, 80)),
            _ => None,
        }
    }

    fn peek_postfix(&self) -> Option<(&'a str, u16)> {
        match self.remaining() {
            s if s.starts_with('!') => Some(("!", 70)),
            _ => None,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_intlit() {
        let mut parser = Parser::new("12345");
        let e = parser.expr(0).unwrap();
        assert!(parser.remaining().is_empty());
        assert_eq!(e.as_sexpr().to_string(), "12345");
    }

    #[test]
    fn test_binop() {
        let mut parser = Parser::new("123 + 45");
        let e = parser.expr(0).unwrap();
        assert!(parser.remaining().is_empty());
        assert_eq!(e.as_sexpr().to_string(), "(+ 123 45)");
    }

    #[test]
    fn test_left_assoc() {
        let mut parser = Parser::new("123 + 45 + 67");
        let e = parser.expr(0).unwrap();
        assert!(parser.remaining().is_empty());
        assert_eq!(e.as_sexpr().to_string(), "(+ (+ 123 45) 67)");
    }

    #[test]
    fn test_right_assoc() {
        let mut parser = Parser::new("2^3^4");
        let e = parser.expr(0).unwrap();
        assert!(parser.remaining().is_empty());
        assert_eq!(e.as_sexpr().to_string(), "(^ 2 (^ 3 4))");
    }

    #[test]
    fn test_prefix() {
        let mut parser = Parser::new("-2 + 5 + -4 ^ 2");
        let e = parser.expr(0).unwrap();
        assert!(parser.remaining().is_empty());
        assert_eq!(e.as_sexpr().to_string(), "(+ (+ (- 2) 5) (- (^ 4 2)))");
    }

    #[test]
    fn test_postfix() {
        let mut parser = Parser::new("1 - -2! + 3");
        let e = parser.expr(0).unwrap();
        assert!(parser.remaining().is_empty());
        assert_eq!(e.as_sexpr().to_string(), "(+ (- 1 (- (! 2))) 3)");
    }

    #[test]
    fn test_paren() {
        let mut parser = Parser::new("-(2 + 5 + -4)^2");
        let e = parser.expr(0).unwrap();
        assert!(parser.remaining().is_empty());
        assert_eq!(e.as_sexpr().to_string(), "(- (^ (+ (+ 2 5) (- 4)) 2))");
    }
}
