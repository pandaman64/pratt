use std::fmt;

#[derive(Debug)]
pub enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

impl fmt::Display for SExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SExpr::Atom(s) => write!(f, "{}", s),
            SExpr::List(l) => {
                let mut iter = l.iter();
                write!(f, "(")?;
                if let Some(head) = iter.next() {
                    write!(f, "{}", head)?;
                }
                for rest in iter {
                    write!(f, " {}", rest)?;
                }
                write!(f, ")")
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum LeadingOpKind {
    Prefix { right_bp: u16 },
    Paren,
}

#[derive(Debug, PartialEq, Eq)]
pub enum FollowingOpKind {
    Postfix { left_bp: u16 },
    Infix { left_bp: u16, right_bp: u16 },
}

#[derive(Debug)]
pub struct Operator<K> {
    kind: K,
    name: String,
    symbols: Vec<char>,
}

pub type LeadingOp = Operator<LeadingOpKind>;
pub type FollowingOp = Operator<FollowingOpKind>;

pub fn prefix(name: String, symbols: Vec<char>, right_bp: u16) -> LeadingOp {
    LeadingOp {
        kind: LeadingOpKind::Prefix { right_bp },
        name,
        symbols,
    }
}

pub fn paren(name: String, symbols: Vec<char>) -> LeadingOp {
    LeadingOp {
        kind: LeadingOpKind::Paren,
        name,
        symbols,
    }
}

pub fn postfix(name: String, symbols: Vec<char>, left_bp: u16) -> FollowingOp {
    FollowingOp {
        kind: FollowingOpKind::Postfix { left_bp },
        name,
        symbols,
    }
}

pub fn infix(name: String, symbols: Vec<char>, left_bp: u16, right_bp: u16) -> FollowingOp {
    FollowingOp {
        kind: FollowingOpKind::Infix { left_bp, right_bp },
        name,
        symbols,
    }
}

#[derive(Debug)]
pub struct Language {
    leading_operators: Vec<LeadingOp>,
    following_operators: Vec<FollowingOp>,
}

impl Language {
    pub fn new(leading_operators: Vec<LeadingOp>, following_operators: Vec<FollowingOp>) -> Self {
        Self {
            leading_operators,
            following_operators,
        }
    }
}

#[derive(Debug)]
pub struct Input<'s> {
    text: &'s str,
    position: usize,
}

impl<'s> Input<'s> {
    pub fn new(text: &'s str) -> Self {
        Self { text, position: 0 }
    }

    // 現在の場所から1文字読む
    pub fn peek(&self) -> Option<char> {
        self.text[self.position..].chars().next()
    }

    // 現在の場所を1文字分進める
    pub fn bump(&mut self) {
        self.position += self.peek().unwrap().len_utf8();
    }
}

pub fn parse_atom(input: &mut Input<'_>) -> SExpr {
    match input.peek().unwrap() {
        c if c.is_ascii_digit() => {
            input.bump(); // 数値を入力から消費
            SExpr::Atom(c.into())
        }
        c => panic!("expected an atom, got {}", c),
    }
}

fn following_operator_lbp(operator: char) -> Option<u16> {
    match operator {
        '?' => Some(20),
        '+' => Some(50),
        '-' => Some(50),
        '*' => Some(80),
        _ => None,
    }
}

fn parse_expr_bp(input: &mut Input<'_>, min_bp: u16) -> SExpr {
    let mut leading_expr = match input.peek().unwrap() {
        '-' => {
            const NEG_RBP: u16 = 51;
            input.bump(); // '-'を消費
            let following_expr = parse_expr_bp(input, NEG_RBP);
            SExpr::List(vec![SExpr::Atom("-".into()), following_expr])
        }
        '(' => {
            input.bump(); // '('を消費
            let following_expr = parse_expr_bp(input, 0);

            // ')'が来なければいけない
            assert!(matches!(input.peek(), Some(')')));
            input.bump();

            SExpr::List(vec![SExpr::Atom("paren".into()), following_expr])
        }
        _ => parse_atom(input),
    };

    loop {
        match input.peek() {
            None => return leading_expr,
            Some(c) => {
                if matches!(following_operator_lbp(c), Some(bp) if bp <= min_bp) {
                    return leading_expr;
                }
            }
        }

        match input.peek() {
            Some('?') => {
                input.bump();
                leading_expr = SExpr::List(vec![SExpr::Atom("?".into()), leading_expr]);
            }
            Some('+') => {
                const PLUS_RBP: u16 = 51;
                input.bump();
                let following_expr = parse_expr_bp(input, PLUS_RBP);
                leading_expr =
                    SExpr::List(vec![SExpr::Atom("+".into()), leading_expr, following_expr]);
            }
            Some('-') => {
                const MINUS_RBP: u16 = 51;
                input.bump();
                let following_expr = parse_expr_bp(input, MINUS_RBP);
                leading_expr =
                    SExpr::List(vec![SExpr::Atom("-".into()), leading_expr, following_expr]);
            }
            Some('*') => {
                const MULT_RBP: u16 = 81;
                input.bump();
                let following_expr = parse_expr_bp(input, MULT_RBP);
                leading_expr =
                    SExpr::List(vec![SExpr::Atom("*".into()), leading_expr, following_expr]);
            }
            _ => return leading_expr,
        }
    }
}

pub fn parse_expr(input: &mut Input<'_>) -> SExpr {
    parse_expr_bp(input, 0)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_sexpr_print() {
        let e = SExpr::List(vec![
            SExpr::Atom("+".into()),
            SExpr::Atom("1".into()),
            SExpr::List(vec![
                SExpr::Atom("+".into()),
                SExpr::Atom("2".into()),
                SExpr::Atom("3".into()),
            ]),
        ]);

        assert_eq!(e.to_string(), "(+ 1 (+ 2 3))");
    }

    #[test]
    fn test_atom() {
        let e = parse_atom(&mut Input::new("3"));

        assert_eq!(e.to_string(), "3");
    }

    // パースした結果として入力が全て消費され想定通りのS式が得られているかチェックする
    fn complete_parse(input: &str, expected: &str) {
        let mut input = Input::new(input);
        let e = parse_expr(&mut input);

        assert_eq!(e.to_string(), expected);
        assert!(input.peek().is_none());
    }

    #[test]
    fn test_atom_expr() {
        complete_parse("7", "7")
    }

    #[test]
    fn test_simple_prefix() {
        complete_parse("-8", "(- 8)")
    }

    #[test]
    fn test_paren() {
        complete_parse("(-1)", "(paren (- 1))")
    }

    #[test]
    fn test_simple_postfix() {
        complete_parse("1?", "(? 1)")
    }

    #[test]
    fn test_simple_infix() {
        complete_parse("1+2", "(+ 1 2)")
    }

    #[test]
    fn test_infix_and_prefix() {
        complete_parse("1+-2", "(+ 1 (- 2))")
    }

    #[test]
    fn test_different_position() {
        complete_parse("1--2", "(- 1 (- 2))")
    }

    #[test]
    fn test_infix_assoc() {
        complete_parse("1+2+3", "(+ (+ 1 2) 3)")
    }

    #[test]
    fn test_infix_prec() {
        complete_parse("1*2+3", "(+ (* 1 2) 3)")
    }
}
