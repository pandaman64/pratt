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

pub fn parse_expr(input: &mut Input<'_>) -> SExpr {
    let leading_expr = match input.peek().unwrap() {
        '-' => {
            input.bump(); // '-'を消費
            let following_expr = parse_expr(input);
            SExpr::List(vec![SExpr::Atom("-".into()), following_expr])
        }
        '(' => {
            input.bump(); // '('を消費
            let following_expr = parse_expr(input);

            // ')'が来なければいけない
            assert!(matches!(input.peek(), Some(')')));
            input.bump();

            SExpr::List(vec![SExpr::Atom("paren".into()), following_expr])
        }
        _ => parse_atom(input),
    };

    match input.peek() {
        Some('?') => {
            input.bump();
            SExpr::List(vec![SExpr::Atom("?".into()), leading_expr])
        }
        _ => leading_expr,
    }
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
}
