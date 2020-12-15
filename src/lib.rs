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

#[cfg(test)]
mod test {
    use crate::SExpr;

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
}