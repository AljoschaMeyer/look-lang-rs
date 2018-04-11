use super::tokenizer::*;

#[derive(Debug, PartialEq, Eq)]
pub struct IntLiteral(pub u64, pub SourceRange);

impl SourceRanged for IntLiteral {
    fn source_range(&self) -> SourceRange {
        self.1
    }
}

#[derive(Debug, PartialEq)]
pub struct FloatLiteral(pub f64, pub SourceRange);
impl Eq for FloatLiteral {} // Literal is never NaN, Inf or -Inf

impl SourceRanged for FloatLiteral {
    fn source_range(&self) -> SourceRange {
        self.1
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct StringLiteral(pub String, pub SourceRange);

impl SourceRanged for StringLiteral {
    fn source_range(&self) -> SourceRange {
        self.1
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Literal {
    Int(IntLiteral),
    Float(FloatLiteral),
    String(StringLiteral),
}

impl SourceRanged for Literal {
    fn source_range(&self) -> SourceRange {
        match self {
            &Literal::Int(ref inner) => inner.source_range(),
            &Literal::Float(ref inner) => inner.source_range(),
            &Literal::String(ref inner) => inner.source_range(),
        }
    }
}

// pub fn p_literal(tokens: &[Token]) -> Result<(&[Token], Literal), &[Token]> {
//     match tokens.get(0) {
//         Some(&Token(TokenType::Int(int), range)) => {
//             Ok((&tokens[1..], Literal::Int(IntLiteral(int, range))))
//         }
//         Some(&Token(TokenType::Float(float), range)) => {
//             Ok((&tokens[1..], Literal::Float(FloatLiteral(float, range))))
//         }
//         Some(&Token(TokenType::String(ref string), range)) => {
//             Ok((&tokens[1..], Literal::String(StringLiteral(string.clone(), range))))
//         }
//         _ => Err(tokens),
//     }
// }

pub fn p_literal(tokens: &mut Tokenizer) -> Result<Literal, Option<Token>> {
    match tokens.next() {
        Some(Token(TokenType::Int(int), range)) => Ok(Literal::Int(IntLiteral(int, range))),
        Some(Token(TokenType::Float(float), range)) => {
            Ok(Literal::Float(FloatLiteral(float, range)))
        }
        Some(Token(TokenType::String(string), range)) => {
            Ok(Literal::String(StringLiteral(string, range)))
        }
        Some(t) => Err(Some(t)),
        None => Err(None),
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct SimpleIdentifier(pub String, pub SourceRange);

impl SourceRanged for SimpleIdentifier {
    fn source_range(&self) -> SourceRange {
        self.1
    }
}

pub fn p_sid(tokens: &mut Tokenizer) -> Result<SimpleIdentifier, Option<Token>> {
    match tokens.next() {
        Some(Token(TokenType::Id(id), range)) => Ok(SimpleIdentifier(id, range)),
        Some(t) => Err(Some(t)),
        None => Err(None),
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Identifier(pub Vec<SimpleIdentifier>, pub SourceRange);

impl SourceRanged for Identifier {
    fn source_range(&self) -> SourceRange {
        self.1
    }
}

pub fn p_id(tokens: &mut Tokenizer) -> Result<Identifier, Option<Token>> {
    let mut sids = vec![];

    loop {
        match tokens.next() {
            Some(Token(TokenType::Id(id), range)) => sids.push(SimpleIdentifier(id, range)),
            Some(t) => return Err(Some(t)),
            None => return Err(None),
        }

        match tokens.peek() {
            Some(&Token(TokenType::Scope, _)) => tokens.next(),
            _ => {
                let from = sids[0].source_range().from;
                let to = sids[sids.len() - 1].source_range().to;

                return Ok(Identifier(sids, SourceRange { from, to }));
            }
        };
    }
}

#[test]
fn test_p_id() {
    let mut tok = Tokenizer::new("abc:: \n  _d  :: __ :: _89");
    let id = p_id(&mut tok).unwrap();

    assert_eq!(id.0[0].0, "abc");
}

#[derive(Debug, PartialEq, Eq)]
pub enum MetaItem {
    Nullary(SimpleIdentifier),
    Pair(SimpleIdentifier, Literal, SourceRange),
    LitArg(SimpleIdentifier, Literal, SourceRange),
    Args(SimpleIdentifier, Vec<MetaItem>, SourceRange),
}

impl SourceRanged for MetaItem {
    fn source_range(&self) -> SourceRange {
        match self {
            &MetaItem::Nullary(ref inner) => inner.source_range(),
            &MetaItem::Pair(_, _, range) => range,
            &MetaItem::LitArg(_, _, range) => range,
            &MetaItem::Args(_, _, range) => range,
        }
    }
}

// pub fn p_meta_item(tokens: &mut Tokenizer) -> Result<MetaItem, Option<Token>> {
//     let sid = p_sid(tokens)?;
//     let from = sid.source_range().from;
//
//     match tokens.peek() {
//         Some(&Token(TokenType::Eq, _)) => {
//             tokens.next();
//             let lit = p_literal(tokens)?;
//             let to = lit.source_range().to;
//             return Ok(MetaItem::Pair(sid, lit, SourceRange { from, to }));
//         }
//
//         Some(&Token(TokenType::LParen, _)) => {
//             tokens.next();
//
//             match tokens.peek() {
//                 Some(&Token(TokenType::Int(int), int_range)) => {
//                     tokens.next();
//                     let Token(_, SourceRange { from: _, to }) = tokens.consume(TokenType::RParen)?;
//                     return Ok(MetaItem::LitArg(sid,
//                                                Literal::Int(IntLiteral(int, int_range)),
//                                                SourceRange { from, to }));
//                 }
//
//                 Some(&Token(TokenType::Float(float), float_range)) => {
//                     tokens.next();
//                     let Token(_, SourceRange { from: _, to }) = tokens.consume(TokenType::RParen)?;
//                     return Ok(MetaItem::LitArg(sid,
//                                                Literal::Float(FloatLiteral(float, float_range)),
//                                                SourceRange { from, to }));
//                 }
//
//                 Some(&Token(TokenType::String(ref string), string_range)) => {
//                     match tokens.next() {
//                         Some(Token(TokenType::String(string), string_range)) => {
//                             let Token(_, SourceRange { from: _, to }) =
//                                 tokens.consume(TokenType::RParen)?;
//                             return Ok(MetaItem::LitArg(sid,
//                                                        Literal::String(StringLiteral(string,
//                                                                                      string_range)),
//                                                        SourceRange { from, to }));
//                         }
//                         _ => unreachable!(),
//                     }
//                 }
//
//                 Some(&Token(TokenType::Id(_), _)) => {
//                     let mut args = vec![];
//
//                     loop {
//                         match p_meta_item(tokens) {
//                             Ok(attr) => args.push(attr),
//                             Err(Some(Token(TokenType::RParen, SourceRange { from: _, to }))) => {
//                                 return Ok(MetaItem::Args(sid, args, SourceRange { from, to }))
//                             }
//                             Err(Some(t)) => return Err(Some(t)),
//                             Err(None) => return Err(None),
//                         }
//                     }
//                 }
//
//                 _ => unimplemented!(), // TODO errors
//             }
//         }
//
//         _ => return Ok(MetaItem::Nullary(sid)),
//     }
// }
//
// #[test]
// fn test_meta_item() {
//     let mut tok = Tokenizer::new("abc");
//     match p_meta_item(&mut tok).unwrap() {
//         MetaItem::Nullary(sid) => assert_eq!(sid.0, "abc"),
//         _ => panic!(),
//     }
//
//     let mut tok = Tokenizer::new("abc = 12.34");
//     match p_meta_item(&mut tok).unwrap() {
//         MetaItem::Pair(sid, Literal::Float(lit), _) => {
//             assert_eq!(sid.0, "abc");
//             assert_eq!(lit.0, 12.34);
//         }
//         _ => panic!(),
//     }
//
//     let mut tok = Tokenizer::new("abc(12.34)");
//     match p_meta_item(&mut tok).unwrap() {
//         MetaItem::LitArg(sid, Literal::Float(lit), _) => {
//             assert_eq!(sid.0, "abc");
//             assert_eq!(lit.0, 12.34);
//         }
//         _ => panic!(),
//     }
//
//     let mut tok = Tokenizer::new("a(b = 42 , c(d = 12.34))");
//     match p_meta_item(&mut tok).unwrap() {
//         MetaItem::Args(ref sid, ref args, _) => {
//             assert_eq!(sid.0, "a");
//             match args[0] {
//                 MetaItem::Pair(ref sid, Literal::Int(ref lit), _) => {
//                     assert_eq!(sid.0, "b");
//                     assert_eq!(lit.0, 42);
//                 }
//                 _ => panic!(),
//             }
//
//             match args[1] {
//                 MetaItem::Args(ref sid, ref args, _) => {
//                     assert_eq!(sid.0, "a");
//                     match args[0] {
//                         MetaItem::Pair(ref sid, Literal::Float(ref lit), _) => {
//                             assert_eq!(sid.0, "d");
//                             assert_eq!(lit.0, 12.34);
//                         }
//                         _ => panic!(),
//                     }
//                 }
//                 _ => panic!(),
//             }
//         }
//         _ => panic!(),
//     }
// }

// unimplemented!() TODO remove this line...
