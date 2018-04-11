use super::tokenizer::*;

macro_rules! separated_list1 (
    ($tokens:expr, $p_item:ident, $p_sep:ident) => {
        {
            let (mut tokens, item) = $p_item($tokens)?;
            let mut items = vec![item];

            loop {
                match $p_sep(tokens) {
                    Ok((new_tokens, _)) => {
                        let (even_newer_tokens, item) = $p_item(new_tokens)?;
                        items.push(item);
                        tokens = even_newer_tokens;
                    }

                    Err(_) => break Ok((tokens, items))
                }
            }
        }
    }
);

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

pub fn p_literal(tokens: &[Token]) -> Result<(&[Token], Literal), &[Token]> {
    match tokens.get(0) {
        Some(&Token(TokenType::Int(int), range)) => {
            Ok((&tokens[1..], Literal::Int(IntLiteral(int, range))))
        }
        Some(&Token(TokenType::Float(float), range)) => {
            Ok((&tokens[1..], Literal::Float(FloatLiteral(float, range))))
        }
        Some(&Token(TokenType::String(ref string), range)) => {
            Ok((&tokens[1..], Literal::String(StringLiteral(string.clone(), range))))
        }
        _ => Err(tokens),
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct SimpleIdentifier(pub String, pub SourceRange);

impl SourceRanged for SimpleIdentifier {
    fn source_range(&self) -> SourceRange {
        self.1
    }
}

pub fn p_sid(tokens: &[Token]) -> Result<(&[Token], SimpleIdentifier), &[Token]> {
    match tokens.get(0) {
        Some(&Token(TokenType::Id(ref id), range)) => {
            Ok((&tokens[1..], SimpleIdentifier(id.clone(), range)))
        }
        _ => Err(tokens),
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Identifier(pub Vec<SimpleIdentifier>, pub SourceRange);

impl SourceRanged for Identifier {
    fn source_range(&self) -> SourceRange {
        self.1
    }
}

pub fn p_id(tokens: &[Token]) -> Result<(&[Token], Identifier), &[Token]> {
    let (mut tokens, sid) = p_sid(tokens)?;
    let mut sids = vec![sid];

    loop {
        match consume(tokens, TokenType::Scope) {
            Ok(new_tokens) => {
                let (even_newer_tokens, sid) = p_sid(new_tokens)?;
                sids.push(sid);
                tokens = even_newer_tokens;
            }

            Err(_) => {
                let from = sids[0].source_range().from;
                let to = sids[sids.len() - 1].source_range().to;
                return Ok((tokens, Identifier(sids, SourceRange { from, to })));
            }
        }
    }
}

#[test]
fn test_p_id() {
    let tokens = tokenize("abc:: \n  _d  :: __ :: _89");
    let (remaining, id) = p_id(&tokens[..]).unwrap();
    assert_eq!(id.0[0].0, "abc");
    assert_eq!(id.0[1].0, "_d");
    assert_eq!(id.0[2].0, "__");
    assert_eq!(id.0[3].0, "_89");
    assert_eq!(remaining, &[][..]);

    assert!(p_id(&tokenize("")[..]).is_err(););
    assert!(p_id(&tokenize("abc::")[..]).is_err(););
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

pub fn p_meta_item(tokens: &[Token]) -> Result<(&[Token], MetaItem), &[Token]> {
    let (tokens, sid) = p_sid(tokens)?;
    let from = sid.source_range().from;

    if let Ok(tokens) = consume(tokens, TokenType::Eq) {
        let (tokens, lit) = p_literal(tokens)?;
        let to = lit.source_range().to;
        return Ok((tokens, MetaItem::Pair(sid, lit, SourceRange { from, to })));
    } else if let Ok(tokens) = consume(tokens, TokenType::LParen) {
        if let Ok((tokens, lit)) = p_literal(tokens) {
            let (tokens, to) = consume_to(tokens, TokenType::RParen)?;
            return Ok((tokens, MetaItem::LitArg(sid, lit, SourceRange { from, to })));
        }

        let (tokens, args) = separated_list1!(tokens, p_meta_item, p_comma)?;
        let (tokens, to) = consume_to(tokens, TokenType::RParen)?;
        return Ok((tokens, MetaItem::Args(sid, args, SourceRange { from, to })));
    } else {
        return Ok((tokens, MetaItem::Nullary(sid)));
    }
}

#[test]
fn test_meta_item() {
    let tokens = tokenize("abc");
    let (remaining, meta) = p_meta_item(&tokens[..]).unwrap();
    match meta {
        MetaItem::Nullary(sid) => assert_eq!(sid.0, "abc"),
        _ => panic!(),
    }
    assert_eq!(remaining, &[][..]);

    let tokens = tokenize("abc = 12.34");
    let (remaining, meta) = p_meta_item(&tokens[..]).unwrap();
    match meta {
        MetaItem::Pair(sid, Literal::Float(lit), _) => {
            assert_eq!(sid.0, "abc");
            assert_eq!(lit.0, 12.34);
        }
        _ => panic!(),
    }
    assert_eq!(remaining, &[][..]);

    let tokens = tokenize("abc(\"foo\")");
    let (remaining, meta) = p_meta_item(&tokens[..]).unwrap();
    match meta {
        MetaItem::LitArg(sid, Literal::String(lit), _) => {
            assert_eq!(sid.0, "abc");
            assert_eq!(lit.0, "foo");
        }
        _ => panic!(),
    }
    assert_eq!(remaining, &[][..]);

    let tokens = tokenize("a(b = 42 , c(d = 12.34))");
    let (remaining, meta) = p_meta_item(&tokens[..]).unwrap();
    match meta {
        MetaItem::Args(ref sid, ref args, _) => {
            assert_eq!(sid.0, "a");
            match args[0] {
                MetaItem::Pair(ref sid, Literal::Int(ref lit), _) => {
                    assert_eq!(sid.0, "b");
                    assert_eq!(lit.0, 42);
                }
                _ => panic!(),
            }

            match args[1] {
                MetaItem::Args(ref sid, ref args, _) => {
                    assert_eq!(sid.0, "c");
                    match args[0] {
                        MetaItem::Pair(ref sid, Literal::Float(ref lit), _) => {
                            assert_eq!(sid.0, "d");
                            assert_eq!(lit.0, 12.34);
                        }
                        _ => panic!(),
                    }
                }
                _ => panic!(),
            }
        }
        _ => panic!(),
    }
    assert_eq!(remaining, &[][..]);
}

fn consume(tokens: &[Token], tt: TokenType) -> Result<&[Token], &[Token]> {
    match tokens.get(0) {
        Some(token) => {
            if token.0 == tt {
                Ok(&tokens[1..])
            } else {
                Err(tokens)
            }
        }
        None => Err(tokens),
    }
}

fn consume_to(tokens: &[Token], tt: TokenType) -> Result<(&[Token], Position), &[Token]> {
    match tokens.get(0) {
        Some(token) => {
            if token.0 == tt {
                Ok((&tokens[1..], token.source_range().to))
            } else {
                Err(tokens)
            }
        }
        None => Err(tokens),
    }
}

pub fn p_comma(tokens: &[Token]) -> Result<(&[Token], Position), &[Token]> {
    consume_to(tokens, TokenType::Comma)
}

// unimplemented!() TODO remove this line...
