use nom_locate::LocatedSpan;
use nom::{IResult, ErrorKind};

use super::Position;

type Span<'a> = LocatedSpan<&'a str>;

// Valid characters for simple identifiers: alphanumeric, `_`. An identifier starting with `_`
// must have a length of at least 2. Maximum length of a simple identifier is 255.

#[derive(Debug, PartialEq, Eq)]
pub struct SimpleIdentifier(pub String, pub Position);

#[derive(Debug, PartialEq, Eq)]
pub enum Identifier {
    Simple(SimpleIdentifier),
    /// foo::bar::baz becomes ("foo", Box(("bar", Box("baz"))))
    Compound(SimpleIdentifier, Box<Identifier>, Position),
}

impl Identifier {
    pub fn is_simple(&self) -> bool {
        match self {
            &Identifier::Simple(_) => true,
            _ => false,
        }
    }

    pub fn is_compound(&self) -> bool {
        match self {
            &Identifier::Compound(_, _, _) => true,
            _ => false,
        }
    }
}

fn is_id_char(chr: char) -> bool {
    chr.is_ascii_alphanumeric() || chr == '_'
}

fn is_id_start_char(chr: char) -> bool {
    chr.is_ascii_alphabetic() || chr == '_'
}

fn concat_into_string<'a>(initial: &'a str, remainder: &'a str) -> String {
    let mut ret = String::with_capacity(initial.len() + remainder.len());
    ret.push_str(initial);
    ret.push_str(remainder);
    ret
}

named!(_sid<Span, SimpleIdentifier>,
    do_parse!(
        start: position!() >>
        initial: take_while1!(is_id_start_char) >>
        remaining: take_while!(is_id_char) >>
        end: position!() >>
        (SimpleIdentifier(concat_into_string(initial.fragment, remaining.fragment), Position::new(start, end)))
    )
);

pub fn p_simple_id(input: Span) -> IResult<Span, SimpleIdentifier> {
    let (input, simple_id) = try_parse!(input, _sid);
    if simple_id.0.len() == 1 && simple_id.0.starts_with("_") {
        IResult::Error(error_code!(ErrorKind::Custom(0)))
    } else if simple_id.0.len() > 255 {
        IResult::Error(error_code!(ErrorKind::Custom(1)))
    } else if simple_id.0 == "pub" || simple_id.0 == "struct" || simple_id.0 == "enum" {
        IResult::Error(error_code!(ErrorKind::Custom(2)))
    } else {
        IResult::Done(input, simple_id)
    }
}

named!(_scope_resolution<Span, Span>, tag!("::"));

pub fn p_identifier(input: Span) -> IResult<Span, Identifier> {
    let (input, start) = try_parse!(input, position!());
    let (input, qualifier) = try_parse!(input, p_simple_id);

    match _scope_resolution(input) {
        IResult::Done(input, _) => {
            let (input, inner) = try_parse!(input, p_identifier);
            let (input, end) = try_parse!(input, position!());
            IResult::Done(input,
                          Identifier::Compound(qualifier,
                                               Box::new(inner),
                                               Position::new(start, end)))
        }
        _ => IResult::Done(input, Identifier::Simple(qualifier)),
    }
}

#[test]
fn test_id() {
    works_check!(p_identifier, "aö", 2, is_simple);
    works_check!(p_identifier, "a::_a::__::t5ö", 2, is_compound);

    fails!(p_identifier, "ä::a");
    works_check!(p_identifier, "a:a", 2, is_simple);
    fails!(p_identifier, "a::ä");
    fails!(p_identifier, "a::::b");
    fails!(p_identifier, "a::");
    fails!(p_identifier, "::a");
    fails!(p_identifier, "a::5");
    fails!(p_identifier, "a::_");
    fails!(p_identifier, "a::_::a");
    fails!(p_identifier, "a::a::_");
    fails!(p_identifier, "_::a");
    fails!(p_identifier, "a:: b");
    works_check!(p_identifier, "a ::b", 4, is_simple);
    works_check!(p_identifier, "a: :b", 4, is_simple);
    fails!(p_identifier, " a");
}

#[test]
fn test_simple_id() {
    works!(p_simple_id, "_a", 0);
    works!(p_simple_id, "a", 0);
    works!(p_simple_id, "A", 0);
    works!(p_simple_id, "aA", 0);
    works!(p_simple_id, "__", 0);
    works!(p_simple_id, "_9", 0);
    works!(p_simple_id, "a9", 0);
    works!(p_simple_id, "a_9", 0);
    works!(p_simple_id, "_aöa", 3);
    works!(p_simple_id,
           "abcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefg",
           0); // 255 characters

    fails!(p_simple_id,
           "abcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefgh"); // 256 characters
    fails!(p_simple_id, "ö");
    fails!(p_simple_id, "_");
    fails!(p_simple_id, "-");
    fails!(p_simple_id, "9");
    fails!(p_simple_id, "9a");
    fails!(p_simple_id, "-a");
    fails!(p_simple_id, "");

    fails!(p_simple_id, "pub");
    fails!(p_simple_id, "struct");
    fails!(p_simple_id, "enum");
    works!(p_simple_id, "pubb", 0);
}
