use nom_locate::LocatedSpan;
use nom::IResult;

use super::{Position, identifiers::{SimpleIdentifier, p_simple_id}};

type Span<'a> = LocatedSpan<&'a str>;

#[derive(Debug, PartialEq, Eq)]
pub enum Attribute {
    Simple(SimpleIdentifier, Position),
    Stuff(SimpleIdentifier, String, Position),
}

impl Attribute {
    pub fn is_simple(&self) -> bool {
        match self {
            &Attribute::Simple(_, _) => true,
            _ => false,
        }
    }

    pub fn is_stuff(&self) -> bool {
        match self {
            &Attribute::Stuff(_, _, _) => true,
            _ => false,
        }
    }
}

named!(rbracket<Span, Span>, tag!("]"));

pub fn p_attribute(input: Span) -> IResult<Span, Attribute> {
    let (input, start) = try_parse!(input, position!());
    let (input, _) = try_parse!(input, tag!("#["));
    let (input, id) = try_parse!(input, p_simple_id);

    match rbracket(input) {
        IResult::Done(input, _) => {
            let (input, end) = try_parse!(input, position!());
            IResult::Done(input,
                          Attribute::Simple(id, Position::new(start, end)))
        }
        _ => {
            let (input, _) = try_parse!(input, tag!("("));
            let (input, stuff) = try_parse!(input, is_not!("()"));
            let (input, _) = try_parse!(input, tag!(")]"));
            let (input, end) = try_parse!(input, position!());
            IResult::Done(input,
                          Attribute::Stuff(id, stuff.fragment.to_string(), Position::new(start, end)))
        },
    }
}

#[test]
fn test_attribute() {
    works_check!(p_attribute,
              "#[foo]", 0, is_simple);
    works_check!(p_attribute,
              "#[foo(arbitrary non-empty stuff =,:][, but no parens)]", 0, is_stuff);

    fails!(p_attribute, "#[foo()]");
    fails!(p_attribute, "#[]");
    fails!(p_attribute, "#[f f]");
    fails!(p_attribute, "#[_]");
    fails!(p_attribute, "#[foo(()]");
    fails!(p_attribute, "#[foo())]");
    fails!(p_attribute, "#[foo(())]");
}
