use nom_locate::LocatedSpan;

use super::{Position, p_skip0, identifiers::{SimpleIdentifier, p_simple_id, Identifier, p_identifier}, attributes::{Attribute, p_attribute}};

type Span<'a> = LocatedSpan<&'a str>;

#[derive(Debug, PartialEq, Eq)]
pub enum ConstExpression {
    IntLiteral(u64, Position)
}

// Option<Attribute>, BaseConstExpression
