use nom::{IResult, ErrorKind};
use nom_locate::LocatedSpan;

use super::Position;

type Span<'a> = LocatedSpan<&'a str>;

pub trait Pos {
    /// Get the position of this value in the source.
    fn pos(&self) -> Position;
}

#[derive(Debug, PartialEq, Eq)]
pub struct Attributes(Vec<MetaItem>, Position);

impl Pos for Attributes {
    fn pos(&self) -> Position {
        self.1
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum MetaItem {
    Nullary(SimpleIdentifier),
    Pair(SimpleIdentifier, Literal, Position),
    LitArg(SimpleIdentifier, Literal, Position),
    Args(SimpleIdentifier, Vec<MetaItem>, Position),
}

impl Pos for MetaItem {
    fn pos(&self) -> Position {
        match self {
            &MetaItem::Nullary(ref inner) => inner.pos(),
            &MetaItem::Pair(_, _, pos) => pos,
            &MetaItem::LitArg(_, _, pos) => pos,
            &MetaItem::Args(_, _, pos) => pos,
        }
    }
}

// Identifiers consists purely of ascii alphanumeric chars or underscores (_).
// The length of a simple identifier must be between 1 and 127 (inclusive).
// An identifier starting with an underscore must have a length of at least 2.

#[derive(Debug, PartialEq, Eq)]
pub struct SimpleIdentifier(pub String, pub Position);

impl Pos for SimpleIdentifier {
    fn pos(&self) -> Position {
        self.1
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Identifier(pub Vec<SimpleIdentifier>, pub Position);

impl Pos for Identifier {
    fn pos(&self) -> Position {
        self.1
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct IndexLiteral(pub String, pub Position);

impl Pos for IndexLiteral {
    fn pos(&self) -> Position {
        self.1
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Index {
    Literal(IndexLiteral),
    Macro(MacroInvocation),
}

impl Pos for Index {
    fn pos(&self) -> Position {
        match self {
            &Index::Literal(ref inner) => inner.pos(),
            &Index::Macro(ref inner) => inner.pos(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
// (A, @B) or (a: Foo, b: @Bar)
pub enum TypeList {
    Anon(Vec<Type>, Position),
    Named(Vec<(Attributes, SimpleIdentifier, Type)>, Position),
}

impl Pos for TypeList {
    fn pos(&self) -> Position {
        match self {
            &TypeList::Anon(_, pos) => pos,
            &TypeList::Named(_, pos) => pos,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
// <A, @B> or <A = Foo, B = @Bar>
pub enum TypeApplicationList {
    Anon(Vec<Type>, Position),
    Named(Vec<(Attributes, SimpleIdentifier, Type)>, Position),
}

impl Pos for TypeApplicationList {
    fn pos(&self) -> Position {
        match self {
            &TypeApplicationList::Anon(_, pos) => pos,
            &TypeApplicationList::Named(_, pos) => pos,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Type {
    Attributed(Attributes, Box<Type>, Position),
    Id(Identifier),
    MacroInv(MacroInvocation),
    Ptr(Box<Type>, Position),
    PtrMut(Box<Type>, Position),
    Array(Box<Type>, Position),
    ProductRepeated(Box<Type>, Index, Position),
    Product(TypeList),
    Fun(TypeList, Box<Type>, Position),
    TypeApplication(Identifier, TypeApplicationList, Position),
}

impl Pos for Type {
    fn pos(&self) -> Position {
        match self {
            &Type::Attributed(_, _, pos) => pos,
            &Type::Id(ref inner) => inner.pos(),
            &Type::MacroInv(ref inner) => inner.pos(),
            &Type::Ptr(_, pos) => pos,
            &Type::PtrMut(_, pos) => pos,
            &Type::Array(_, pos) => pos,
            &Type::ProductRepeated(_, _, pos) => pos,
            &Type::Product(ref inner) => inner.pos(),
            &Type::Fun(_, _, pos) => pos,
            &Type::TypeApplication(_, _, pos) => pos,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum TypeDef {
    Inline(Type),
    Attributed(Attributes, Box<TypeDef>, Position),
    TypeLevelFun(Vec<(Attributes, SimpleIdentifier)>, Box<TypeDef>, Position),
    // pub | pub A(Foo, Bar) | pub B | C(x: Foo)
    // First bool is whether the tag constructors are public, second bool (per constructor) is whether its fields are public
    Sum(bool, Vec<(bool, (Attributes, SimpleIdentifier, TypeList))>, Position), // allow not having a TypeList at all in concrete syntax
}

impl Pos for TypeDef {
    fn pos(&self) -> Position {
        match self {
            &TypeDef::Inline(ref inner) => inner.pos(),
            &TypeDef::Attributed(_, _, pos) => pos,
            &TypeDef::TypeLevelFun(_, _, pos) => pos,
            &TypeDef::Sum(_, _, pos) => pos,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct IntLiteral(pub String, pub Position);

impl Pos for IntLiteral {
    fn pos(&self) -> Position {
        self.1
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct FloatLiteral(pub String, pub Position);

impl Pos for FloatLiteral {
    fn pos(&self) -> Position {
        self.1
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct StringLiteral(pub String, pub Position);

impl Pos for StringLiteral {
    fn pos(&self) -> Position {
        self.1
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Literal {
    Int(IntLiteral),
    Float(FloatLiteral),
    String(StringLiteral),
}

impl Pos for Literal {
    fn pos(&self) -> Position {
        match self {
            &Literal::Int(ref inner) => inner.pos(),
            &Literal::Float(ref inner) => inner.pos(),
            &Literal::String(ref inner) => inner.pos(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
// (a, @b) or (a = Foo, b = @bar)
pub enum PatternList {
    Anon(Vec<Pattern>, Position),
    Named(Vec<(Attributes, SimpleIdentifier, Pattern)>, Position),
}

impl Pos for PatternList {
    fn pos(&self) -> Position {
        match self {
            &PatternList::Anon(_, pos) => pos,
            &PatternList::Named(_, pos) => pos,
        }
    }
}

// (Ir)refutability can not be checked syntactically, since you need context whether a sum tag is
// refutable or not (i.e. whether the sum type has more than one summand).
//
// A pattern without tags is irrefutable iff it contains no literals.
#[derive(Debug, PartialEq, Eq)]
pub enum Pattern {
    Id(bool, SimpleIdentifier, Option<Type>, Position),
    Blank(Position),
    Attributed(Attributes, Box<Pattern>, Position),
    Named(SimpleIdentifier, Box<Pattern>, Position), // foo := @bar
    Ptr(Box<Pattern>, Position),
    PtrMut(Box<Pattern>, Position),
    Product(PatternList),
    Sum(Identifier, PatternList, Position), // list parens can be omitted in the syntax for unit sums: `| Foo`
    Literal(Literal),
}

impl Pos for Pattern {
    fn pos(&self) -> Position {
        match self {
            &Pattern::Id(_, _, _, pos) => pos,
            &Pattern::Blank(pos) => pos,
            &Pattern::Attributed(_, _, pos) => pos,
            &Pattern::Named(_, _, pos) => pos,
            &Pattern::Ptr(_, pos) => pos,
            &Pattern::PtrMut(_, pos) => pos,
            &Pattern::Product(ref inner) => inner.pos(),
            &Pattern::Sum(_, _, pos) => pos,
            &Pattern::Literal(ref inner) => inner.pos(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct GuardedPattern(pub Pattern, pub Expression, pub Position);

impl Pos for GuardedPattern {
    fn pos(&self) -> Position {
        self.2
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum TopLevelPattern {
    Guarded(GuardedPattern),
    Unguarded(Pattern),
}

impl Pos for TopLevelPattern {
    fn pos(&self) -> Position {
        match self {
            &TopLevelPattern::Guarded(ref inner) => inner.pos(),
            &TopLevelPattern::Unguarded(ref inner) => inner.pos(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum BinOp {
    LAnd,
    LOr,
    Add,
    BitAnd,
    BitOr,
    BitXor,
    Div,
    Eq,
    Modulus,
    Mul,
    Neq,
    ShiftL,
    ShiftR,
    Sub,
}

#[derive(Debug, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Assign {
    Id,
    LAnd,
    LOr,
    Add,
    BitAnd,
    BitOr,
    BitXor,
    Div,
    Modulus,
    Mul,
    ShiftL,
    ShiftR,
    Sub,
}

#[derive(Debug, PartialEq, Eq)]
// (a, b + c) or (a = x, b = y + z)
pub enum ExpressionList {
    Anon(Vec<Expression>, Position),
    Named(Vec<(Attributes, SimpleIdentifier, Expression)>, Position),
}

impl Pos for ExpressionList {
    fn pos(&self) -> Position {
        match self {
            &ExpressionList::Anon(_, pos) => pos,
            &ExpressionList::Named(_, pos) => pos,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Expression {
    Literal(Literal),
    Attributed(Attributes, Box<Expression>, Position),
    Id(Identifier),
    MacroInv(MacroInvocation),
    Block(Vec<Expression>, Position),
    Ref(Box<Expression>, Position),
    RefMut(Box<Expression>, Position),
    Deref(Box<Expression>, Position),
    DerefMut(Box<Expression>, Position),
    Array(Box<Expression>, Position),
    ArrayIndex(Box<Expression>, Box<Expression>, Position),
    ProductRepeated(Box<Expression>, Index, Position),
    Product(ExpressionList),
    ProductAccessAnon(Box<Expression>, Index, Position),
    ProductAccessNamed(Box<Expression>, SimpleIdentifier, Position),
    Fun(Vec<Pattern>, Type, Vec<Expression>, Position),
    FunApplication(Box<Expression>, ExpressionList, Position),
    Generic(Vec<(Attributes, SimpleIdentifier)>, Box<Expression>, Position),
    TypeApplication(Box<Expression>, TypeApplicationList, Position),
    UnaryOperator(UnOp, Box<Expression>, Position),
    BinaryOperator(Box<Expression>, BinOp, Box<Expression>, Position),
    Cast(Box<Expression>, Type, Position),
    Assignment(Box<Expression>, Assign, Box<Expression>, Position),
    Let(Pattern, Box<Expression>, Position),
    If(Box<Expression>, Box<Expression>, Position),
    IfElse(Box<Expression>, Box<Expression>, Box<Expression>, Position),
    Match(Box<Expression>, Vec<(Pattern, Expression)>, Position),
    While(Box<Expression>, Box<Expression>, Position),
    WhileMatch(Box<Expression>, Pattern, Box<Expression>, Position),
    Return(Box<Expression>, Position),
    Break(Box<Expression>, Position),
    Label(SimpleIdentifier, Position),
    Goto(SimpleIdentifier, Position),
}

impl Pos for Expression {
    fn pos(&self) -> Position {
        match self {
            &Expression::Literal(ref inner) => inner.pos(),
            &Expression::Attributed(_, _, pos) => pos,
            &Expression::Id(ref inner) => inner.pos(),
            &Expression::MacroInv(ref inner) => inner.pos(),
            &Expression::Block(_, pos) => pos,
            &Expression::Ref(_, pos) => pos,
            &Expression::RefMut(_, pos) => pos,
            &Expression::Deref(_, pos) => pos,
            &Expression::DerefMut(_, pos) => pos,
            &Expression::Array(_, pos) => pos,
            &Expression::ArrayIndex(_, _, pos) => pos,
            &Expression::ProductRepeated(_, _, pos) => pos,
            &Expression::Product(ref inner) => inner.pos(),
            &Expression::ProductAccessAnon(_, _, pos) => pos,
            &Expression::ProductAccessNamed(_, _, pos) => pos,
            &Expression::Fun(_, _, _, pos) => pos,
            &Expression::FunApplication(_, _, pos) => pos,
            &Expression::Generic(_, _, pos) => pos,
            &Expression::TypeApplication(_, _, pos) => pos,
            &Expression::UnaryOperator(_, _, pos) => pos,
            &Expression::BinaryOperator(_, _, _, pos) => pos,
            &Expression::Cast(_, _, pos) => pos,
            &Expression::Assignment(_, _, _, pos) => pos,
            &Expression::Let(_, _, pos) => pos,
            &Expression::If(_, _, pos) => pos,
            &Expression::IfElse(_, _, _, pos) => pos,
            &Expression::Match(_, _, pos) => pos,
            &Expression::While(_, _, pos) => pos,
            &Expression::WhileMatch(_, _, _, pos) => pos,
            &Expression::Return(_, pos) => pos,
            &Expression::Break(_, pos) => pos,
            &Expression::Label(_, pos) => pos,
            &Expression::Goto(_, pos) => pos,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct MacroInvocation(pub Identifier, pub String, pub Position);

impl Pos for MacroInvocation {
    fn pos(&self) -> Position {
        self.2
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum UseStart {
    Super(Position),
    Mod(Position),
    Extern(Position),
    Magic(Position), // really special-case this?
    Id(SimpleIdentifier),
}

impl Pos for UseStart {
    fn pos(&self) -> Position {
        match self {
            &UseStart::Super(pos) => pos,
            &UseStart::Mod(pos) => pos,
            &UseStart::Extern(pos) => pos,
            &UseStart::Magic(pos) => pos,
            &UseStart::Id(ref inner) => inner.pos(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum UseTree {
    Selff(Position),
    Leaf(SimpleIdentifier),
    Inner(Vec<(SimpleIdentifier, UseTree)>, Position),
}

impl Pos for UseTree {
    fn pos(&self) -> Position {
        match self {
            &UseTree::Selff(pos) => pos,
            &UseTree::Leaf(ref inner) => inner.pos(),
            &UseTree::Inner(_, pos) => pos,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct FfiBlock(pub String, pub Vec<(Attributes, FfiItem)>, pub Position);

impl Pos for FfiBlock {
    fn pos(&self) -> Position {
        self.2
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum FfiItem {
    Fun(bool, SimpleIdentifier, TypeList, Box<Type>, Position),
}

impl Pos for FfiItem {
    fn pos(&self) -> Position {
        match self {
            &FfiItem::Fun(_, _, _, _, pos) => pos,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Module(pub Vec<(Attributes, Item)>, pub Position);

impl Pos for Module {
    fn pos(&self) -> Position {
        self.1
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Magic(pub MetaItem, pub Position);

impl Pos for Magic {
    fn pos(&self) -> Position {
        self.1
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum MagicExpression {
    Magic(Magic),
    Expression(Expression),
}

impl Pos for MagicExpression {
    fn pos(&self) -> Position {
        match self {
            &MagicExpression::Magic(ref inner) => inner.pos(),
            &MagicExpression::Expression(ref inner) => inner.pos(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum MagicTypeDef {
    Magic(Magic),
    TypeDef(TypeDef),
}

impl Pos for MagicTypeDef {
    fn pos(&self) -> Position {
        match self {
            &MagicTypeDef::Magic(ref inner) => inner.pos(),
            &MagicTypeDef::TypeDef(ref inner) => inner.pos(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Item {
    Use(bool, UseStart, UseTree, Position),
    Mod(bool, SimpleIdentifier, Box<Module>, Position),
    TypeDef(bool, SimpleIdentifier, MagicTypeDef, Position),
    Macro(bool, SimpleIdentifier, Magic, Position),
    Attribute(bool, SimpleIdentifier, Magic, Position),
    Let(bool, Pattern, MagicExpression, Position),
    Ffi(SimpleIdentifier, FfiBlock, Position),
}

impl Pos for Item {
    fn pos(&self) -> Position {
        match self {
            &Item::Use(_, _, _, pos) => pos,
            &Item::Mod(_, _, _, pos) => pos,
            &Item::TypeDef(_, _, _, pos) => pos,
            &Item::Macro(_, _, _, pos) => pos,
            &Item::Attribute(_, _, _, pos) => pos,
            &Item::Let(_, _, _, pos) => pos,
            &Item::Ffi(_, _, pos) => pos,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct File(pub Vec<(Attributes, Item)>, pub Position);

impl Pos for File {
    fn pos(&self) -> Position {
        self.1
    }
}

// keywords: mod, use, self, super, extern, goto, label, break, return, while, match, if, then, else, let, as, type, macro, magic, attribute, mut

named!(pub p_skip0<Span, ()>, map!(
    many0!(alt!(
        map!(one_of!(" \n"), |_| ()) |
        do_parse!(
            tag!("//") >>
            many0!(none_of!("\n")) >>
            tag!("\n") >>
            (())
        )
    )), |_| ()));

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
    let (input, _) = try_parse!(input, p_skip0);
    if simple_id.0.len() == 1 && simple_id.0.starts_with("_") {
        IResult::Error(error_code!(ErrorKind::Custom(0)))
    } else if simple_id.0.len() > 127 {
        IResult::Error(error_code!(ErrorKind::Custom(1)))
    } else if simple_id.0 == "mod" || simple_id.0 == "use" || simple_id.0 == "self" ||
              simple_id.0 == "super" || simple_id.0 == "extern" ||
              simple_id.0 == "magic" ||
              simple_id.0 == "pub" ||
              simple_id.0 == "mut" || simple_id.0 == "let" || simple_id.0 == "type" ||
              simple_id.0 == "macro" ||
              simple_id.0 == "attribute" ||
              simple_id.0 == "label" || simple_id.0 == "goto" ||
              simple_id.0 == "return" || simple_id.0 == "break" ||
              simple_id.0 == "if" || simple_id.0 == "then" || simple_id.0 == "else" ||
              simple_id.0 == "match" ||
              simple_id.0 == "while" ||
              simple_id.0 == "as" {
        IResult::Error(error_code!(ErrorKind::Custom(2)))
    } else {
        IResult::Done(input, simple_id)
    }
}

named!(pub p_scope_separator<Span, ()>, do_parse!(tag!("::") >> p_skip0 >> (())));

named!(pub p_id<Span, Identifier>, map!(
    separated_list!(p_scope_separator, p_simple_id),
    |ids| {
        let pos = Position::from_positions(ids.first().unwrap().1, ids.last().unwrap().1);
        Identifier(ids, pos)
    }
));

// pub enum MetaItem {
//     Nullary(Identifier, Position),
//     Pair(Identifier, Literal, Position),
//     LitArg(Identifier, Literal, Position),
//     Args(Identifier, Vec<MetaItem>, Position),
// }

named!(pub p_meta_item_nullary<Span, MetaItem>, map!(p_simple_id, MetaItem::Nullary));

// named!(pub p_meta_item_pair<Span, MetaItem>, do_parse!(
//     id: p_simple_id >>
//     p_eq >>
//     lit: p_literal >>
//     (MetaItem::Pair(id, lit, Position::from_positions(id.pos(), lit.pos())))
// ));

#[test]
fn test_skip0() {
    works!(p_skip0, "", 0);
    works!(p_skip0, "a", 1);
    works!(p_skip0, " ", 0);
    works!(p_skip0, "   ", 0);
    works!(p_skip0, "\n", 0);
    works!(p_skip0, "   \n  \n\n  ", 0);

    not_complete!(p_skip0, "\r");
    not_complete!(p_skip0, "\t");

    not_complete!(p_skip0, "//");
    not_complete!(p_skip0, "// ");

    works!(p_skip0, "//\n", 0);
    works!(p_skip0, "// \n", 0);
    works!(p_skip0, "///\n", 0);
    works!(p_skip0, "////\n", 0);
    works!(p_skip0, "//\n//\n", 0);
    works!(p_skip0, "//\na", 1);
    works!(p_skip0, "// \rö\n   \n    /// /\n  a", 1);
}

#[test]
fn test_simple_id() {
    works!(p_simple_id, "_a", 0);
    works!(p_simple_id, "_a   ", 0);
    works!(p_simple_id, "a", 0);
    works!(p_simple_id, "A", 0);
    works!(p_simple_id, "aA", 0);
    works!(p_simple_id, "__", 0);
    works!(p_simple_id, "_9", 0);
    works!(p_simple_id, "a9", 0);
    works!(p_simple_id, "a_9", 0);
    works!(p_simple_id, "_aöa", 3);
    works!(p_simple_id,
           "abcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefg",
           0); // 127 characters

    fails!(p_simple_id,
           "abcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefgh"); // 128 characters
    fails!(p_simple_id, "ö");
    fails!(p_simple_id, "_");
    fails!(p_simple_id, "-");
    fails!(p_simple_id, "9");
    fails!(p_simple_id, "9a");
    fails!(p_simple_id, "-a");
    fails!(p_simple_id, "");

    fails!(p_simple_id, "pub");
    works!(p_simple_id, "pubb", 0);
    fails!(p_simple_id, "mod");
    fails!(p_simple_id, "use");
    fails!(p_simple_id, "self");
    fails!(p_simple_id, "extern");
    fails!(p_simple_id, "goto");
    fails!(p_simple_id, "label");
    fails!(p_simple_id, "break");
    fails!(p_simple_id, "return");
    fails!(p_simple_id, "while");
    fails!(p_simple_id, "match");
    fails!(p_simple_id, "if");
    fails!(p_simple_id, "then");
    fails!(p_simple_id, "else");
    fails!(p_simple_id, "let");
    fails!(p_simple_id, "as");
    fails!(p_simple_id, "type");
    fails!(p_simple_id, "macro");
    fails!(p_simple_id, "magic");
    fails!(p_simple_id, "attribute");
    fails!(p_simple_id, "mut");
}

#[test]
fn test_id() {
    works!(p_id, "aö", 2);
    works!(p_id, "a::_a::__::t5ö", 2);
    works!(p_id, "a  ::  _a::__    ::  t5  ö", 2);
    fails!(p_id, "");
}
