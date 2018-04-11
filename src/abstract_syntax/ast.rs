use std::u64;
use std::f64;
use std::str::FromStr;
use std::convert::TryFrom;

use nom::{IResult, ErrorKind};
use nom_locate::LocatedSpan;

use super::Position;

type Span<'a> = LocatedSpan<&'a str>;

pub trait Pos {
    /// Get the position of this value in the source.
    fn pos(&self) -> Position;
}

#[derive(Debug, PartialEq, Eq)]
pub struct Attributes(Vec<Attribute>, Position);

impl Pos for Attributes {
    fn pos(&self) -> Position {
        self.1
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Attribute(MetaItem, Position);

impl Pos for Attribute {
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
pub struct IndexLiteral(pub u64, pub Position);

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
    Product(TypeList, Position),
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
            &Type::Product(_, pos) => pos,
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
pub enum IntSuffix {
    U8,
    U16,
    U32,
    U64,
    USize,
    I8,
    I16,
    I32,
    I64,
    ISize,
}

#[derive(Debug, PartialEq, Eq)]
pub struct IntLiteral(pub u64, Option<IntSuffix>, pub Position);

impl Pos for IntLiteral {
    fn pos(&self) -> Position {
        self.2
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum FloatSuffix {
    F32,
    F64,
}

#[derive(Debug, PartialEq)]
pub struct FloatLiteral(pub f64, Option<FloatSuffix>, pub Position);

impl Eq for FloatLiteral {}

impl Pos for FloatLiteral {
    fn pos(&self) -> Position {
        self.2
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
    GT,
    GET,
    LT,
    LET,
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
    Magic(Position),
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
pub enum MacroDef {
    Id(Identifier),
}

impl Pos for MacroDef {
    fn pos(&self) -> Position {
        match self {
            &MacroDef::Id(ref inner) => inner.pos(),
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
pub enum Item {
    Use(bool, UseStart, UseTree, Position),
    Mod(bool, SimpleIdentifier, Box<Module>, Position),
    TypeDef(bool, SimpleIdentifier, TypeDef, Position),
    Macro(bool, SimpleIdentifier, MacroDef, Position),
    Let(bool, Pattern, Expression, Position),
    Ffi(SimpleIdentifier, FfiBlock, Position),
}

impl Pos for Item {
    fn pos(&self) -> Position {
        match self {
            &Item::Use(_, _, _, pos) => pos,
            &Item::Mod(_, _, _, pos) => pos,
            &Item::TypeDef(_, _, _, pos) => pos,
            &Item::Macro(_, _, _, pos) => pos,
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

pub const ERR_SIMPLE_ID_ONLY_UNDERSCORE: u32 = 0;
pub const ERR_SIMPLE_ID_TOO_LONG: u32 = 1;
pub const ERR_SIMPLE_ID_KEYWORD: u32 = 2;
pub const ERR_INT_NOT_A_U64: u32 = 3;
pub const ERR_FLOAT_NOT_A_F64: u32 = 4;
pub const ERR_STRING_UNICODE_ESCAPE_TOO_LONG: u32 = 5;
pub const ERR_STRING_UNICODE_ESCAPE_INVALID: u32 = 6;
pub const ERR_MACRO_INVALID_CHAR: u32 = 7;
pub const ERR_ID_EMPTY: u32 = 8;

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

macro_rules! list (
    ($i:expr, $submac:ident!( $($args:tt)* )) => (
        separated_list!($i, do_parse!(p_skip0 >> p_comma >> (())), $submac!($($args)*));
    );
    ($i:expr, $f:expr) => (
        list!($i, call!($f));
    );
);

macro_rules! would_match (
    ($i:expr, $submac:ident!( $($args:tt)* )) => (
        do_parse!($i, opt: opt!($submac!($($args)*)) >> (opt.is_some()));
    );
    ($i:expr, $f:expr) => (
        would_match!($i, call!($f));
    );
);

macro_rules! opt_attrs (
    ($i:expr, $submac:ident!( $($args:tt)* )) => (
        alt!($i,
            do_parse!(
                attrs: p_attributes >>
                p_lbrace >>
                inner: $submac!($($args)*) >>
                p_rbrace >>
                (attrs, inner)
            ) |
            do_parse!(
                start: position!() >>
                inner: $submac!($($args)*) >>
                (Attributes(vec![], Position::new(start, start)), inner)
            )
        )
    );
    ($i:expr, $f:expr) => (
        opt_attrs!($i, call!($f));
    );
);

macro_rules! opt_attrs_flat (
    ($i:expr, $submac:ident!( $($args:tt)* )) => (
        alt!($i,
            do_parse!(
                attrs: p_attributes >>
                p_lbrace >>
                inner: $submac!($($args)*) >>
                p_rbrace >>
                (attrs, inner.0, inner.1)
            ) |
            do_parse!(
                start: position!() >>
                inner: $submac!($($args)*) >>
                (Attributes(vec![], Position::new(start, start)), inner.0, inner.1)
            )
        )
    );
    ($i:expr, $f:expr) => (
        opt_attrs_flat!($i, call!($f));
    );
);

///////////////////
// Begin Tokens  //
///////////////////

named!(pub p_eq<Span, ()>, do_parse!(tag!("=") >> p_skip0 >> (())));
named!(pub p_lparen<Span, ()>, do_parse!(tag!("(") >> p_skip0 >> (())));
named!(pub p_rparen<Span, ()>, do_parse!(tag!(")") >> p_skip0 >> (())));
named!(pub p_lbracket<Span, ()>, do_parse!(tag!("[") >> p_skip0 >> (())));
named!(pub p_rbracket<Span, ()>, do_parse!(tag!("]") >> p_skip0 >> (())));
named!(pub p_lbrace<Span, ()>, do_parse!(tag!("{") >> p_skip0 >> (())));
named!(pub p_rbrace<Span, ()>, do_parse!(tag!("}") >> p_skip0 >> (())));
named!(pub p_langle<Span, ()>, do_parse!(tag!("<") >> p_skip0 >> (())));
named!(pub p_rangle<Span, ()>, do_parse!(tag!(">") >> p_skip0 >> (())));
named!(pub p_comma<Span, ()>, do_parse!(tag!(",") >> p_skip0 >> (())));
named!(pub p_dollar<Span, ()>, do_parse!(tag!("$") >> p_skip0 >> (())));
named!(pub p_colon<Span, ()>, do_parse!(tag!(":") >> p_skip0 >> (())));
named!(pub p_hash<Span, ()>, do_parse!(tag!("#") >> p_skip0 >> (())));
named!(pub p_at<Span, ()>, do_parse!(tag!("@") >> p_skip0 >> (())));
named!(pub p_tilde<Span, ()>, do_parse!(tag!("~") >> p_skip0 >> (())));
named!(pub p_semi<Span, ()>, do_parse!(tag!(";") >> p_skip0 >> (())));
named!(pub p_scope_separator<Span, ()>, do_parse!(tag!("::") >> p_skip0 >> (())));
named!(pub p_arrow<Span, ()>, do_parse!(tag!("->") >> p_skip0 >> (())));

named!(pub p_start_attribute<Span, ()>, do_parse!(p_hash >> p_lbracket >> (())));

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
        IResult::Error(error_code!(ErrorKind::Custom(ERR_SIMPLE_ID_ONLY_UNDERSCORE)))
    } else if simple_id.0.len() > 127 {
        IResult::Error(error_code!(ErrorKind::Custom(ERR_SIMPLE_ID_TOO_LONG)))
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
        IResult::Error(error_code!(ErrorKind::Custom(ERR_SIMPLE_ID_KEYWORD)))
    } else {
        IResult::Done(input, simple_id)
    }
}

fn p_dec_int(input: Span) -> IResult<Span, u64> {
    let (input, parsed) = try_parse!(input, is_a!("_0123456789"));

    let mut string = parsed.to_string();
    unsafe {
        string.as_mut_vec().retain(|byte| *byte != 95u8);
    }

    match u64::from_str_radix(&string, 10) {
        Ok(int) => IResult::Done(input, int),
        Err(_) => IResult::Error(error_code!(ErrorKind::Custom(ERR_INT_NOT_A_U64))),
    }
}

fn p_bin_int(input: Span) -> IResult<Span, u64> {
    let (input, _) = try_parse!(input, tag!("0b"));
    let (input, parsed) = try_parse!(input, is_a!("_01"));

    let mut string = parsed.to_string();
    unsafe {
        string.as_mut_vec().retain(|byte| *byte != 95u8);
    }

    match u64::from_str_radix(&string, 2) {
        Ok(int) => IResult::Done(input, int),
        Err(_) => IResult::Error(error_code!(ErrorKind::Custom(ERR_INT_NOT_A_U64))),
    }
}

fn p_hex_int(input: Span) -> IResult<Span, u64> {
    let (input, _) = try_parse!(input, tag!("0x"));
    let (input, parsed) = try_parse!(input, is_a!("_0123456789ABCDEF"));

    let mut string = parsed.to_string();
    unsafe {
        string.as_mut_vec().retain(|byte| *byte != 95u8);
    }

    match u64::from_str_radix(&string, 16) {
        Ok(int) => IResult::Done(input, int),
        Err(_) => IResult::Error(error_code!(ErrorKind::Custom(ERR_INT_NOT_A_U64))),
    }
}

named!(p_int_suffix<Span, IntSuffix>, alt!(
    do_parse!(
        tag!("U") >>
        ret: alt!(
            value!(IntSuffix::U8, tag!("8")) |
            value!(IntSuffix::U16, tag!("16")) |
            value!(IntSuffix::U32, tag!("32")) |
            value!(IntSuffix::U64, tag!("64")) |
            value!(IntSuffix::USize, tag!("Size"))
        ) >>
        (ret)
    ) |
    do_parse!(
        tag!("I") >>
        ret: alt!(
            value!(IntSuffix::I8, tag!("8")) |
            value!(IntSuffix::I16, tag!("16")) |
            value!(IntSuffix::I32, tag!("32")) |
            value!(IntSuffix::I64, tag!("64")) |
            value!(IntSuffix::ISize, tag!("Size"))
        ) >>
        (ret)
    )
));

named!(p_int_literal<Span, IntLiteral>, do_parse!(
    start: position!() >>
    int: alt!(p_bin_int | p_hex_int | p_dec_int) >>
    suffix: opt!(p_int_suffix) >>
    end: position!() >>
    p_skip0 >>
    (IntLiteral(int, suffix, Position::new(start, end)))
));

fn p_float_without_suffix(input: Span) -> IResult<Span, f64> {
    let (input, pre_dot) = try_parse!(input, is_a!("_0123456789"));
    let (input, _) = try_parse!(input, tag!("."));
    let (input, post_dot) = try_parse!(input, is_a!("_0123456789"));

    let (input, exponent) = try_parse!(input,
                                       opt!(map!(do_parse!(
        tag!("e") >>
        sign: opt!(alt!(tag!("+") | tag!("-"))) >>
        data: is_a!("_0123456789")
        >> (sign, data)
    ),
                                                 |(sign, data)| {
        let sign = sign.map_or("".to_string(), |span| span.fragment.to_string());
        let mut string = String::with_capacity(sign.len() + data.fragment.len() + 1);
        string.push_str("e");
        string.push_str(&sign);
        string.push_str(data.fragment);
        string
    })));
    let exponent = exponent.unwrap_or("".to_string());

    let mut string = String::with_capacity(pre_dot.fragment.len() + post_dot.fragment.len() +
                                           exponent.len());
    string.push_str(pre_dot.fragment);
    string.push_str(post_dot.fragment);
    string.push_str(&exponent);
    unsafe {
        string.as_mut_vec().retain(|byte| *byte != 95u8);
    }

    match f64::from_str(&string) {
        Ok(float) => IResult::Done(input, float),
        Err(_) => IResult::Error(error_code!(ErrorKind::Custom(ERR_FLOAT_NOT_A_F64))),
    }
}

named!(p_float_suffix<Span, FloatSuffix>, alt!(
    value!(FloatSuffix::F32, tag!("F32")) |
    value!(FloatSuffix::F64, tag!("F64"))
));

named!(p_float_literal<Span, FloatLiteral>, do_parse!(
    start: position!() >>
    float: p_float_without_suffix >>
    suffix: opt!(p_float_suffix) >>
    end: position!() >>
    p_skip0 >>
    (FloatLiteral(float, suffix, Position::new(start, end)))
));

named!(p_x_escape<Span, String>, map!(do_parse!(
    tag!("\\x") >>
    first: one_of!("01234567") >>
    second: one_of!("0123456789ABCDEF") >>
    ((first, second))
), |(first, second)| {
    let mut string = String::with_capacity(2);
    string.push(first);
    string.push(second);
    char::from(u8::from_str_radix(&string, 16).unwrap()).to_string()
}));

fn _p_u_escape(input: Span) -> IResult<Span, String> {
    let (input, hex_digits) = try_parse!(input, is_a!("0123456789ABCDEF"));

    if hex_digits.fragment.len() > 6 {
        IResult::Error(error_code!(ErrorKind::Custom(ERR_STRING_UNICODE_ESCAPE_TOO_LONG)))
    } else {
        match char::try_from(u32::from_str_radix(hex_digits.fragment, 16).unwrap()) {
            Ok(chr) => IResult::Done(input, chr.to_string()),
            Err(_) => {
                IResult::Error(error_code!(ErrorKind::Custom(ERR_STRING_UNICODE_ESCAPE_INVALID)))
            }
        }
    }
}

named!(p_u_escape<Span, String>, do_parse!(
    tag!("\\u{") >>
    escaped: _p_u_escape >>
    tag!("}") >>
    (escaped)
));

named!(p_string_inner<Span, String>, map!(many0!(alt!(
    map!(is_not!(r#"\""#), |span| span.fragment.to_string()) |
    value!("\0".to_string(), tag!("\\0")) |
    value!("\t".to_string(), tag!("\\t")) |
    value!("\n".to_string(), tag!("\\n")) |
    value!("\\".to_string(), tag!("\\\\")) |
    value!("\"".to_string(), tag!("\\\"")) |
    p_x_escape |
    p_u_escape
)), |strings| {
    let mut ret = String::new();
    for string in strings {
        ret.push_str(&string);
    }
    ret
}));

named!(p_string_literal<Span, StringLiteral>, do_parse!(
    start: position!() >>
    tag!("\"") >>
    string: p_string_inner >>
    tag!("\"") >>
    end: position!() >>
    p_skip0 >>
    (StringLiteral(string, Position::new(start, end)))
));

///////////////////
//   End Tokens  //
///////////////////

pub fn p_id(input: Span) -> IResult<Span, Identifier> {
    let (input, ids) = try_parse!(input, separated_list!(p_scope_separator, p_simple_id));

    if ids.len() > 0 {
        let pos = Position::from_positions(ids.first().unwrap().1, ids.last().unwrap().1);
        IResult::Done(input, Identifier(ids, pos))
    } else {
        return IResult::Error(error_code!(ErrorKind::Custom(ERR_ID_EMPTY)));
    }
}

named!(pub p_literal<Span, Literal>, alt!(
    map!(p_float_literal, Literal::Float) |
    map!(p_int_literal, Literal::Int) |
    map!(p_string_literal, Literal::String)
));

named!(pub p_meta_item_nullary<Span, MetaItem>, map!(p_simple_id, MetaItem::Nullary));

named!(pub p_meta_item_pair<Span, MetaItem>, map!(do_parse!(
    id: p_simple_id >>
    p_eq >>
    lit: p_literal >>
    ((id, lit))), |(id, lit)| {
        let pos = Position::from_positions(id.pos(), lit.pos());
        MetaItem::Pair(id, lit, pos)
    }));

named!(pub p_meta_item_lit_arg<Span, MetaItem>, do_parse!(
    start: position!() >>
    id: p_simple_id >>
    p_lparen >>
    lit: p_literal >>
    p_rparen >>
    end: position!() >>
    (MetaItem::LitArg(id, lit, Position::new(start, end)))
));

named!(pub p_meta_item_args<Span, MetaItem>, do_parse!(
    start: position!() >>
    id: p_simple_id >>
    p_lparen >>
    inner: list!(p_meta_item) >>
    p_rparen >>
    end: position!() >>
    (MetaItem::Args(id, inner, Position::new(start, end)))
));

named!(pub p_meta_item<Span, MetaItem>, alt!(
    p_meta_item_lit_arg |
    p_meta_item_args |
    p_meta_item_pair |
    p_meta_item_nullary
));

named!(pub p_attribute<Span, Attribute>, do_parse!(
    start: position!() >>
    p_start_attribute >>
    meta: p_meta_item >>
    p_rbracket >>
    end: position!() >>
    (Attribute(meta, Position::new(start, end)))
));

named!(pub p_attributes<Span, Attributes>, map!(
    many1!(p_attribute), |attrs| {
        let len = attrs.len();
        let start_pos = attrs.get(0).unwrap().pos();
        let end_pos = attrs.get(len - 1).unwrap().pos();
        Attributes(attrs, Position::from_positions(start_pos, end_pos))
    }
));

fn p_macro_inv_args(mut input: Span) -> IResult<Span, String> {
    let mut paren_count = 1;
    let mut args = String::new();

    loop {
        let (remaining, took) = try_parse!(input, take!(1));
        input = remaining;
        let chr = char::from_str(took.fragment).unwrap();

        if !(chr.is_ascii_graphic() || chr == ' ' || chr == '\n') {
            return IResult::Error(error_code!(ErrorKind::Custom(ERR_MACRO_INVALID_CHAR)));
        }

        if chr == ')' {
            paren_count -= 1;
        }

        if paren_count == 0 {
            return IResult::Done(input, args);
        } else {
            if chr == '(' {
                paren_count += 1;
            }
            args.push(chr)
        }
    }
}

named!(pub p_macro_invocation<Span, MacroInvocation>, do_parse!(
    start: position!() >>
    p_dollar >>
    id: p_id >>
    p_lparen >>
    args: p_macro_inv_args >>
    end: position!() >>
    p_skip0 >>
    (MacroInvocation(id, args, Position::new(start, end)))
));

named!(pub p_index_literal<Span, IndexLiteral>, do_parse!(
    start: position!() >>
    int_str: is_a!("0123456789") >>
    end: position!() >>
    p_skip0 >>
    (IndexLiteral(u64::from_str_radix(int_str.fragment, 10).unwrap(), Position::new(start, end)))
));

named!(pub p_index<Span, Index>, alt!(
    map!(p_index_literal, Index::Literal) |
    map!(p_macro_invocation, Index::Macro)
));

named!(p_type_list<Span, TypeList>, do_parse!(
    start: position!() >>
    p_lparen >>
    is_named: would_match!(opt_attrs!(do_parse!(p_simple_id >> p_colon >> p_type >> (())))) >>
    ret: alt!(
        cond_reduce!(is_named, do_parse!(
            types: list!(opt_attrs_flat!(do_parse!(
                id: p_simple_id >>
                p_colon >>
                the_type: p_type >>
                (id, the_type)
            ))) >>
            p_rparen >>
            end: position!() >>
            (TypeList::Named(types, Position::new(start, end)))
        )) |
        do_parse!(
            types: list!(p_type) >>
            p_rparen >>
            end: position!() >>
            (TypeList::Anon(types, Position::new(start, end)))
        )
    ) >>
    (ret)
));

named!(p_type_application_list<Span, TypeApplicationList>, do_parse!(
    start: position!() >>
    p_langle >>
    is_named: would_match!(opt_attrs!(do_parse!(p_simple_id >> p_eq >> p_type >> (())))) >>
    ret: alt!(
        cond_reduce!(is_named, do_parse!(
            types: list!(opt_attrs_flat!(do_parse!(
                id: p_simple_id >>
                p_eq >>
                the_type: p_type >>
                (id, the_type)
            ))) >>
            p_rangle >>
            end: position!() >>
            (TypeApplicationList::Named(types, Position::new(start, end)))
        )) |
        do_parse!(
            types: list!(p_type) >>
            p_rangle >>
            end: position!() >>
            (TypeApplicationList::Anon(types, Position::new(start, end)))
        )
    ) >>
    (ret)
));

named!(pub p_ptr<Span, Type>, do_parse!(
    start: position!() >>
    p_at >>
    inner: p_type >>
    end: position!() >>
    (Type::Ptr(Box::new(inner), Position::new(start, end)))
));

named!(pub p_ptr_mut<Span, Type>, do_parse!(
    start: position!() >>
    p_tilde >>
    inner: p_type >>
    end: position!() >>
    (Type::PtrMut(Box::new(inner), Position::new(start, end)))
));

named!(pub p_array<Span, Type>, do_parse!(
    start: position!() >>
    p_lbracket >>
    inner: p_type >>
    p_rbracket >>
    end: position!() >>
    (Type::Array(Box::new(inner), Position::new(start, end)))
));

named!(pub p_type_macro_invocation<Span, Type>, map!(p_macro_invocation, Type::MacroInv));

named!(pub p_type_attributed<Span, Type>, do_parse!(
    start: position!() >>
    stuff: opt_attrs!(p_nonattributed_type) >>
    end: position!() >>
    (Type::Attributed(stuff.0, Box::new(stuff.1), Position::new(start, end)))
));

named!(pub p_product_repeated<Span, Type>, do_parse!(
    start: position!() >>
    p_lparen >>
    inner: p_type >>
    p_semi >>
    index: p_index >>
    p_rparen >>
    end: position!() >>
    (Type::ProductRepeated(Box::new(inner), index, Position::new(start, end)))
));

named!(pub p_type_fun<Span, Type>, do_parse!(
    start: position!() >>
    args: p_type_list >>
    p_arrow >>
    return_type: p_type >>
    end: position!() >>
    (Type::Fun(args, Box::new(return_type), Position::new(start, end)))
));

named!(pub p_type_product<Span, Type>, do_parse!(
    start: position!() >>
    types: p_type_list >>
    end: position!() >>
    (Type::Product(types, Position::new(start, end)))
));

named!(pub p_type_type_application<Span, Type>, do_parse!(
    start: position!() >>
    id: p_id >>
    p_langle >>
    args: p_type_application_list >>
    p_rangle >>
    end: position!() >>
    (Type::TypeApplication(id, args, Position::new(start, end)))
));

named!(pub p_nonattributed_type<Span, Type>, alt!(
    p_ptr | p_ptr_mut | p_array | p_type_macro_invocation | p_product_repeated |
    p_type_fun | p_type_product | p_type_type_application | map!(p_id, Type::Id)
));

named!(pub p_type<Span, Type>, alt!(
    p_nonattributed_type | p_type_attributed
));

// #[test]
// fn test_skip0() {
//     works!(p_skip0, "", 0);
//     works!(p_skip0, "a", 1);
//     works!(p_skip0, " ", 0);
//     works!(p_skip0, "   ", 0);
//     works!(p_skip0, "\n", 0);
//     works!(p_skip0, "   \n  \n\n  ", 0);
//
//     not_complete!(p_skip0, "\r");
//     not_complete!(p_skip0, "\t");
//
//     not_complete!(p_skip0, "//");
//     not_complete!(p_skip0, "// ");
//
//     works!(p_skip0, "//\n", 0);
//     works!(p_skip0, "// \n", 0);
//     works!(p_skip0, "///\n", 0);
//     works!(p_skip0, "////\n", 0);
//     works!(p_skip0, "//\n//\n", 0);
//     works!(p_skip0, "//\na", 1);
//     works!(p_skip0, "// \rö\n   \n    /// /\n  a", 1);
// }
//
// #[test]
// fn test_simple_id() {
//     works!(p_simple_id, "_a", 0);
//     works!(p_simple_id, "_a   ", 0);
//     works!(p_simple_id, "a", 0);
//     works!(p_simple_id, "A", 0);
//     works!(p_simple_id, "aA", 0);
//     works!(p_simple_id, "__", 0);
//     works!(p_simple_id, "_9", 0);
//     works!(p_simple_id, "a9", 0);
//     works!(p_simple_id, "a_9", 0);
//     works!(p_simple_id, "_aöa", 3);
//     works!(p_simple_id,
//            "abcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefg",
//            0); // 127 characters
//
//     fails!(p_simple_id,
//            "abcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefgh"); // 128 characters
//     fails!(p_simple_id, "ö");
//     fails!(p_simple_id, "_");
//     fails!(p_simple_id, "-");
//     fails!(p_simple_id, "9");
//     fails!(p_simple_id, "9a");
//     fails!(p_simple_id, "-a");
//     fails!(p_simple_id, "");
//
//     fails!(p_simple_id, "pub");
//     works!(p_simple_id, "pubb", 0);
//     fails!(p_simple_id, "mod");
//     fails!(p_simple_id, "use");
//     fails!(p_simple_id, "self");
//     fails!(p_simple_id, "extern");
//     fails!(p_simple_id, "goto");
//     fails!(p_simple_id, "label");
//     fails!(p_simple_id, "break");
//     fails!(p_simple_id, "return");
//     fails!(p_simple_id, "while");
//     fails!(p_simple_id, "match");
//     fails!(p_simple_id, "if");
//     fails!(p_simple_id, "then");
//     fails!(p_simple_id, "else");
//     fails!(p_simple_id, "let");
//     fails!(p_simple_id, "as");
//     fails!(p_simple_id, "type");
//     fails!(p_simple_id, "macro");
//     fails!(p_simple_id, "magic");
//     fails!(p_simple_id, "attribute");
//     fails!(p_simple_id, "mut");
// }
//
// #[test]
// fn test_id() {
//     works!(p_id, "aö", 2);
//     works!(p_id, "a::_a::__::t5ö", 2);
//     works!(p_id, "a  ::  _a::__    ::  t5  ö", 2);
//     fails!(p_id, "");
// }
//
// #[cfg(test)]
// macro_rules! test_int_lit {
//     ($input:expr, $exp:expr) => {
//         {
//             match p_literal(Span::new($input)).unwrap() {
//                 (_, Literal::Int(lit)) => {
//                     assert_eq!(lit.0, $exp);
//                     assert!(lit.1.is_none());
//                 }
//                 _ => panic!("Did not parse an integer literal"),
//             }
//         }
//     }
// }
//
// #[cfg(test)]
// macro_rules! test_float_lit {
//     ($input:expr, $exp:expr) => {
//         {
//             match p_literal(Span::new($input)).unwrap() {
//                 (_, Literal::Float(lit)) => {
//                     assert_eq!(lit.0, $exp);
//                     assert!(lit.1.is_none());
//                 }
//                 _ => panic!("Did not parse a float literal"),
//             }
//         }
//     }
// }
//
// #[cfg(test)]
// macro_rules! test_string_lit {
//     ($input:expr, $exp:expr) => {
//         {
//             match p_literal(Span::new($input)).unwrap() {
//                 (_, Literal::String(lit)) => {
//                     assert_eq!(lit.0, $exp);
//                 }
//                 _ => panic!("Did not parse a string literal"),
//             }
//         }
//     }
// }
//
// #[test]
// fn test_literal() {
//     test_int_lit!("0ö", 0);
//     test_int_lit!("_0 ", 0);
//     test_int_lit!("0_ ", 0);
//     test_int_lit!("012345 ", 12345);
//     test_int_lit!("__01____23_45__ ", 12345);
//     test_int_lit!("0b__001_01_ ", 0b__001_01_);
//     test_int_lit!("0x123_ABF ", 0x123_ABF);
//     works_check!(p_literal, "0U8 ", 0, Literal::Int(_));
//     works_check!(p_literal, "0U16 ", 0, Literal::Int(_));
//     works_check!(p_literal, "0U32 ", 0, Literal::Int(_));
//     works_check!(p_literal, "0U64 ", 0, Literal::Int(_));
//     works_check!(p_literal, "0USize ", 0, Literal::Int(_));
//     works_check!(p_literal, "0x123I8 ", 0, Literal::Int(_));
//     works_check!(p_literal, "0b01101_0110__1I16 ", 0, Literal::Int(_));
//     works_check!(p_literal, "0I32 ", 0, Literal::Int(_));
//     works_check!(p_literal, "0I64 ", 0, Literal::Int(_));
//     works_check!(p_literal, "0ISize ", 0, Literal::Int(_));
//
//     fails!(p_literal, "-5 ");
//     fails!(p_literal, "_ ");
//     fails!(p_literal, "__ ");
//     not_complete!(p_literal, "0b2 ");
//     not_complete!(p_literal, "0xG ");
//     not_complete!(p_literal, "0xf ");
//     not_complete!(p_literal, "0F32 ");
//
//     test_float_lit!("0.0ö", 0.0);
//     test_float_lit!("_0.0 ", 0.0);
//     test_float_lit!("0_.0 ", 0_.0);
//     test_float_lit!("0._0 ", 0.0);
//     test_float_lit!("0.0_ ", 0.0_);
//     test_float_lit!("0.0e42 ", 0.0e42);
//     test_float_lit!("0.0e4_2 ", 0.0e4_2);
//     test_float_lit!("0.0e+42 ", 0.0e+42);
//     test_float_lit!("0.0e-42 ", 0.0e-42);
//     test_float_lit!("00___0.0_00_0e-42 ", 00___0.0_00_0e-42);
//     test_float_lit!("0._ ", 0.0);
//     test_float_lit!("_.0 ", 0.0);
//     test_float_lit!("0._e42 ", 0.0e42);
//
//     works_check!(p_literal, "0.0F32 ", 0, Literal::Float(_));
//     works_check!(p_literal, "0.0F64 ", 0, Literal::Float(_));
//     works_check!(p_literal, "0_00.00_0F64 ", 0, Literal::Float(_));
//     works_check!(p_literal, "0.0e+42F32 ", 0, Literal::Float(_));
//     works_check!(p_literal, "0.0e+42F64 ", 0, Literal::Float(_));
//
//     not_complete!(p_literal, "0. ");
//     fails!(p_literal, ".0 ");
//     not_complete!(p_literal, "0.0U32 ");
//     fails!(p_literal, "-0.5 ");
//     not_complete!(p_literal, "0.0e_ ");
//     not_complete!(p_literal, "0e42 ");
//
//     test_string_lit!(r#""""#, "");
//     test_string_lit!(r#""a""#, "a");
//     test_string_lit!(r#""ö""#, "ö");
//     test_string_lit!(r#""🦄""#, "🦄");
//     test_string_lit!(r#""💂🏾""#, "💂🏾");
//     test_string_lit!(r#""abc""#, "abc");
//     test_string_lit!(r#""\"""#, "\"");
//     test_string_lit!(r#""\\""#, "\\");
//     test_string_lit!(r#""\n""#, "\n");
//     test_string_lit!(r#""\t""#, "\t");
//     test_string_lit!(r#""\0""#, "\0");
//     test_string_lit!(r#""'""#, "'");
//     test_string_lit!(r#""\x0F""#, "\x0F");
//     test_string_lit!(r#""\u{0}""#, "\u{0}");
//     test_string_lit!(r#""\u{A}""#, "\u{A}");
//     test_string_lit!(r#""\u{012345}""#, "\u{012345}");
//     test_string_lit!(r#""\x7AA""#, "\x7AA");
//
//     fails!(p_literal, r#"""#);
//     fails!(p_literal, r#""\ö""#);
//     fails!(p_literal, r#""\x""#);
//     fails!(p_literal, r#""\xA""#);
//     fails!(p_literal, r#""\xaa""#);
//     fails!(p_literal, r#""\x80""#);
//     fails!(p_literal, r#""\xG4""#);
//     fails!(p_literal, r#""\x4G""#);
//     fails!(p_literal, r#""\u""#);
//     fails!(p_literal, r#""\u1234""#);
//     fails!(p_literal, r#""\u{}""#);
//     fails!(p_literal, r#""\u{""#);
//     fails!(p_literal, r#""\u{0123456}""#);
//     fails!(p_literal, r#""\u{a}""#);
//     not_complete!(p_literal, r#"""""#);
// }
//
// #[test]
// fn test_meta_item() {
//     works_check!(p_meta_item, "aö", 2, MetaItem::Nullary(_));
//     works_check!(p_meta_item, "a = 42.0F32", 0, MetaItem::Pair(_, _, _));
//     works_check!(p_meta_item, "a(42.0F32)", 0, MetaItem::LitArg(_, _, _));
//     works_check!(p_meta_item, "a(b = 42 , c(d = \"\\\\\"))", 0, MetaItem::Args(_, _, _));
// }
//
// #[test]
// fn test_attributes() {
//     works!(p_attributes, "#[a]#[a(b = 42 , c(d = \"\\\\\"))]", 0);
//     fails!(p_attributes, "#[a::b]");
// }
//
// #[test]
// fn test_macro_invocation() {
//     works!(p_macro_invocation, "$a()", 0);
//     works!(p_macro_invocation, "$a(())", 0);
//     works!(p_macro_invocation, "$a::b(a)", 0);
//     works!(p_macro_invocation, "$a(j(f   e)wjf8--fhewf[{)", 0);
//
//     fails!(p_macro_invocation, "$a(ö");
//     fails!(p_macro_invocation, "$a(()");
//     not_complete!(p_macro_invocation, "$a())");
// }
//
// #[test]
// fn test_index() {
//     works_check!(p_index, "0404", 0, Index::Literal(_));
//     works_check!(p_index, "0404   ", 0, Index::Literal(_));
//     works_check!(p_index, "$a()", 0, Index::Macro(_));
//     works_check!(p_index, "$a()   ", 0, Index::Macro(_));
// }
//
// #[test]
// fn test_type() {
//     // works!(p_type_list, "(#[foo]{a: r})", 0);
//     //
//     // works_check!(p_type, "@r ö", 2, Type::Ptr(_, _));
//     // works_check!(p_type, "@ ( r  ) ö", 2, Type::Ptr(_, _));
//     //
//     // works_check!(p_type, "~(r, b) ö", 2, Type::PtrMut(_, _));
//     // works_check!(p_type, "~ r ö", 2, Type::PtrMut(_, _));
//     //
//     // works_check!(p_type, "[r]", 0, Type::Array(_, _));
//     // works_check!(p_type, "[ (r)]", 0, Type::Array(_, _));
//     // works_check!(p_type, "[r ]", 0, Type::Array(_, _));
//     //
//     // works_check!(p_type, "#[foo] { r }", 0, Type::Attributed(_, _, _));
//     // works_check!(p_type, "#[foo]{ r }", 0, Type::Attributed(_, _, _));
//     // works_check!(p_type, "#[foo]  { r }", 0, Type::Attributed(_, _, _));
//     // works_check!(p_type, "#[foo] {r }", 0, Type::Attributed(_, _, _));
//     // works_check!(p_type, "#[foo] { r}", 0, Type::Attributed(_, _, _));
//     // works_check!(p_type, "#[foo] #[bar] { r }", 0, Type::Attributed(_, _, _));
//     //
//     // works_check!(p_type, "(r; 42)", 0, Type::ProductRepeated(_, _, _));
//     // works_check!(p_type, "( r; 42)", 0, Type::ProductRepeated(_, _, _));
//     // works_check!(p_type, "((r) ; 42)", 0, Type::ProductRepeated(_, _, _));
//     // works_check!(p_type, "(r;42)", 0, Type::ProductRepeated(_, _, _));
//     // works_check!(p_type, "(r;  42)", 0, Type::ProductRepeated(_, _, _));
//     // works_check!(p_type, "(r; 42 )", 0, Type::ProductRepeated(_, _, _));
//     // works_check!(p_type, "(r; $a())", 0, Type::ProductRepeated(_, _, _));
//     // fails!(p_type, "(r; 0b11)");
//     //
//     // works_check!(p_type, "$a()", 0, Type::MacroInv(_));
//     //
//     // works_check!(p_type, "()ö", 2, Type::Product(_, _));
//     // works_check!(p_type, "( )ö", 2, Type::Product(_, _));
//     // works_check!(p_type, "(r)ö", 2, Type::Product(_, _));
//     // works_check!(p_type, "(#[foo]{r})ö", 2, Type::Product(_, _));
//     // works_check!(p_type, "(r, r)ö", 2, Type::Product(_, _));
//     // works_check!(p_type, "(#[foo]{r} , r)ö", 2, Type::Product(_, _));
//     // works_check!(p_type, "(  r,  (r)  )ö", 2, Type::Product(_, _));
//     // works_check!(p_type, "(r,r)ö", 2, Type::Product(_, _));
//     // works_check!(p_type, "(r ,r)ö", 2, Type::Product(_, _));
//     //
//     // works_check!(p_type, "(a: @r)ö", 2, Type::Product(_, _));
//     // works_check!(p_type, "(#[foo]{a: r})ö", 2, Type::Product(_, _));
//     works_check!(p_type, "(a: r, a: r)ö", 2, Type::Product(_, _));
//     works_check!(p_type, "(a: r,#[foo] {a: r  }  )ö", 2, Type::Product(_, _));
//     works_check!(p_type, "( a: r,  A:  r )ö", 2, Type::Product(_, _));
//     works_check!(p_type, "(a : (r))ö", 2, Type::Product(_, _));
//     works_check!(p_type, "(a :r)ö", 2, Type::Product(_, _));
//     works_check!(p_type, "(a: r , b: r)ö", 2, Type::Product(_, _));
//     fails!(p_type, "(a: r,)");
//
//     works_check!(p_type, "() -> ()", 0, Type::Fun(_, _, _)); // TODO ö?
//     works_check!(p_type, "() ->  r", 0, Type::Fun(_, _, _));
//     works_check!(p_type, "() ->  #[foo]{r}", 0, Type::Fun(_, _, _));
//     works_check!(p_type, "( ) -> r", 0, Type::Fun(_, _, _));
//     works_check!(p_type, "(r) -> r", 0, Type::Fun(_, _, _));
//     works_check!(p_type, "(#[foo]{r}) -> r", 0, Type::Fun(_, _, _));
//     works_check!(p_type, "(r, r) -> (r, r)", 0, Type::Fun(_, _, _));
//     works_check!(p_type, "(r, #[foo]{r}) -> (#[foo]{r}, r)", 0, Type::Fun(_, _, _));
//     works_check!(p_type, "(  r,  r  ) -> (r)", 0, Type::Fun(_, _, _));
//     works_check!(p_type, "(r,r) -> r", 0, Type::Fun(_, _, _));
//     works_check!(p_type, "(r ,r) -> r", 0, Type::Fun(_, _, _));
//     works_check!(p_type, "()-> r", 0, Type::Fun(_, _, _));
//     works_check!(p_type, "()  -> r", 0, Type::Fun(_, _, _));
//     not_complete!(p_type, "() - r");
//
//     works_check!(p_type, "(a: r) -> r", 0, Type::Fun(_, _, _));
//     works_check!(p_type, "(#[foo]{a: r}) -> r", 0, Type::Fun(_, _, _));
//     works_check!(p_type, "(a: r, b: r) -> (r, r)", 0, Type::Fun(_, _, _));
//     works_check!(p_type, "(a: r, #[foo]{b: r}) -> (r, r)", 0, Type::Fun(_, _, _));
//     works_check!(p_type, "(  a:   r,  b: r  ) -> r", 0, Type::Fun(_, _, _));
//     works_check!(p_type, "(a: r)-> (r)", 0, Type::Fun(_, _, _));
//     works_check!(p_type, "(a: r)  -> r", 0, Type::Fun(_, _, _));
//     not_complete!(p_type, "(a: r) - r");
//
//     works_check!(p_type, "a", 0, Type::Id(_));
//     works_check!(p_type, "a::b::c", 0, Type::Id(_));
//
//     works_check!(p_type, "a<b>", 0, Type::TypeApplication(_, _, _));
//     works_check!(p_type, "a<(b, c)>", 0, Type::TypeApplication(_, _, _));
//     works_check!(p_type, "a<#[foo]{b}>", 0, Type::TypeApplication(_, _, _));
//     works_check!(p_type, "a::b<c>", 0, Type::TypeApplication(_, _, _));
//     works_check!(p_type, "a<  @b  >", 0, Type::TypeApplication(_, _, _));
//     works_check!(p_type, "a<b, c>", 0, Type::TypeApplication(_, _, _));
//     works_check!(p_type, "a<#[foo]{b}, c>", 0, Type::TypeApplication(_, _, _));
//     works_check!(p_type, "a<  b,  c  >", 0, Type::TypeApplication(_, _, _));
//     works_check!(p_type, "a<a,b>", 0, Type::TypeApplication(_, _, _));
//     works_check!(p_type, "a<a ,b>", 0, Type::TypeApplication(_, _, _));
//     works_check!(p_type, "a  <  b  >", 0, Type::TypeApplication(_, _, _));
//     not_complete!(p_type, "a<>");
//     not_complete!(p_type, "a<   >");
//
//     works_check!(p_type, "a<b = y>", 0, Type::TypeApplication(_, _, _));
//     works_check!(p_type, "a<#[foo] {b = y}>", 0, Type::TypeApplication(_, _, _));
//     works_check!(p_type, "a::b<c = z>", 0, Type::TypeApplication(_, _, _));
//     works_check!(p_type, "a<  b   =  y  >", 0, Type::TypeApplication(_, _, _));
//     works_check!(p_type, "a<b = y, c = z>", 0, Type::TypeApplication(_, _, _));
//     works_check!(p_type, "a<b = y,#[foo]{ c = z}>", 0, Type::TypeApplication(_, _, _));
//     works_check!(p_type, "a<  b = y,  c = z  >", 0, Type::TypeApplication(_, _, _));
//     works_check!(p_type, "a<a= @x>", 0, Type::TypeApplication(_, _, _));
//     works_check!(p_type, "a<a =x>", 0, Type::TypeApplication(_, _, _));
//     works_check!(p_type, "a<a = x,b = y>", 0, Type::TypeApplication(_, _, _));
//     works_check!(p_type, "a<a = x , b = y>", 0, Type::TypeApplication(_, _, _));
// }

// TODO remove modules (use one file per module instead)
// TODO remove operators (use functions instead)
// TODO allow let expressions without a right side `let foo;`
