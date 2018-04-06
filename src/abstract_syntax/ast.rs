use super::Position;

#[derive(Debug, PartialEq, Eq)]
pub struct Attributes(Vec<MetaItem>, Position);

#[derive(Debug, PartialEq, Eq)]
pub enum MetaItem {
    Nullary(Identifier, Position),
    Pair(Identifier, Literal, Position),
    LitArg(Identifier, Literal, Position),
    Args(Identifier, Vec<MetaItem>, Position),
}

// Identifiers consists purely of ascii alphanumeric chars or underscores (_).
// The length of a simple identifier must be between 1 and 255 (inclusive).
// An identifier starting with an underscore must have a length of at least 2.

#[derive(Debug, PartialEq, Eq)]
pub struct SimpleIdentifier(pub String, pub Position);

#[derive(Debug, PartialEq, Eq)]
pub struct Identifier(Vec<SimpleIdentifier>, Position);
#[derive(Debug, PartialEq, Eq)]
pub struct IndexLiteral(pub String, pub Position);

#[derive(Debug, PartialEq, Eq)]
pub enum Index {
    Literal(IndexLiteral),
}

#[derive(Debug, PartialEq, Eq)]
// (A, @B) or (a: Foo, b: @Bar)
pub enum TypeList {
    Anon(Vec<Type>),
    Named(Vec<(Attributes, SimpleIdentifier, Type)>),
}

#[derive(Debug, PartialEq, Eq)]
// <A, @B> or <A = Foo, B = @Bar>
pub enum TypeApplicationList {
    Anon(Vec<Type>),
    Named(Vec<(Attributes, SimpleIdentifier, Type)>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Type {
    Attributed(Attributes, Box<Type>, Position),
    Id(Identifier, Position),
    MacroInv(Identifier, String, Position),
    Ptr(Box<Type>, Position),
    PtrMut(Box<Type>, Position),
    Array(Box<Type>, Position),
    ProductRepeated(Box<Type>, Index, Position),
    Product(TypeList, Position),
    Fun(TypeList, Box<Type>, Position),
    TypeApplicationAnon(Identifier, TypeApplicationList, Position),
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

#[derive(Debug, PartialEq, Eq)]
pub struct IntLiteral(String, Position);

#[derive(Debug, PartialEq, Eq)]
pub struct FloatLiteral(String, Position);

#[derive(Debug, PartialEq, Eq)]
pub struct StringLiteral(String, Position);

#[derive(Debug, PartialEq, Eq)]
pub enum Literal {
    Int(IntLiteral),
    Float(FloatLiteral),
    String(StringLiteral),
}

#[derive(Debug, PartialEq, Eq)]
// (a, @b) or (a = Foo, b = @bar)
pub enum PatternList {
    Anon(Vec<Pattern>),
    Named(Vec<(Attributes, SimpleIdentifier, Pattern)>),
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
    Product(PatternList, Position),
    Sum(Identifier, PatternList, Position), // list parens can be omitted in the syntax for unit sums: `| Foo`
    Literal(Literal),
}

#[derive(Debug, PartialEq, Eq)]
pub struct GuardedPattern(Pattern, Expression, Position);

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
    Anon(Vec<Expression>),
    Named(Vec<(Attributes, SimpleIdentifier, Expression)>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Expression {
    Literal(Literal),
    Attributed(Attributes, Box<Expression>, Position),
    Id(Identifier, Position),
    MacroInv(Identifier, String, Position),
    Block(Vec<Expression>, Position),
    Ref(Box<Expression>, Position),
    RefMut(Box<Expression>, Position),
    DeRef(Box<Expression>, Position),
    DeRefMut(Box<Expression>, Position),
    Array(Box<Expression>, Position),
    ArrayIndex(Box<Expression>, Box<Expression>, Position),
    ProductRepeated(Box<Expression>, Index, Position),
    Product(ExpressionList, Position),
    ProductAccessAnon(Box<Expression>, Index, Position),
    ProductAccessNamed(Box<Expression>, SimpleIdentifier),
    Sum(Identifier, ExpressionList),
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

#[derive(Debug, PartialEq, Eq)]
pub enum UseStart {
    Super(Position),
    Mod(Position),
    Extern(Position),
    Magic(Position), // really special-case this?
    Id(SimpleIdentifier),
}

#[derive(Debug, PartialEq, Eq)]
pub enum UseTree {
    Selff(Position),
    Leaf(SimpleIdentifier, Position),
    Inner(Vec<(SimpleIdentifier, UseTree)>, Position),
}

#[derive(Debug, PartialEq, Eq)]
pub struct FfiBlock(String, Vec<(Attributes, FfiItem)>, Position);

#[derive(Debug, PartialEq, Eq)]
pub enum FfiItem {
    Fun(SimpleIdentifier, TypeList, Box<Type>, Position),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Module(Vec<(Attributes, Item)>, Position);

#[derive(Debug, PartialEq, Eq)]
pub struct Magic(MetaItem, Position);

#[derive(Debug, PartialEq, Eq)]
pub enum MagicExpression {
    Magic(Magic),
    Expression(Expression),
}

#[derive(Debug, PartialEq, Eq)]
pub enum MagicTypeDef {
    Magic(Magic),
    TypeDef(TypeDef),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Item {
    Use(bool, UseStart, UseTree, Position),
    Mod(bool, SimpleIdentifier, Box<Module>, Position),
    TypeDef(bool, SimpleIdentifier, MagicTypeDef, Position),
    Macro(bool, SimpleIdentifier, Magic, Position),
    Attribute(bool, SimpleIdentifier, Magic, Position),
    Let(bool, Pattern, MagicExpression, Position),
    Ffi(bool, SimpleIdentifier, FfiBlock, Position),
}

#[derive(Debug, PartialEq, Eq)]
pub struct File(Vec<(Attributes, Item)>, Position);

// keywords: mod, use, self, super, extern, goto, label, break, return, while, match, if, then, else, let, as, type, macro, magic, attribute

// pub enum Token {
//
// }
//
// named!(pub p_token, tag!("TODO"));
