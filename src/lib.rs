#[macro_use]
extern crate nom;
#[macro_use(position)]
extern crate nom_locate;

pub mod abstract_syntax;

struct SimpleIdentifier(String); // XXX

enum Identifier {
    Simple(SimpleIdentifier), // XXX
    Qualified(Box<Identifier>), // XXX
}

// TODO modules

enum Attribute {
    SimpleAttribute, // #foo XXX
    ListAttribute, // #foo(bar, baz) XXX
    MapAttribute, // #foo(bar = baz) XXX
}

enum Macro {
    // Not designed yet, needs more research
}

enum InlineType {
    Id(Identifier), // XXX
    Void, // XXX
    Fun {
        args: Vec<InlineType>,
        ret: Box<InlineType>,
    }, // XXX
    Pointer {
        inner: Box<InlineType>,
        mutable: bool,
    }, // points to a single thing, can be dereferenced XXX
    ArrayType(Box<InlineType>), // zero or more of a type (has no static size) XXX
    ProductAnon(Vec<InlineType>), // XXX
    ProductNamed(Vec<(SimpleIdentifier, InlineType)>), // XXX
    ProductRepeated(Box<InlineType>, u64), // `(Bool; 42)` XXX
    TypeLevelApplication(Identifier, Vec<InlineType>), // XXX
    TypeLevelApplicationNamed(Identifier, Vec<(SimpleIdentifier, InlineType)>), // XXX
    MacroInv(Identifier), // XXX
    Attributed(Box<Attribute>, Box<InlineType>), // XXX
}

enum DefinedType {
    Inline(InlineType),
    Sum(bool, Vec<(SimpleIdentifier, InlineType)>), // bool is whether the tags are visible
    TypeLevelFunction(Vec<SimpleIdentifier>, Box<DefinedType>), // <S, T> => Foo
    Attributed(Box<Attribute>, Box<DefinedType>),
}

struct FloatLiteral(String);
struct StringLiteral(String);
struct IntLiteralDec(String);
struct IntLiteralBin(String);
struct IntLiteralHex(String);

enum Expression {
    Id(Identifier),
    FloatLit(FloatLiteral),
    StringLit(StringLiteral),
    IntLitDec(IntLiteralDec),
    IntLitBin(IntLiteralBin),
    IntLitHex(IntLiteralHex),
    Reference(Box<Expression>, bool), // true: mutable, false: immutable (default)
    Dereference(Box<Expression>), // TODO mutability?
    Array(Vec<Expression>),
    Indexing {
        indexee: Box<Expression>,
        index: Box<Expression>,
    },
    ProductAnon(Vec<Expression>),
    ProductNamed(Vec<(SimpleIdentifier, Expression)>),
    ProductRepeated(Box<Expression>, u64),
    ProductAccessAnon {
        accessee: Box<Expression>,
        index: u64,
    },
    ProductAccessNamed {
        accessee: Box<Expression>,
        field: SimpleIdentifier,
    },
    FunApplication(Identifier, Vec<Expression>),
    FunApplicationNamed(Identifier, Vec<(SimpleIdentifier, Expression)>),
    TypeApplication(Identifier, Vec<InlineType>),
    TypeApplicationNamed(Identifier, Vec<(SimpleIdentifier, InlineType)>),
    Sum(Identifier, Box<Expression>),
    Sizeof(Box<InlineType>),
    Alignof(Box<InlineType>),
    Offsetof(Identifier, SimpleIdentifier),
    LAnd(Box<Expression>, Box<Expression>), // &&
    LOr(Box<Expression>, Box<Expression>), // ||
    Add(Box<Expression>, Box<Expression>), // +
    BitAnd(Box<Expression>, Box<Expression>), // &
    BitOr(Box<Expression>, Box<Expression>), // |
    BitXor(Box<Expression>, Box<Expression>), // ^
    Div(Box<Expression>, Box<Expression>), // /
    Eq(Box<Expression>, Box<Expression>), // ==
    NEq(Box<Expression>, Box<Expression>), // !=
    Modulus(Box<Expression>, Box<Expression>), // %
    Mul(Box<Expression>, Box<Expression>), // *
    Neg(Box<Expression>), // -
    Not(Box<Expression>), // !
    ShiftL(Box<Expression>, Box<Expression>), // <<
    ShiftR(Box<Expression>, Box<Expression>), // >>
    Sub(Box<Expression>, Box<Expression>), // -
    Cast(Box<InlineType>, Box<Expression>),
    FunLiteral(Vec<(SimpleIdentifier, bool, InlineType)>, Vec<Statement>), // bool is mutability
    MacroInv(Identifier),
    Attributed(Box<Attribute>, Box<Expression>),
    // TODO assignment, also `+=` etc?
}

enum Statement {
    Return(Option<Box<Expression>>),
    Break(Option<Box<Expression>>),
    Expr(Box<Expression>), // evaluate expression for its side-effects
    IfThen(Box<Expression>, Vec<Statement>),
    IfThenElse(Box<Expression>, Vec<Statement>, Vec<Statement>),
    Match(Box<Expression>, Vec<(Pattern, Vec<Statement>)>),
    While(Box<Expression>, Vec<Statement>),
    WhileMatch(Box<Expression>, Vec<(Pattern, Vec<Statement>)>),
    Let(bool, Vec<PatternIrrefutable>, Option<InlineType>, Option<Expression>),
    Label(SimpleIdentifier),
    Goto(SimpleIdentifier),
    MacroInv(Identifier, Pattern),
    Attributed(Box<Attribute>, Box<Statement>),
}

enum PatternIrrefutable {
    Blank,
    Id(SimpleIdentifier),
    Attributed(Box<Attribute>, Box<PatternIrrefutable>),
}

enum Pattern {
    Irrefutable(PatternIrrefutable),
    Blank,
    FloatLit(FloatLiteral),
    StringLit(StringLiteral),
    IntLitDec(IntLiteralDec),
    IntLitBin(IntLiteralBin),
    IntLitHex(IntLiteralHex),
    ProductAnon(Vec<Pattern>),
    ProductNamed(Vec<(SimpleIdentifier, Pattern)>),
    Sum(Identifier, Box<Pattern>),
    Reference(Box<Pattern>),
    GuardedPattern(Box<Pattern>, Box<Expression>),
    ManyPatterns(Vec<Pattern>),
    NamedPattern(SimpleIdentifier, Box<Pattern>),
    Attributed(Box<Attribute>, Box<Pattern>),
}
