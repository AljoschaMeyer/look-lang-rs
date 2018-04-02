use std::num::ParseIntError;

use nom::IResult;
use nom_locate::LocatedSpan;

use super::{Position, p_skip0, identifiers::{SimpleIdentifier, p_simple_id, Identifier, p_identifier}, attributes::{Attribute, p_attribute}};

type Span<'a> = LocatedSpan<&'a str>;

#[derive(Debug, PartialEq, Eq)]
pub struct Repetition(u32, Position);

fn is_repetition_char(chr: char) -> bool {
    chr.is_ascii_digit()
}

fn from_base_10<'a>(src: Span<'a>) -> Result<u32, ParseIntError> {
    u32::from_str_radix(src.fragment, 10)
}

named!(p_repetition<Span, Repetition>, do_parse!(
    start: position!() >>
    int: map_res!(take_while1!(is_repetition_char), from_base_10) >>
    end: position!() >>
    (Repetition(int, Position::new(start, end)))
));

#[test]
fn test_repetition() {
    works!(p_repetition, "0", 0);
    works!(p_repetition, "0042", 0);
    works!(p_repetition, "0a", 1);
    works!(p_repetition, "0 0", 2);
    fails!(p_repetition, "b0");
}

named!(p_sid_with_type<Span, (SimpleIdentifier, Type)>, do_parse!(
    sid: p_simple_id >>
    p_skip0 >>
    tag!(":") >>
    p_skip0 >>
    the_type: p_type >>
    ((sid, the_type))
));

#[test]
fn test_sid_with_type() {
    works!(p_sid_with_type, "a: t", 0);
    works!(p_sid_with_type, "a:  t", 0);
    works!(p_sid_with_type, "a : t", 0);
    works!(p_sid_with_type, "a:t", 0);
}

named!(p_type_eq_sid<Span, (Type, SimpleIdentifier)>, do_parse!(
    the_type: p_type >>
    p_skip0 >>
    tag!("=") >>
    p_skip0 >>
    sid: p_simple_id >>
    ((the_type, sid))
));

#[test]
fn test_type_eq_sid() {
    works!(p_type_eq_sid, "r = a", 0);
    works!(p_type_eq_sid, "r =  a", 0);
    works!(p_type_eq_sid, "r = a", 0);
    works!(p_type_eq_sid, "r=a", 0);
}

#[derive(Debug, PartialEq, Eq)]
pub enum TypeList {
    Anonymous(Vec<Type>),
    Named(Vec<(SimpleIdentifier, Type)>)
}

named!(_peek_sid_colon<Span, ()>, peek!(do_parse!(
    p_simple_id >>
    p_skip0 >>
    tag!(":") >>
    (())
)));

pub fn p_type_list(input: Span) -> IResult<Span, TypeList> {
    match _peek_sid_colon(input) {
        IResult::Done(input, _) => {
            let (input, list) = try_parse!(input, map!(separated_list!(do_parse!(tag!(",") >> p_skip0 >> (())), p_sid_with_type), TypeList::Named));
            IResult::Done(input, list)
        }
        _ => {
            let (input, list) = try_parse!(input, map!(separated_list!(do_parse!(tag!(",") >> p_skip0 >> (())), p_type), TypeList::Anonymous));
            IResult::Done(input, list)
        }
    }
}

#[test]
fn test_type_list() {
    works!(p_type_list, "ö", 2);
    works!(p_type_list, "Aö", 2);
    works!(p_type_list, "A,B,Cö", 2);
    works!(p_type_list, "A  ,  B  ,  Cö", 2);
    works!(p_type_list, "a:Aö", 2);
    works!(p_type_list, "a:A,b:B,c:Cö", 2);
    works!(p_type_list, "a  :  A  ,  b  :  B  ,  c  :  Cö", 2);
}

#[derive(Debug, PartialEq, Eq)]
pub enum Type {
    Ptr(Box<Type>, Position),
    PtrMut(Box<Type>, Position),
    Array(Box<Type>, Position),
    Attributed(Box<Attribute>, Box<Type>, Position),
    ProductRepeated(Box<Type>, Repetition, Position),
    Product(TypeList, Position),
    Fun(TypeList, Box<Type>, Position),
    Id(Identifier, Position),
    MacroInv(Identifier, String, Position),
    TypeApplicationAnon(Identifier, Vec<Type>, Position),
    TypeApplicationNamed(Identifier, Vec<(Type, SimpleIdentifier)>, Position),
}

impl Type {
    pub fn is_ptr(&self) -> bool {
        match self {
            &Type::Ptr(_, _) => true,
            _ => false
        }
    }

    pub fn is_ptr_mut(&self) -> bool {
        match self {
            &Type::PtrMut(_, _) => true,
            _ => false
        }
    }

    pub fn is_array(&self) -> bool {
        match self {
            &Type::Array(_, _) => true,
            _ => false
        }
    }

    pub fn is_attributed(&self) -> bool {
        match self {
            &Type::Attributed(_, _, _) => true,
            _ => false
        }
    }

    pub fn is_product_repeated(&self) -> bool {
        match self {
            &Type::ProductRepeated(_, _, _) => true,
            _ => false
        }
    }

    pub fn is_product_anon(&self) -> bool {
        match self {
            &Type::Product(ref list, _) => {
                match list {
                    &TypeList::Anonymous(_) => true,
                    _ => false
                }
            },
            _ => false
        }
    }

    pub fn is_product_named(&self) -> bool {
        match self {
            &Type::Product(ref list, _) => {
                match list {
                    &TypeList::Named(_) => true,
                    _ => false
                }
            },
            _ => false
        }
    }

    pub fn is_fun_anon(&self) -> bool {
        match self {
            &Type::Fun(ref list, _, _) => {
                match list {
                    &TypeList::Anonymous(_) => true,
                    _ => false
                }
            },
            _ => false
        }
    }

    pub fn is_fun_named(&self) -> bool {
        match self {
            &Type::Fun(ref list, _, _) => {
                match list {
                    &TypeList::Named(_) => true,
                    _ => false
                }
            },
            _ => false
        }
    }

    pub fn is_id(&self) -> bool {
        match self {
            &Type::Id(_, _) => true,
            _ => false
        }
    }

    pub fn is_macro_inv(&self) -> bool {
        match self {
            &Type::MacroInv(_, _, _) => true,
            _ => false
        }
    }

    pub fn is_type_application_anon(&self) -> bool {
        match self {
            &Type::TypeApplicationAnon(_, _, _) => true,
            _ => false
        }
    }

    pub fn is_type_application_named(&self) -> bool {
        match self {
            &Type::TypeApplicationNamed(_, _, _) => true,
            _ => false
        }
    }
}

named!(p_ptr<Span, Type>, do_parse!(
    start: position!() >>
    tag!("@") >>
    p_skip0 >>
    inner: p_type >>
    end: position!() >>
    (Type::Ptr(Box::new(inner), Position::new(start, end)))
));

named!(p_ptr_mut<Span, Type>, do_parse!(
    start: position!() >>
    tag!("~") >>
    p_skip0 >>
    inner: p_type >>
    end: position!() >>
    (Type::PtrMut(Box::new(inner), Position::new(start, end)))
));

named!(p_array<Span, Type>, do_parse!(
    start: position!() >>
    tag!("[") >>
    p_skip0 >>
    inner: p_type >>
    p_skip0 >>
    tag!("]") >>
    end: position!() >>
    (Type::Array(Box::new(inner), Position::new(start, end)))
));

named!(p_attributed<Span, Type>, do_parse!(
    start: position!() >>
    attr: p_attribute >>
    p_skip0 >>
    tag!("{") >>
    p_skip0 >>
    inner: p_type >>
    p_skip0 >>
    tag!("}") >>
    end: position!() >>
    (Type::Attributed(Box::new(attr), Box::new(inner), Position::new(start, end)))
));

named!(p_product_repeated<Span, Type>, do_parse!(
    start: position!() >>
    tag!("(") >>
    p_skip0 >>
    inner: p_type >>
    p_skip0 >>
    tag!(";") >>
    p_skip0 >>
    rep: p_repetition >>
    p_skip0 >>
    tag!(")") >>
    end: position!() >>
    (Type::ProductRepeated(Box::new(inner), rep, Position::new(start, end)))
));

named!(_arrow<Span, Span>, tag!("->"));

pub fn p_product_or_fun_anon(input: Span) -> IResult<Span, Type> {
    let (input, start) = try_parse!(input, position!());
    let (input, _) = try_parse!(input, tag!("("));
    let (input, _) = try_parse!(input, p_skip0);
    let (input, types) = try_parse!(input, separated_list!(
        do_parse!(p_skip0 >> tag!(",") >> p_skip0 >> (())),
        p_type
    ));
    let (input, _) = try_parse!(input, p_skip0);
    let (input, _) = try_parse!(input, tag!(")"));
    let (input, _) = try_parse!(input, p_skip0);

    match _arrow(input) {
        IResult::Done(input, _) => {
            let (input, _) = try_parse!(input, p_skip0);
            let (input, return_type) = try_parse!(input, p_type);
            let (input, end) = try_parse!(input, position!());
            IResult::Done(input, Type::Fun(TypeList::Anonymous(types), Box::new(return_type), Position::new(start, end)))
        }
        _ => {
            let (input, end) = try_parse!(input, position!());
            IResult::Done(input, Type::Product(TypeList::Anonymous(types), Position::new(start, end)))
        },
    }
}

pub fn p_product_or_fun_named(input: Span) -> IResult<Span, Type> {
    let (input, start) = try_parse!(input, position!());
    let (input, _) = try_parse!(input, tag!("("));
    let (input, _) = try_parse!(input, p_skip0);
    let (input, types) = try_parse!(input, separated_list!(
        do_parse!(p_skip0 >> tag!(",") >> p_skip0 >> (())),
        p_sid_with_type
    ));
    let (input, _) = try_parse!(input, p_skip0);
    let (input, _) = try_parse!(input, tag!(")"));
    let (input, _) = try_parse!(input, p_skip0);

    match _arrow(input) {
        IResult::Done(input, _) => {
            let (input, _) = try_parse!(input, p_skip0);
            let (input, return_type) = try_parse!(input, p_type);
            let (input, end) = try_parse!(input, position!());
            IResult::Done(input, Type::Fun(TypeList::Named(types), Box::new(return_type), Position::new(start, end)))
        }
        _ => {
            let (input, end) = try_parse!(input, position!());
            IResult::Done(input, Type::Product(TypeList::Named(types), Position::new(start, end)))
        },
    }
}

named!(_bang<Span, Span>, tag!("!"));
named!(_langle<Span, Span>, tag!("<"));
named!(_peek_p_type_eq_sid<Span, (Type, SimpleIdentifier)>, peek!(p_type_eq_sid));

pub fn p_starts_with_id(input: Span) -> IResult<Span, Type> {
    let (input, start) = try_parse!(input, position!());
    let (input, id) = try_parse!(input, p_identifier);
    let (input, _) = try_parse!(input, p_skip0);

    match _bang(input) {
        IResult::Done(input, _) => {
            let (input, _) = try_parse!(input, p_skip0);
            let (input, _) = try_parse!(input, tag!("["));
            let (input, stuff) = try_parse!(input, opt!(is_not!("[]")));
            let (input, _) = try_parse!(input, tag!("]"));
            let (input, end) = try_parse!(input, position!());
            if stuff.is_some() {
                IResult::Done(input, Type::MacroInv(id, stuff.unwrap().fragment.to_string(), Position::new(start, end)))
            } else {
                IResult::Done(input, Type::MacroInv(id, "".to_string(), Position::new(start, end)))
            }

        }
        _ => {
            match _langle(input) {
                IResult::Done(input, _) => {
                    let (input, _) = try_parse!(input, terminated!(p_skip0, peek!(p_simple_id)));
                    match _peek_p_type_eq_sid(input) {
                        IResult::Done(input, _) => {
                            let (input, args) = try_parse!(input, separated_list!(
                                do_parse!(p_skip0 >> tag!(",") >> p_skip0 >> (())),
                                p_type_eq_sid
                            ));
                            let (input, _) = try_parse!(input, p_skip0);
                            let (input, _) = try_parse!(input, tag!(">"));
                            let (input, end) = try_parse!(input, position!());
                            IResult::Done(input, Type::TypeApplicationNamed(id, args, Position::new(start, end)))
                        }
                        _ => {
                            let (input, args) = try_parse!(input, separated_list!(
                                do_parse!(p_skip0 >> tag!(",") >> p_skip0  >> (())),
                                p_type
                            ));
                            let (input, _) = try_parse!(input, p_skip0);
                            let (input, _) = try_parse!(input, tag!(">"));
                            let (input, end) = try_parse!(input, position!());
                            IResult::Done(input, Type::TypeApplicationAnon(id, args, Position::new(start, end)))
                        }
                    }
                }
                _ => {
                    let (input, end) = try_parse!(input, position!());
                    IResult::Done(input, Type::Id(id, Position::new(start, end)))
                },
            }
        },
    }
}

named!(pub p_type<Span, Type>, alt!(
    p_ptr | p_ptr_mut | p_array | p_attributed | p_product_repeated | p_product_or_fun_anon | p_product_or_fun_named | p_starts_with_id
));

#[test]
fn test_type() {
    works_check!(p_type, "@r", 0, is_ptr);
    works_check!(p_type, "@ r", 0, is_ptr);

    works_check!(p_type, "~r", 0, is_ptr_mut);
    works_check!(p_type, "~ r", 0, is_ptr_mut);

    works_check!(p_type, "[r]", 0, is_array);
    works_check!(p_type, "[ r]", 0, is_array);
    works_check!(p_type, "[r ]", 0, is_array);

    works_check!(p_type, "#[foo] { r }", 0, is_attributed);
    works_check!(p_type, "#[foo]{ r }", 0, is_attributed);
    works_check!(p_type, "#[foo]  { r }", 0, is_attributed);
    works_check!(p_type, "#[foo] {r }", 0, is_attributed);
    works_check!(p_type, "#[foo] { r}", 0, is_attributed);

    works_check!(p_type, "(r; 42)", 0, is_product_repeated);
    works_check!(p_type, "( r; 42)", 0, is_product_repeated);
    works_check!(p_type, "(r ; 42)", 0, is_product_repeated);
    works_check!(p_type, "(r;42)", 0, is_product_repeated);
    works_check!(p_type, "(r;  42)", 0, is_product_repeated);
    works_check!(p_type, "(r; 42 )", 0, is_product_repeated);
    fails!(p_type, "(r; 0b11)");

    works_check!(p_type, "()", 0, is_product_anon);
    works_check!(p_type, "( )", 0, is_product_anon);
    works_check!(p_type, "(r)", 0, is_product_anon);
    works_check!(p_type, "(r, r)", 0, is_product_anon);
    works_check!(p_type, "(  r,  r  )", 0, is_product_anon);
    works_check!(p_type, "(r,r)", 0, is_product_anon);
    works_check!(p_type, "(r ,r)", 0, is_product_anon);

    works_check!(p_type, "(a: r)", 0, is_product_named);
    works_check!(p_type, "(a: r, a: r)", 0, is_product_named);
    works_check!(p_type, "( a: r,  A:  r )", 0, is_product_named);
    works_check!(p_type, "(a : r)", 0, is_product_named);
    works_check!(p_type, "(a :r)", 0, is_product_named);
    works_check!(p_type, "(a: r , b: r)", 0, is_product_named);
    fails!(p_type, "(a: r,)");

    works_check!(p_type, "() -> ()", 0, is_fun_anon);
    works_check!(p_type, "() ->  r", 0, is_fun_anon);
    works_check!(p_type, "( ) -> r", 0, is_fun_anon);
    works_check!(p_type, "(r) -> r", 0, is_fun_anon);
    works_check!(p_type, "(r, r) -> (r, r)", 0, is_fun_anon);
    works_check!(p_type, "(  r,  r  ) -> r", 0, is_fun_anon);
    works_check!(p_type, "(r,r) -> r", 0, is_fun_anon);
    works_check!(p_type, "(r ,r) -> r", 0, is_fun_anon);
    works_check!(p_type, "()-> r", 0, is_fun_anon);
    works_check!(p_type, "()  -> r", 0, is_fun_anon);
    not_complete!(p_type, "() - r");

    works_check!(p_type, "(a: r) -> r", 0, is_fun_named);
    works_check!(p_type, "(a: r, b: r) -> (r, r)", 0, is_fun_named);
    works_check!(p_type, "(  a:   r,  b: r  ) -> r", 0, is_fun_named);
    works_check!(p_type, "(a: r)-> r", 0, is_fun_named);
    works_check!(p_type, "(a: r)  -> r", 0, is_fun_named);
    not_complete!(p_type, "(a: r) - r");

    works_check!(p_type, "a", 0, is_id);
    works_check!(p_type, "a::b::c", 0, is_id);

    works_check!(p_type, "a![  ö ( +@! goo, iji  ]", 0, is_macro_inv);
    works_check!(p_type, "a![]", 0, is_macro_inv);
    works_check!(p_type, "a::b![]", 0, is_macro_inv);
    works_check!(p_type, "a![  ]", 0, is_macro_inv);
    works_check!(p_type, "a! []", 0, is_macro_inv);
    works_check!(p_type, "a ![]", 0, is_macro_inv);
    fails!(p_type, "a![[]");
    not_complete!(p_type, "a![]]");

    works_check!(p_type, "a<b>", 0, is_type_application_anon);
    works_check!(p_type, "a::b<c>", 0, is_type_application_anon);
    works_check!(p_type, "a<  b  >", 0, is_type_application_anon);
    works_check!(p_type, "a<b, c>", 0, is_type_application_anon);
    works_check!(p_type, "a<  b,  c  >", 0, is_type_application_anon);
    works_check!(p_type, "a<a,b>", 0, is_type_application_anon);
    works_check!(p_type, "a<a ,b>", 0, is_type_application_anon);
    works_check!(p_type, "a  <  b  >", 0, is_type_application_anon);
    not_complete!(p_type, "a<>");
    not_complete!(p_type, "a<   >");

    works_check!(p_type, "a<b = y>", 0, is_type_application_named);
    works_check!(p_type, "a::b<c = z>", 0, is_type_application_named);
    works_check!(p_type, "a<  b   =  y  >", 0, is_type_application_named);
    works_check!(p_type, "a<b = y, c = z>", 0, is_type_application_named);
    works_check!(p_type, "a<  b = y,  c = z  >", 0, is_type_application_named);
    works_check!(p_type, "a<a= x>", 0, is_type_application_named);
    works_check!(p_type, "a<a =x>", 0, is_type_application_named);
    works_check!(p_type, "a<a = x,b = y>", 0, is_type_application_named);
    works_check!(p_type, "a<a = x , b = y>", 0, is_type_application_named);
}

pub enum TypeDef {
    Inline(Type),
    Attributed(Box<Attribute>, Box<TypeDef>, Position),
    TypeLevelFun(Vec<SimpleIdentifier>, Box<TypeDef>, Position),
    Struct(bool, TypeList, Position),
    Enum(bool, Vec<(SimpleIdentifier, TypeList)>, Position),
}

impl TypeDef {
    pub fn is_inline(&self) -> bool {
        match self {
            &TypeDef::Inline(_) => true,
            _ => false
        }
    }

    pub fn is_attributed(&self) -> bool {
        match self {
            &TypeDef::Attributed(_, _, _) => true,
            _ => false
        }
    }

    pub fn is_type_level_fun(&self) -> bool {
        match self {
            &TypeDef::TypeLevelFun(_, _, _) => true,
            _ => false
        }
    }

    pub fn is_struct(&self) -> bool {
        match self {
            &TypeDef::Struct(_, _, _) => true,
            _ => false
        }
    }

    pub fn is_enum(&self) -> bool {
        match self {
            &TypeDef::Enum(_, _, _) => true,
            _ => false
        }
    }
}

named!(p_inline_def<Span, TypeDef>, map!(p_type, TypeDef::Inline));

named!(p_attributed_def<Span, TypeDef>, do_parse!(
    start: position!() >>
    attr: p_attribute >>
    p_skip0 >>
    tag!("{") >>
    p_skip0 >>
    inner: p_type_def >>
    p_skip0 >>
    tag!("}") >>
    end: position!() >>
    (TypeDef::Attributed(Box::new(attr), Box::new(inner), Position::new(start, end)))
));

named!(p_type_level_fun<Span, TypeDef>, do_parse!(
    start: position!() >>
    tag!("<") >>
    terminated!(p_skip0, peek!(p_simple_id)) >>
    args: separated_list!(
        do_parse!(p_skip0 >> tag!(",") >> p_skip0 >> (())),
        p_simple_id
    ) >>
    p_skip0 >>
    tag!(">") >>
    p_skip0 >>
    tag!("=>") >>
    p_skip0 >>
    return_type: p_type_def >>
    end: position!() >>
    (TypeDef::TypeLevelFun(args, Box::new(return_type), Position::new(start, end)))
));

named!(p_struct<Span, TypeDef>, do_parse!(
    start: position!() >>
    public: opt!(do_parse!(tag!("pub") >> p_skip0 >> (()))) >>
    tag!("struct") >>
    p_skip0 >>
    tag!("(") >>
    p_skip0 >>
    list: p_type_list >>
    tag!(")") >>
    end: position!() >>
    (TypeDef::Struct(public.is_some(), list, Position::new(start, end)))
));

named!(p_enum<Span, TypeDef>, do_parse!(
    start: position!() >>
    public: opt!(do_parse!(tag!("pub") >> p_skip0 >> (()))) >>
    tag!("enum") >>
    p_skip0 >>
    tag!("{") >>
    p_skip0 >>
    entries: separated_list!(
        do_parse!(tag!(",") >> p_skip0 >> (())),
        do_parse!(
            id: p_simple_id >>
            p_skip0 >>
            tag!("(") >>
            p_skip0 >>
            fields: p_type_list >>
            p_skip0 >>
            tag!(")") >>
            p_skip0 >>
            ((id, fields))
        )
    ) >>
    p_skip0 >>
    tag!("}") >>
    end: position!() >>
    (TypeDef::Enum(public.is_some(), entries, Position::new(start, end)))
));

named!(pub p_type_def<Span, TypeDef>, alt!(
    p_attributed_def | p_type_level_fun | p_struct | p_enum | p_inline_def
));

#[test]
fn test_type_def() {
    works_check!(p_type_def, "foo", 0, is_inline);

    works_check!(p_type_def, "#[foo] { r }", 0, is_attributed);
    works_check!(p_type_def, "#[foo]{ r }", 0, is_attributed);
    works_check!(p_type_def, "#[foo]  { r }", 0, is_attributed);
    works_check!(p_type_def, "#[foo] {r }", 0, is_attributed);
    works_check!(p_type_def, "#[foo] { r}", 0, is_attributed);

    works_check!(p_type_def, "<A>=>A", 0, is_type_level_fun);
    works_check!(p_type_def, "<  A  >  =>  A", 0, is_type_level_fun);
    works_check!(p_type_def, "<A,B>=>A", 0, is_type_level_fun);
    works_check!(p_type_def, "<  A  ,  B  >  =>  A", 0, is_type_level_fun);
    fails!(p_type_def, "<>=>A");

    works_check!(p_type_def, "struct ()", 0, is_struct);
    works_check!(p_type_def, "struct  ( )", 0, is_struct);
    works_check!(p_type_def, "pub struct ()", 0, is_struct);
    works_check!(p_type_def, "struct (A)", 0, is_struct);
    works_check!(p_type_def, "struct (a:A)", 0, is_struct);
    works_check!(p_type_def, "struct (A,B)", 0, is_struct);
    works_check!(p_type_def, "struct (a:A,b:B)", 0, is_struct);
    works_check!(p_type_def, "struct  (  a  :  A  ,  b  :  B  )", 0, is_struct);

    works_check!(p_type_def, "enum {}", 0, is_enum);
    works_check!(p_type_def, "enum{A()}", 0, is_enum);
    works_check!(p_type_def, "enum{A(  )}", 0, is_enum);
    works_check!(p_type_def, "enum{A(B)}", 0, is_enum);
    works_check!(p_type_def, "enum  {  A  (  B  )  }", 0, is_enum);
    works_check!(p_type_def, "enum{A(b:B)}", 0, is_enum);
    works_check!(p_type_def, "enum{A(B),B(C)}", 0, is_enum);
    works_check!(p_type_def, "enum  {  A  (  B  )  ,  B  (  C  )  }", 0, is_enum);
    works_check!(p_type_def, "pub enum{A(B)}", 0, is_enum);
    works_check!(p_type_def, "enum{A(B,C)}", 0, is_enum);
    works_check!(p_type_def, "enum{A(  B  ,  C  )}", 0, is_enum);
    works_check!(p_type_def, "enum{A(b:B,  c  :  C  )  }", 0, is_enum);
    not_complete!(p_type_def, "enum{A}");
    not_complete!(p_type_def, "enum{A(),}");

    // TODO allow attributes in (named) lists (applications, products, product definitions, argument definitions (both value and type level))
}
