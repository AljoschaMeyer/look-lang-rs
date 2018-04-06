use nom::{IResult};
use nom_locate::LocatedSpan;

use super::{Position, p_skip0, p_skip1, identifiers::{SimpleIdentifier, p_simple_id, Identifier, p_identifier}, attributes::{Attribute, p_attribute}};

type Span<'a> = LocatedSpan<&'a str>;

named!(p_opt_mut<Span, bool>,
    do_parse!(
        is_mut: opt!(do_parse!(
            tag!("mut") >>
            p_skip1 >>
            (())
        )) >>
        (is_mut.is_some())
    )
);

named!(p_pattern_opt_attributed<Span, (Option<Attribute>, Pattern)>,
    alt!(
        do_parse!(
            attr: p_attribute >>
            p_skip0 >>
            tag!("{") >>
            inner: p_pattern >>
            p_skip0 >>
            tag!("}") >>
            ((Some(attr), inner))
        ) |
        do_parse!(
            inner: p_pattern >>
            ((None, inner))
        )
    )
);

named!(p_pattern_named<Span, (Option<Attribute>, SimpleIdentifier, Option<Attribute>, Pattern)>,
    alt!(
        do_parse!(
            attr: p_attribute >>
            p_skip0 >>
            tag!("{") >>
            p_skip0 >>
            sid: p_simple_id >>
            p_skip0 >>
            tag!("=") >>
            p_skip0 >>
            inner: p_pattern_opt_attributed >>
            p_skip0 >>
            tag!("}") >>
            ((Some(attr), sid, inner.0, inner.1))
        ) |
        do_parse!(
            sid: p_simple_id >>
            p_skip0 >>
            tag!("=") >>
            p_skip0 >>
            inner: p_pattern_opt_attributed >>
            ((None, sid, inner.0, inner.1))
        )
    )
);

named!(_peek_p_pattern_named<Span, (Option<Attribute>, SimpleIdentifier, Option<Attribute>, Pattern)>, peek!(p_pattern_named));

#[test]
fn test_sid_eq_sid() {
    works!(p_pattern_named, "a= t", 0);
    works!(p_pattern_named, "a=  t", 0);
    works!(p_pattern_named, "a = t", 0);
    works!(p_pattern_named, "a=t", 0);
    works!(p_pattern_named, "#[foo]{a=t}", 0);
    works!(p_pattern_named, "#[foo]  {  a  =  t  }", 0);

    works!(p_pattern_named, "a= mut t", 0);
    works!(p_pattern_named, "a=  mut  t", 0);
    works!(p_pattern_named, "a = mut t", 0);
    works!(p_pattern_named, "a=mut t", 0);
    works!(p_pattern_named, "#[foo]{a=mut t}", 0);
    works!(p_pattern_named, "#[foo]  {  a  =  mut  t  }", 0);
}

#[derive(Debug, PartialEq, Eq)]
pub enum PatternList {
    Anonymous(Vec<(Option<Attribute>, Pattern)>),
    Named(Vec<(Option<Attribute>, SimpleIdentifier, Option<Attribute>, Pattern)>)
}

pub fn p_pattern_list(input: Span) -> IResult<Span, PatternList> {
    match _peek_p_pattern_named(input) {
        IResult::Done(input, _) => {
            let (input, list) = try_parse!(input, map!(separated_list!(do_parse!(p_skip0 >> tag!(",") >> p_skip0 >> (())), p_pattern_named), PatternList::Named));
            IResult::Done(input, list)
        }
        _ => {
            let (input, list) = try_parse!(input, map!(separated_list!(do_parse!(p_skip0 >> tag!(",") >> p_skip0 >> (())), p_pattern_opt_attributed), PatternList::Anonymous));
            IResult::Done(input, list)
        }
    }
}

#[test]
fn test_pattern_list() {
    works!(p_pattern_list, "ö", 2);
    works!(p_pattern_list, "Aö", 2);
    works!(p_pattern_list, "A,@~B,Cö", 2);
    works!(p_pattern_list, "A  ,  B  ,  Cö", 2);
    works!(p_pattern_list, "a=Aö", 2);
    works!(p_pattern_list, "a=A,b=B,c=Cö", 2);
    works!(p_pattern_list, "a  =  A  ,  b  =  B  ,  c  =  Cö", 2);
    works!(p_pattern_list, "#[foo]{a}ö", 2);
    works!(p_pattern_list, "#[foo]{ a= a }ö", 2);
    works!(p_pattern_list, "#[foo]{ a= #[foo]{a} }ö", 2);

    works!(p_pattern_list, "mut Aö", 2);
    works!(p_pattern_list, "A, mut B,Cö", 2);
    works!(p_pattern_list, "A  ,  mut  B  ,  Cö", 2);
    works!(p_pattern_list, "a=mut Aö", 2);
    works!(p_pattern_list, "a=A,b=mut B,c=Cö", 2);
    works!(p_pattern_list, "a  =  A  ,  b  =  mut  B  ,  c  =  Cö", 2);
    works!(p_pattern_list, "#[foo]{mut a}ö", 2);
    works!(p_pattern_list, "#[foo]{ a= mut a }ö", 2);
    works!(p_pattern_list, "#[foo]{ a= #[foo]{mut a} }ö", 2);
}

#[derive(Debug, PartialEq, Eq)]
pub enum ConstPattern {

} // literals, operators, if, ifelse, match?, ref, ptr, deref, array, tuple_anon, tuple_named, tuple_repeated, indexing (index must be const expression), product_access_anon/named, sizeof, offsetof, cast, macro_inv; but: no identifier, no function literal TODO attributes?

#[derive(Debug, PartialEq, Eq)]
pub enum Pattern {
    Id(bool, SimpleIdentifier, Position),
    Blank(Position),
    Ptr(Box<Pattern>, Position),
    PtrMut(Box<Pattern>, Position),
    Tuple(PatternList, Position),
    Struct(Identifier, PatternList, Position),
}

impl Pattern {
    pub fn is_id(&self) -> bool {
        match self {
            &Pattern::Id(_, _, _) => true,
            _ => false
        }
    }

    pub fn is_blank(&self) -> bool {
        match self {
            &Pattern::Blank(_) => true,
            _ => false
        }
    }

    pub fn is_ptr(&self) -> bool {
        match self {
            &Pattern::Ptr(_, _) => true,
            _ => false
        }
    }

    pub fn is_ptr_mut(&self) -> bool {
        match self {
            &Pattern::PtrMut(_, _) => true,
            _ => false
        }
    }

    pub fn is_tuple(&self) -> bool {
        match self {
            &Pattern::Tuple(_, _) => true,
            _ => false
        }
    }

    pub fn is_struct(&self) -> bool {
        match self {
            &Pattern::Struct(_, _, _) => true,
            _ => false
        }
    }
}

named!(p_pattern_id<Span, Pattern>, do_parse!(
    start: position!() >>
    is_mut: p_opt_mut >>
    id: p_simple_id >>
    end: position!() >>
    (Pattern::Id(is_mut, id, Position::new(start, end)))
));

named!(p_blank<Span, Pattern>, do_parse!(
    start: position!() >>
    tag!("_") >>
    end: position!() >>
    (Pattern::Blank(Position::new(start, end)))
));

named!(p_ptr<Span, Pattern>, do_parse!(
    start: position!() >>
    tag!("@") >>
    inner: p_pattern >>
    end: position!() >>
    (Pattern::Ptr(Box::new(inner), Position::new(start, end)))
));

named!(p_ptr_mut<Span, Pattern>, do_parse!(
    start: position!() >>
    tag!("~") >>
    inner: p_pattern >>
    end: position!() >>
    (Pattern::PtrMut(Box::new(inner), Position::new(start, end)))
));

named!(p_tuple<Span, Pattern>, do_parse!(
    start: position!() >>
    tag!("(") >>
    p_skip0 >>
    list: p_pattern_list >>
    p_skip0 >>
    tag!(")") >>
    end: position!() >>
    (Pattern::Tuple(list, Position::new(start, end)))
));

named!(p_struct<Span, Pattern>, do_parse!(
    start: position!() >>
    id: p_identifier >>
    p_skip0 >>
    tag!("(") >>
    p_skip0 >>
    list: p_pattern_list >>
    p_skip0 >>
    tag!(")") >>
    end: position!() >>
    (Pattern::Struct(id, list, Position::new(start, end)))
));

named!(pub p_pattern<Span, Pattern>, alt!(
    complete!(p_struct) | p_pattern_id | p_blank | p_ptr | p_ptr_mut | p_tuple
));

#[test]
fn test_pattern() {
    works_check!(p_pattern, "_a", 0, is_id);
    works_check!(p_pattern, "mut _a", 0, is_id);
    works_check!(p_pattern, "mut_a", 0, is_id);
    works_check!(p_pattern, "mut_", 0, is_id);

    works_check!(p_pattern, "_", 0, is_blank);
    fails!(p_pattern, "mut _");

    works_check!(p_pattern, "@a", 0, is_ptr);
    works_check!(p_pattern, "@~a", 0, is_ptr);
    fails!(p_pattern, "mut @A");

    works_check!(p_pattern, "~a", 0, is_ptr_mut);
    works_check!(p_pattern, "~@a", 0, is_ptr_mut);
    fails!(p_pattern, "mut ~A");

    works_check!(p_pattern, "()", 0, is_tuple);
    works_check!(p_pattern, "(a)", 0, is_tuple);
    works_check!(p_pattern, "(a,b)", 0, is_tuple);
    works_check!(p_pattern, "(a=a,b=b)", 0, is_tuple);
    works_check!(p_pattern, "(#[foo]{a})", 0, is_tuple);
    works_check!(p_pattern, "(#[foo]{a},b)", 0, is_tuple);
    works_check!(p_pattern, "(#[foo]{a=#[foo]{a}},b=b)", 0, is_tuple);
    works_check!(p_pattern, "(mut a)", 0, is_tuple);
    works_check!(p_pattern, "(a,mut b)", 0, is_tuple);
    works_check!(p_pattern, "(a=a,b=mut b)", 0, is_tuple);
    works_check!(p_pattern, "(#[foo]{mut a})", 0, is_tuple);
    works_check!(p_pattern, "(#[foo]{mut a},b)", 0, is_tuple);
    works_check!(p_pattern, "(#[foo]{a=#[foo]{mut a}},b=b)", 0, is_tuple);
    not_complete!(p_pattern, "mut()");
    fails!(p_pattern, "(mut a=mut b)");

    works_check!(p_pattern, "s::t::u()", 0, is_struct);
    works_check!(p_pattern, "s(a)", 0, is_struct);
    works_check!(p_pattern, "s(a,b)", 0, is_struct);
    works_check!(p_pattern, "s(a=a,b=b)", 0, is_struct);
    works_check!(p_pattern, "s(#[foo]{a})", 0, is_struct);
    works_check!(p_pattern, "s(#[foo]{a},b)", 0, is_struct);
    works_check!(p_pattern, "s(#[foo]{a=#[foo]{a}},b=b)", 0, is_struct);
    works_check!(p_pattern, "s(mut a)", 0, is_struct);
    works_check!(p_pattern, "s(a,mut b)", 0, is_struct);
    works_check!(p_pattern, "s::t::u  (  a  ,  mut  b  )", 0, is_struct);
    works_check!(p_pattern, "s(a=a,b=mut b)", 0, is_struct);
    works_check!(p_pattern, "s(#[foo]{mut a})", 0, is_struct);
    works_check!(p_pattern, "s(#[foo]{mut a},b)", 0, is_struct);
    works_check!(p_pattern, "s(#[foo]{a=#[foo]{mut a}},b=b)", 0, is_struct);
}
