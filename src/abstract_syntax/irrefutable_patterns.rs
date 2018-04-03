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

named!(p_mut_sid<Span, (bool, Option<Attribute>, SimpleIdentifier)>,
    alt!(
        do_parse!(
            mutable: p_opt_mut >>
            attr: p_attribute >>
            p_skip0 >>
            tag!("{") >>
            p_skip0 >>
            id: p_simple_id >>
            p_skip0 >>
            tag!("}") >>
            ((mutable, Some(attr), id))
        ) |
        do_parse!(
           mutable: p_opt_mut >>
           id: p_simple_id >>
           ((mutable, None, id))
       )
    )
 );

 #[test]
 fn test_mut_sid() {
     works!(p_mut_sid, "a", 0);
     works!(p_mut_sid, "#[foo]{a}", 0);
     works!(p_mut_sid, "mut a", 0);
     works!(p_mut_sid, "mut #[foo]{a}", 0);
 }

named!(p_sid_eq_sid<Span, (Option<Attribute>, SimpleIdentifier, bool, Option<Attribute>, SimpleIdentifier)>,
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
            mutable_sid: p_mut_sid >>
            p_skip0 >>
            tag!("}") >>
            ((Some(attr), sid, mutable_sid.0, mutable_sid.1, mutable_sid.2))
        ) |
        do_parse!(
            sid: p_simple_id >>
            p_skip0 >>
            tag!("=") >>
            p_skip0 >>
            mutable_sid: p_mut_sid >>
            ((None, sid, mutable_sid.0, mutable_sid.1, mutable_sid.2))
        )
    )
);

named!(_peek_p_sid_eq_sid<Span, (Option<Attribute>, SimpleIdentifier, bool, Option<Attribute>, SimpleIdentifier)>, peek!(p_sid_eq_sid));

#[test]
fn test_sid_eq_sid() {
    works!(p_sid_eq_sid, "a= t", 0);
    works!(p_sid_eq_sid, "a=  t", 0);
    works!(p_sid_eq_sid, "a = t", 0);
    works!(p_sid_eq_sid, "a=t", 0);
    works!(p_sid_eq_sid, "#[foo]{a=t}", 0);
    works!(p_sid_eq_sid, "#[foo]  {  a  =  t  }", 0);

    works!(p_sid_eq_sid, "a= mut t", 0);
    works!(p_sid_eq_sid, "a=  mut  t", 0);
    works!(p_sid_eq_sid, "a = mut t", 0);
    works!(p_sid_eq_sid, "a=mut t", 0);
    works!(p_sid_eq_sid, "#[foo]{a=mut t}", 0);
    works!(p_sid_eq_sid, "#[foo]  {  a  =  mut  t  }", 0);
}

#[derive(Debug, PartialEq, Eq)]
pub enum MutSidList {
    Anonymous(Vec<(bool, Option<Attribute>, SimpleIdentifier)>),
    Named(Vec<(Option<Attribute>, SimpleIdentifier, bool, Option<Attribute>, SimpleIdentifier)>)
}

pub fn p_sid_list(input: Span) -> IResult<Span, MutSidList> {
    match _peek_p_sid_eq_sid(input) {
        IResult::Done(input, _) => {
            let (input, list) = try_parse!(input, map!(separated_list!(do_parse!(p_skip0 >> tag!(",") >> p_skip0 >> (())), p_sid_eq_sid), MutSidList::Named));
            IResult::Done(input, list)
        }
        _ => {
            let (input, list) = try_parse!(input, map!(separated_list!(do_parse!(p_skip0 >> tag!(",") >> p_skip0 >> (())), p_mut_sid), MutSidList::Anonymous));
            IResult::Done(input, list)
        }
    }
}

#[test]
fn test_sid_list() {
    works!(p_sid_list, "ö", 2);
    works!(p_sid_list, "Aö", 2);
    works!(p_sid_list, "A,B,Cö", 2);
    works!(p_sid_list, "A  ,  B  ,  Cö", 2);
    works!(p_sid_list, "a=Aö", 2);
    works!(p_sid_list, "a=A,b=B,c=Cö", 2);
    works!(p_sid_list, "a  =  A  ,  b  =  B  ,  c  =  Cö", 2);
    works!(p_sid_list, "#[foo]{a}ö", 2);
    works!(p_sid_list, "#[foo]{ a= a }ö", 2);
    works!(p_sid_list, "#[foo]{ a= #[foo]{a} }ö", 2);

    works!(p_sid_list, "mut Aö", 2);
    works!(p_sid_list, "A, mut B,Cö", 2);
    works!(p_sid_list, "A  ,  mut  B  ,  Cö", 2);
    works!(p_sid_list, "a=mut Aö", 2);
    works!(p_sid_list, "a=A,b=mut B,c=Cö", 2);
    works!(p_sid_list, "a  =  A  ,  b  =  mut  B  ,  c  =  Cö", 2);
    works!(p_sid_list, "mut #[foo]{a}ö", 2);
    works!(p_sid_list, "#[foo]{ a= mut a }ö", 2);
    works!(p_sid_list, "#[foo]{ a= mut #[foo]{a} }ö", 2);
}

#[derive(Debug, PartialEq, Eq)]
pub enum PatternIrrefutable {
    Id(bool, SimpleIdentifier, Position),
    Blank(Position),
    Ptr(Box<PatternIrrefutable>, Position),
    PtrMut(Box<PatternIrrefutable>, Position),
    Tuple(MutSidList, Position),
    Struct(Identifier, MutSidList, Position),
}

impl PatternIrrefutable {
    pub fn is_id(&self) -> bool {
        match self {
            &PatternIrrefutable::Id(_, _, _) => true,
            _ => false
        }
    }

    pub fn is_blank(&self) -> bool {
        match self {
            &PatternIrrefutable::Blank(_) => true,
            _ => false
        }
    }

    pub fn is_ptr(&self) -> bool {
        match self {
            &PatternIrrefutable::Ptr(_, _) => true,
            _ => false
        }
    }

    pub fn is_ptr_mut(&self) -> bool {
        match self {
            &PatternIrrefutable::PtrMut(_, _) => true,
            _ => false
        }
    }

    pub fn is_tuple(&self) -> bool {
        match self {
            &PatternIrrefutable::Tuple(_, _) => true,
            _ => false
        }
    }

    pub fn is_struct(&self) -> bool {
        match self {
            &PatternIrrefutable::Struct(_, _, _) => true,
            _ => false
        }
    }
}

named!(p_pattern_id<Span, PatternIrrefutable>, do_parse!(
    start: position!() >>
    is_mut: p_opt_mut >>
    id: p_simple_id >>
    end: position!() >>
    (PatternIrrefutable::Id(is_mut, id, Position::new(start, end)))
));

named!(p_blank<Span, PatternIrrefutable>, do_parse!(
    start: position!() >>
    tag!("_") >>
    end: position!() >>
    (PatternIrrefutable::Blank(Position::new(start, end)))
));

named!(p_ptr<Span, PatternIrrefutable>, do_parse!(
    start: position!() >>
    tag!("@") >>
    inner: p_pattern_irrefutable >>
    end: position!() >>
    (PatternIrrefutable::Ptr(Box::new(inner), Position::new(start, end)))
));

named!(p_ptr_mut<Span, PatternIrrefutable>, do_parse!(
    start: position!() >>
    tag!("~") >>
    inner: p_pattern_irrefutable >>
    end: position!() >>
    (PatternIrrefutable::PtrMut(Box::new(inner), Position::new(start, end)))
));

named!(p_tuple<Span, PatternIrrefutable>, do_parse!(
    start: position!() >>
    tag!("(") >>
    p_skip0 >>
    list: p_sid_list >>
    p_skip0 >>
    tag!(")") >>
    end: position!() >>
    (PatternIrrefutable::Tuple(list, Position::new(start, end)))
));

named!(p_struct<Span, PatternIrrefutable>, do_parse!(
    start: position!() >>
    id: p_identifier >>
    p_skip0 >>
    tag!("(") >>
    p_skip0 >>
    list: p_sid_list >>
    p_skip0 >>
    tag!(")") >>
    end: position!() >>
    (PatternIrrefutable::Struct(id, list, Position::new(start, end)))
));

named!(pub p_pattern_irrefutable<Span, PatternIrrefutable>, alt!(
    complete!(p_struct) | p_pattern_id | p_blank | p_ptr | p_ptr_mut | p_tuple
));

#[test]
fn test_pattern_irrefutable() {
    works_check!(p_pattern_irrefutable, "_a", 0, is_id);
    works_check!(p_pattern_irrefutable, "mut _a", 0, is_id);
    works_check!(p_pattern_irrefutable, "mut_a", 0, is_id);
    works_check!(p_pattern_irrefutable, "mut_", 0, is_id);

    works_check!(p_pattern_irrefutable, "_", 0, is_blank);
    fails!(p_pattern_irrefutable, "mut _");

    works_check!(p_pattern_irrefutable, "@a", 0, is_ptr);
    works_check!(p_pattern_irrefutable, "@~a", 0, is_ptr);

    works_check!(p_pattern_irrefutable, "~a", 0, is_ptr_mut);
    works_check!(p_pattern_irrefutable, "~@a", 0, is_ptr_mut);

    works_check!(p_pattern_irrefutable, "()", 0, is_tuple);
    works_check!(p_pattern_irrefutable, "(a)", 0, is_tuple);
    works_check!(p_pattern_irrefutable, "(a,b)", 0, is_tuple);
    works_check!(p_pattern_irrefutable, "(a=a,b=b)", 0, is_tuple);
    works_check!(p_pattern_irrefutable, "(#[foo]{a})", 0, is_tuple);
    works_check!(p_pattern_irrefutable, "(#[foo]{a},b)", 0, is_tuple);
    works_check!(p_pattern_irrefutable, "(#[foo]{a=#[foo]{a}},b=b)", 0, is_tuple);
    works_check!(p_pattern_irrefutable, "(mut a)", 0, is_tuple);
    works_check!(p_pattern_irrefutable, "(a,mut b)", 0, is_tuple);
    works_check!(p_pattern_irrefutable, "(a=a,b=mut b)", 0, is_tuple);
    works_check!(p_pattern_irrefutable, "(mut #[foo]{a})", 0, is_tuple);
    works_check!(p_pattern_irrefutable, "(mut #[foo]{a},b)", 0, is_tuple);
    works_check!(p_pattern_irrefutable, "(#[foo]{a=mut #[foo]{a}},b=b)", 0, is_tuple);
    not_complete!(p_pattern_irrefutable, "mut()");
    fails!(p_pattern_irrefutable, "(mut a=mut b)");

    works_check!(p_pattern_irrefutable, "s::t::u()", 0, is_struct);
    works_check!(p_pattern_irrefutable, "s(a)", 0, is_struct);
    works_check!(p_pattern_irrefutable, "s(a,b)", 0, is_struct);
    works_check!(p_pattern_irrefutable, "s(a=a,b=b)", 0, is_struct);
    works_check!(p_pattern_irrefutable, "s(#[foo]{a})", 0, is_struct);
    works_check!(p_pattern_irrefutable, "s(#[foo]{a},b)", 0, is_struct);
    works_check!(p_pattern_irrefutable, "s(#[foo]{a=#[foo]{a}},b=b)", 0, is_struct);
    works_check!(p_pattern_irrefutable, "s(mut a)", 0, is_struct);
    works_check!(p_pattern_irrefutable, "s(a,mut b)", 0, is_struct);
    works_check!(p_pattern_irrefutable, "s::t::u  (  a  ,  mut  b  )", 0, is_struct);
    works_check!(p_pattern_irrefutable, "s(a=a,b=mut b)", 0, is_struct);
    works_check!(p_pattern_irrefutable, "s(mut #[foo]{a})", 0, is_struct);
    works_check!(p_pattern_irrefutable, "s(mut #[foo]{a},b)", 0, is_struct);
    works_check!(p_pattern_irrefutable, "s(#[foo]{a=mut #[foo]{a}},b=b)", 0, is_struct);
}
