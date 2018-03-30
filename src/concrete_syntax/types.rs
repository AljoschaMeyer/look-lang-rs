use super::attributes::{Attribute, attribute as p_attribute};
use super::whitespace::{Ignored, ignored0 as p_ignored0, ignored1 as p_ignored1};

#[derive(Debug, PartialEq, Eq)]
pub enum Type<'a> {
    Void(&'a str),
    Ptr(&'a str, Box<Type<'a>>),
    Array(&'a str, Box<Type<'a>>, &'a str),
    Attributed {
        attribute: Attribute<'a>,
        space: &'a str,
        lbrace: &'a str,
        ignored0: Ignored<'a>,
        inner: Box<Type<'a>>,
        ignored1: Ignored<'a>,
        rbrace: &'a str,
    },
    ProductRepeated {
        lparen: &'a str,
        ignored0: Ignored<'a>,
        inner: Box<Type<'a>>,
        semi_and_space: &'a str,
        size: &'a str,
        ignored1: Ignored<'a>,
        rparen: &'a str,
    },
    ProductAnon {
        lparen: &'a str,
        ignored0: Ignored<'a>,
        first: Option<Box<Type<'a>>>,
        remaining: Vec<(&'a str, Ignored<'a>, Type<'a>)>,
        ignored1: Ignored<'a>,
        rparen: &'a str,
    },
}

named!(void<&str, Type>, map!(tag!("!"), Type::Void));
named!(ptr<&str, Type>, do_parse!(
    at: tag!("@") >>
    inner: p_type >>
    (Type::Ptr(at, Box::new(inner)))
));
named!(array<&str, Type>, do_parse!(
    start: tag!("[") >>
    inner: p_type >>
    end: tag!("]") >>
    (Type::Array(start, Box::new(inner), end))
));
named!(attr<&str, Type>, do_parse!(
    attribute: p_attribute >>
    space: tag!(" ") >>
    lbrace: tag!("{") >>
    ignored0: p_ignored1 >>
    inner: p_type >>
    ignored1: p_ignored1 >>
    rbrace: tag!("}") >>
    (Type::Attributed {
        attribute: attribute,
        space: space,
        lbrace: lbrace,
        ignored0: ignored0,
        inner: Box::new(inner),
        ignored1: ignored1,
        rbrace: rbrace
    })
));
// named!(lparen_type<&str, Type>, do_parse!(
//     lparen: tag!("(") >>
//     ignored0: p_ignored0 >>
//     ret: alt!(
//         do_parse!(
//             inner: p_type >>
//             semi_and_space: tag!("; ") >>
//             size: is_a!("0123456789") >>
//             ignored1: p_ignored0 >>
//             rparen: tag!(")") >>
//             (Type::ProductRepeated {
//                 lparen: lparen,
//                 ignored0: ignored0,
//                 inner: Box::new(inner),
//                 semi_and_space: semi_and_space,
//                 size: size,
//                 ignored1: ignored1,
//                 rparen: rparen
//             })
//         ) |
//         do_parse!(
//
//         )
//     ) >>
//     (ret)
// ));

named!(pub p_type<&str, Type>, alt!(
    void | ptr | array | attr// | lparen_type
));

#[test]
fn test_type() {
    works_eq!(p_type, "!ö", Type::Void("!"), 2);

    works_eq!(p_type, "@!", Type::Ptr("@", Box::new(Type::Void("!"))), 0);

    works_eq!(p_type,
              "[!]",
              Type::Array("[", Box::new(Type::Void("!")), "]"),
              0);
    fails!(p_type, "[!ö]");

    works!(p_type, "#[foo] { ! }", 0);
    fails!(p_type, "#[foo]{ ! }");
    fails!(p_type, "#[foo]  { ! }");
    fails!(p_type, "#[foo] {! }");
    fails!(p_type, "#[foo] { !}");

    works_eq!(p_type,
              "(!; 42)",
              Type::ProductRepeated {
                  lparen: "(",
                  ignored0: Ignored(vec![]),
                  inner: Box::new(Type::Void("!")),
                  semi_and_space: "; ",
                  size: "42",
                  ignored1: Ignored(vec![]),
                  rparen: ")",
              },
              0);
    works!(p_type, "( !; 42)", 0);
    fails!(p_type, "(! ; 42)");
    fails!(p_type, "(!;42)");
    fails!(p_type, "(!;  42)");
    works!(p_type, "(!; 42 )", 0);
    fails!(p_type, "(!; 0b11)");

    // works_eq!(p_type,
    //           "()",
    //           Type::ProductAnon {
    //               lparen: "(",
    //               ignored0: Ignored(vec![]),
    //               first: None,
    //               remaining: vec![],
    //               ignored1: Ignored(vec![]),
    //               rparen: ")",
    //           },
    //           0);
    // should work: ( ), (!), (!, !), (  !,  !  )
    // should fail: (! ,!)
}
