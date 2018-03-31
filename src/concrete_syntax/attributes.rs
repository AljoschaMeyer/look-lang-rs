// use super::identifiers::simple_id;
//
// #[derive(Debug, PartialEq, Eq)]
// pub enum Attribute<'a> {
//     Simple {
//         // #[foo]
//         hash_and_lbracket: &'a str,
//         id: &'a str,
//         rbracket: &'a str,
//     },
//     Nonsimple {
//         // #[foo(arbitrary non-empty stuff =,:][, but no parens)]
//         hash_and_lbracket: &'a str,
//         id: &'a str,
//         lparen: &'a str,
//         stuff: &'a str,
//         rparen_and_rbracket: &'a str,
//     },
// }
//
// named!(pub attribute<&str, Attribute>, do_parse!(
//     hash_and_lbracket: tag!("#[") >>
//     id: simple_id >>
//     ret: alt!(
//         do_parse!(
//             rbracket: tag!("]") >>
//             (Attribute::Simple {
//                 hash_and_lbracket: hash_and_lbracket,
//                 id: id,
//                 rbracket: rbracket
//             })
//         ) |
//         do_parse!(
//             lparen: tag!("(") >>
//             stuff: is_not!("()") >>
//             rparen_and_rbracket: tag!(")]") >>
//             (Attribute::Nonsimple {
//                 hash_and_lbracket: hash_and_lbracket,
//                 id: id,
//                 lparen: lparen,
//                 stuff: stuff,
//                 rparen_and_rbracket: rparen_and_rbracket
//             })
//         )
//     ) >>
//     (ret)
// ));
//
// #[test]
// fn test_attribute() {
//     works_eq!(attribute,
//               "#[foo]",
//               Attribute::Simple {
//                   hash_and_lbracket: "#[",
//                   id: "foo",
//                   rbracket: "]",
//               },
//               0);
//     works_eq!(attribute,
//               "#[foo(arbitrary non-empty stuff =,:][, but no parens)]",
//               Attribute::Nonsimple {
//                   hash_and_lbracket: "#[",
//                   id: "foo",
//                   lparen: "(",
//                   stuff: "arbitrary non-empty stuff =,:][, but no parens",
//                   rparen_and_rbracket: ")]",
//               },
//               0);
//
//     fails!(attribute, "#[foo()]");
//     fails!(attribute, "#[]");
//     fails!(attribute, "#[f f]");
//     fails!(attribute, "#[_]");
//     fails!(attribute, "#[foo(()]");
//     fails!(attribute, "#[foo())]");
//     fails!(attribute, "#[foo(())]");
// }
