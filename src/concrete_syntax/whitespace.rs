#[derive(Debug, PartialEq, Eq)]
pub struct Ignored<'a>(pub Vec<IgnoredItem<'a>>);

#[derive(Debug, PartialEq, Eq)]
pub enum IgnoredItem<'a> {
    Whitespace(&'a str),
    LineComment(&'a str),
}

// Whitespace (only space (U+0020) or \n are allowed)
// named!(ws_many_0<&str, &str>, re_find!("^[ \\n]*"));
named!(ws_many_1<&str, &str>, re_find!("^[ \\n]+"));

/// First slice is the `//`, second slice is the remaining text (including the linebreak)
named!(line_comment<&str, &str>, re_find!("^//[^\n]*\n"));

named!(ignored_item<&str, IgnoredItem>, alt!(
    map!(ws_many_1, IgnoredItem::Whitespace) |
    map!(line_comment, IgnoredItem::LineComment)
));

named!(pub ignored0<&str, Ignored>, map!(many0!(ignored_item), Ignored));
named!(pub ignored1<&str, Ignored>, map!(many1!(ignored_item), Ignored));

#[test]
fn test_ignored() {
    fails!(ignored1, "");
    fails!(ignored1, "a");
    works_eq!(ignored0, "", Ignored(vec![]), 0);
    works!(ignored0, "a", 1);

    fails!(ignored1, "\r");
    fails!(ignored1, "\t");

    fails!(line_comment, "//");

    works!(ignored1, "//\n", 0);
    works!(line_comment, "// \n", 0);
    works!(ignored1, "///\n", 0);
    works!(ignored1, "////\n", 0);
    works!(ignored1, "//\n//\n", 0);
    works!(ignored1, "//\na", 1);
    works!(ignored0, "// \rö\n   /// /\n /", 1);
}
