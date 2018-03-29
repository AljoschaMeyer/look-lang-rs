// Valid characters for simple identifiers: alphanumeric, `-`, `_`. Identifiers may not start with
// `-`. An identifier starting with `_` must have a length of at least 2. Maximum length of a
// simple identifier is 255.
//
// A qualified identifier is an identifier followed by `::` followed by a simple identifier.

#[derive(Debug, PartialEq, Eq)]
pub struct Identifier<'a> {
    pub first: &'a str, // a simple identifier
    pub remaining: Vec<(&'a str, &'a str)>, // first entry is the '::', second is the simple identifier
}

named!(pub simple_id<&str, &str>, re_find!("^_[[[:alnum:]]_-]{1,254}|^[[:alpha:]][[[:alnum:]]_-]{0,254}"));

named!(pub id<&str, Identifier>, do_parse!(
    first: simple_id >>
    remaining: many0!(pair!(tag!("::"), simple_id)) >>
    (Identifier {
        first: first,
        remaining: remaining
    })
));

#[test]
fn test_id() {
    works!(id, "aö", 2);
    works!(id, "a::_a::_-::t5ö", 2);

    fails!(id, "ä::a");
    works!(id, "a:a", 2);
    works!(id, "a::ä", 4);
    works!(id, "a::::b", 5);
    works!(id, "a::", 2);
    fails!(id, "::a");
    works!(id, "a::5", 3);
    works!(id, "a::_", 3);
    works!(id, "a::_::a", 6);
    works!(id, "a::a::_", 3);
    fails!(id, "_::a");
    works!(id, "a:: b", 4);
    works!(id, "a ::b", 4);
    works!(id, "a: :b", 4);
    fails!(id, " a");
}

#[test]
fn test_simple_id() {
    works!(simple_id, "_a", 0);
    works!(simple_id, "a", 0);
    works!(simple_id, "A", 0);
    works!(simple_id, "aA", 0);
    works!(simple_id, "__", 0);
    works!(simple_id, "_9", 0);
    works!(simple_id, "a9", 0);
    works!(simple_id, "_-", 0);
    works!(simple_id, "a-_9", 0);
    works_eq!(simple_id, "_aöa", "_a", 3);
    works!(simple_id,
           "abcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefg",
           0); // 255 characters

    works!(simple_id,
           "abcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefghabcdefgh",
           1); // 256 characters
    fails!(simple_id, "ö");
    fails!(simple_id, "_");
    fails!(simple_id, "-");
    fails!(simple_id, "9");
    fails!(simple_id, "9a");
    fails!(simple_id, "-a");
    fails!(simple_id, "");
}
