#[derive(Debug, PartialEq, Eq)]
pub enum Type<'a> {
    Void(&'a str),
}

named!(void<&str, Type>, map!(tag!("!"), Type::Void));

#[test]
fn test_type() {
    works_eq!(void, "!ö", Type::Void("!"), 2);
}
