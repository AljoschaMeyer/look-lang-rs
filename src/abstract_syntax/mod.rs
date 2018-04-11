//! An abstract syntax tree with line/column markers, which owns its data.
use nom_locate::LocatedSpan;
use nom::AsBytes;

type Span<'a> = LocatedSpan<&'a str>;

/// A position in the input. Lines and columns start at 1.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Position {
    start_line: u32,
    start_col: usize,
    end_line: u32,
    end_col: usize,
}

impl Position {
    pub fn from_positions(start: Position, end: Position) -> Position {
        Position {
            start_line: start.start_line,
            start_col: start.start_col,
            end_line: end.end_line,
            end_col: end.end_col,
        }
    }

    fn new<T: AsBytes>(start: LocatedSpan<T>, end: LocatedSpan<T>) -> Position {
        Position {
            start_line: start.line,
            start_col: start.get_column_utf8().unwrap(),
            end_line: end.line,
            end_col: end.get_column_utf8().unwrap(),
        }
    }

    pub fn start_line(&self) -> u32 {
        self.start_line
    }

    pub fn start_col(&self) -> usize {
        self.start_col
    }

    pub fn end_line(&self) -> u32 {
        self.end_line
    }

    pub fn end_col(&self) -> usize {
        self.end_col
    }
}

#[cfg(test)]
macro_rules! works {
    ($parser:expr, $input:expr, $exp:expr) => {
        {
            if let ::nom::IResult::Done(i, _) = $parser(::nom_locate::LocatedSpan::new($input)) {
                assert!(i.fragment.len() == $exp);
            } else {
                panic!("parser did not succeed");
            }
        }
    }
}

#[cfg(test)]
macro_rules! works_check {
    ($parser:expr, $input:expr, $exp:expr, $check:pat) => {
        {
            if let ::nom::IResult::Done(i, o) = $parser(::nom_locate::LocatedSpan::new($input)) {
                assert!(i.fragment.len() == $exp);
                match o {
                    $check => {},
                    _ => {
                        panic!("parser did not return the correct enum variant");
                    }
                }
            } else {
                panic!("parser did not succeed");
            }
        }
    }
}

#[cfg(test)]
macro_rules! fails {
    ($parser:expr, $input:expr) => {
        {
            if let ::nom::IResult::Done(_, _) = $parser(::nom_locate::LocatedSpan::new($input)) {
                panic!("parser succeeded");
            }
        }
    }
}

#[cfg(test)]
macro_rules! not_complete {
    ($parser:expr, $input:expr) => {
        {
            if let ::nom::IResult::Done(i, _) = $parser(::nom_locate::LocatedSpan::new($input)) {
                assert!(i.fragment.len() > 0);
            }
        }
    }
}

named!(pub p_skip0<Span, ()>, map!(
    many0!(alt!(
        map!(one_of!(" \n"), |_| ()) |
        do_parse!(
            tag!("//") >>
            many0!(none_of!("\n")) >>
            tag!("\n") >>
            (())
        )
    )), |_| ()));

named!(pub p_skip1<Span, ()>, map!(
    many1!(alt!(
        map!(one_of!(" \n"), |_| ()) |
        do_parse!(
            tag!("//") >>
            many0!(none_of!("\n")) >>
            tag!("\n") >>
            (())
        )
    )), |_| ()));

#[test]
fn test_ignored() {
    fails!(p_skip1, "");
    fails!(p_skip1, "a");
    works!(p_skip0, "", 0);
    works!(p_skip0, "a", 1);

    fails!(p_skip1, "\r");
    fails!(p_skip1, "\t");

    fails!(p_skip0, "//");

    works!(p_skip1, "//\n", 0);
    works!(p_skip1, "// \n", 0);
    works!(p_skip1, "///\n", 0);
    works!(p_skip1, "////\n", 0);
    works!(p_skip1, "//\n//\n", 0);
    works!(p_skip1, "//\na", 1);
    works!(p_skip0, "// \rö\n   /// /\n a", 1);
}

pub mod ast;
// pub mod attributes;
// pub mod const_expressions;
// pub mod expressions;
// pub mod identifiers;
// pub mod irrefutable_patterns;
// pub mod patterns;
// pub mod types;

pub mod tokenizer;
