use std::iter::Peekable;
use std::str::{Bytes, FromStr};
use std::num::ParseIntError;
use std::num::ParseFloatError;

pub fn tokenize(input: &str) -> Vec<Token> {
    Tokenizer::new(input).collect()
}

#[derive(Debug, PartialEq, Eq)]
pub struct Token(pub TokenType, pub SourceRange);

impl SourceRanged for Token {
    fn source_range(&self) -> SourceRange {
        self.1
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Position {
    pub line: usize,
    pub col: usize,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct SourceRange {
    pub from: Position,
    pub to: Position,
}

pub trait SourceRanged {
    /// Get the SourceRange of this value.
    fn source_range(&self) -> SourceRange;
}

#[derive(Debug, PartialEq)]
pub enum TokenType {
    At, // @
    Tilde, // ~
    Eq, // =
    LParen, // (
    RParen, // )
    LBracket, // [
    RBracket, // ]
    LBrace, // {
    RBrace, // }
    LAngle, // <
    RAngle, // >
    Comma, // ,
    Dollar, // $
    Hyphen, // -
    Colon, // :
    Semi, // ;
    Pipe, // |
    Scope, // ::
    Arrow, // ->
    FatArrow, // =>
    BeginAttribute, // #[
    Define, // :=
    Underscore, // _
    Id(String),
    Int(u64),
    Float(f64),
    String(String),
    Use,
    Mod,
    Selff,
    Super,
    Deps,
    Magic,
    Goto,
    Label,
    Break,
    Return,
    While,
    Match,
    If,
    Then,
    Else,
    Let,
    As,
    Type,
    Macro,
    Mut,
    UnexpectedByte(u8), // Encountered a byte that does not sigify the start of a token
    IncompleteBeginAttribute(u8), // A `#` not followed by a `[`
    IncompleteBeginLinecomment(u8), // A `/` not followed by a `/`
    InvalidDecInt(ParseIntError), // Encountered a decimal integer literal that could not be parsed into a u64
    InvalidBinInt(ParseIntError), // Encountered a binary integer literal that could not be parsed into a u64
    InvalidFloat(ParseFloatError), // Encountered a float literal that could not be parsed into an f64
    FloatEndsWithE, // Encountered partial float literal, ending with E
    FloatEndsWithSign, // Encountered partial float literal, ending with + or -
    IdTooLong, // Encountered an id of length >= 128
    UnexpectedEof, // String literal runs until end of file
    StringInvalidEscape,
}

impl Eq for TokenType {
    // Float literal never contains NaN, Inf or -Inf
}

pub struct Tokenizer<'a>(Peekable<_Tokenizer<'a>>);

impl<'a> Tokenizer<'a> {
    pub fn new(text: &'a str) -> Tokenizer<'a> {
        Tokenizer(_Tokenizer::new(text).peekable())
    }

    pub fn peek(&mut self) -> Option<&Token> {
        self.0.peek()
    }

    pub fn consume(&mut self, tt: TokenType) -> Result<Token, Option<Token>> {
        match self.next() {
            Some(token) => {
                if token.0 == tt {
                    Ok(token)
                } else {
                    Err(Some(token))
                }
            }
            None => Err(None),
        }
    }
}

impl<'a> Iterator for Tokenizer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

struct _Tokenizer<'a> {
    bytes: Peekable<Bytes<'a>>,
    line: usize,
    col: usize,
    state: Option<State>, // Never a `None`, but needed to keep the borrow checker happy...
}

impl<'a> _Tokenizer<'a> {
    fn new(text: &'a str) -> _Tokenizer<'a> {
        _Tokenizer {
            bytes: text.bytes().peekable(),
            line: 1,
            col: 1,
            state: Some(State::Default),
        }
    }

    fn token(&self, tt: TokenType, start_line: usize, start_col: usize) -> Token {
        Token(tt,
              SourceRange {
                  from: Position {
                      line: start_line,
                      col: start_col,
                  },
                  to: Position {
                      line: self.line,
                      col: self.col,
                  },
              })
    }

    fn next_byte(&mut self) -> Option<u8> {
        match self.bytes.next() {
            Some(b) => {
                if b == '\n' as u8 {
                    self.line += 1;
                    self.col = 1;
                } else {
                    self.col += 1;
                }
                Some(b)
            }
            None => None,
        }
    }

    fn peek(&mut self) -> Option<u8> {
        self.bytes.peek().map(|byte_ref| *byte_ref)
    }
}

impl<'a> Iterator for _Tokenizer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        let start_line = self.line;
        let start_col = self.col;

        let mut state = self.state.take().unwrap();

        loop {
            match state {
                State::Default => {
                    match self.next_byte() {
                        None => {return None;}
                        Some(64) /* @ */ => {
                            self.state = Some(State::Default);
                            return Some(self.token(TokenType::At, start_line, start_col));}
                        Some(126) /* ~ */ => {self.state = Some(State::Default);return Some(self.token(TokenType::Tilde, start_line, start_col));}
                        Some(40) /* ( */ => {self.state = Some(State::Default);return Some(self.token(TokenType::LParen, start_line, start_col));}
                        Some(41) /* 9 */ => {self.state = Some(State::Default);return Some(self.token(TokenType::RParen, start_line, start_col));}
                        Some(91) /* [ */ => {self.state = Some(State::Default);return Some(self.token(TokenType::LBracket, start_line, start_col));}
                        Some(93) /* ] */ => {self.state = Some(State::Default);return Some(self.token(TokenType::RBracket, start_line, start_col));}
                        Some(123) /* { */ => {self.state = Some(State::Default);return Some(self.token(TokenType::LBrace, start_line, start_col));}
                        Some(125) /* } */ => {self.state = Some(State::Default);return Some(self.token(TokenType::RBrace, start_line, start_col));}
                        Some(60) /* < */ => {self.state = Some(State::Default);return Some(self.token(TokenType::LAngle, start_line, start_col));}
                        Some(62) /* > */ => {self.state = Some(State::Default);return Some(self.token(TokenType::RAngle, start_line, start_col));}
                        Some(44) /* , */ => {self.state = Some(State::Default);return Some(self.token(TokenType::Comma, start_line, start_col));}
                        Some(36) /* $ */ => {self.state = Some(State::Default);return Some(self.token(TokenType::Dollar, start_line, start_col));}
                        Some(59) /* ; */ => {self.state = Some(State::Default);return Some(self.token(TokenType::Semi, start_line, start_col));}
                        Some(124) /* | */ => {self.state = Some(State::Default);return Some(self.token(TokenType::Pipe, start_line, start_col));}
                        Some(35) /* # */ => {
                            state = State::Hash {start_line, start_col}
                        }
                        Some(61) /* = */ => {
                            state = State::Eq {start_line, start_col}
                        }
                        Some(58) /* : */ => {
                            state = State::Colon {start_line, start_col}
                        }
                        Some(95) /* _ */ => {
                            state = State::Underscore {start_line, start_col}
                        }
                        Some(45) /* - */ => {
                            state = State::Hyphen {start_line, start_col}
                        }

                        Some(47) /* / */ => {
                            state = State::Slash {start_line, start_col}
                        }

                        Some(34) /* " */ => {
                            state = State::Quote {start_line, start_col}
                        }

                        Some(48) /* 0 */ => {
                            state = State::Zero {start_line, start_col}
                        }

                        Some(b@ 49 ... 57) /* [1-9] */ => {
                            state = State::DecInt {chars: vec![b], start_line, start_col}
                        }

                        Some(b@ 65 ... 90) | Some(b@ 97 ... 122) /* [A-Za-z] */ => {
                            state = State::Id {chars: vec![b], start_line, start_col}
                        }

                        Some(10) | Some(32) /* [\n ] */ => { /* no-op */}

                        Some(b) => {self.state = Some(State::Default);return Some(self.token(TokenType::UnexpectedByte(b), start_line, start_col));}
                    }
                }

                State::Hash {
                    start_line,
                    start_col,
                } => {
                    match self.peek() {
                        None => {
                            return None;
                        }
                        // [
                        Some(91) => {
                            self.state = Some(State::Default);
                            self.next_byte();
                            return Some(self.token(TokenType::BeginAttribute,
                                                   start_line,
                                                   start_col));
                        }
                        Some(b) => {
                            self.state = Some(State::Default);
                            return Some(self.token(TokenType::IncompleteBeginAttribute(b),
                                                   start_line,
                                                   start_col));
                        }
                    }
                }

                State::Eq {
                    start_line,
                    start_col,
                } => {
                    match self.peek() {
                        // >
                        Some(62) => {
                            self.state = Some(State::Default);
                            self.next_byte();
                            return Some(self.token(TokenType::FatArrow, start_line, start_col));
                        }
                        None | Some(_) => {
                            self.state = Some(State::Default);
                            return Some(self.token(TokenType::Eq, start_line, start_col));
                        }
                    }
                }

                State::Colon {
                    start_line,
                    start_col,
                } => {
                    match self.peek() {
                        // :
                        Some(58) => {
                            self.state = Some(State::Default);
                            self.next_byte();
                            return Some(self.token(TokenType::Scope, start_line, start_col));
                        }
                        // =
                        Some(61) => {
                            self.state = Some(State::Default);
                            self.next_byte();
                            return Some(self.token(TokenType::Define, start_line, start_col));
                        }
                        None | Some(_) => {
                            self.state = Some(State::Default);
                            return Some(self.token(TokenType::Colon, start_line, start_col));
                        }
                    }
                }

                State::Hyphen {
                    start_line,
                    start_col,
                } => {
                    match self.peek() {
                        // >
                        Some(62) => {
                            self.state = Some(State::Default);
                            self.next_byte();
                            return Some(self.token(TokenType::Arrow, start_line, start_col));
                        }
                        None | Some(_) => {
                            self.state = Some(State::Default);
                            return Some(self.token(TokenType::Hyphen, start_line, start_col));
                        }
                    }
                }

                State::Slash {
                    start_line,
                    start_col,
                } => {
                    match self.peek() {
                        None => {
                            return None;
                        }
                        // /
                        Some(47) => {
                            state = State::Comment;
                            self.next_byte();
                        }
                        Some(b) => {
                            self.state = Some(State::Default);
                            return Some(self.token(TokenType::IncompleteBeginLinecomment(b),
                                                   start_line,
                                                   start_col));
                        }
                    }
                }

                State::Comment => {
                    match self.next_byte() {
                        None => {
                            return None;
                        }
                        // \n
                        Some(10) => state = State::Default,
                        Some(_) => { /* no-op */ }
                    }
                }

                State::Underscore {
                    start_line,
                    start_col,
                } => {
                    match self.peek() {
                        // [0-9A-Za-z_]
                        Some(b @ 48...57) |
                        Some(b @ 65...90) |
                        Some(b @ 97...122) |
                        Some(b @ 95) => {
                            state = State::Id {
                                chars: vec![95, b],
                                start_line,
                                start_col,
                            };
                            self.next_byte();
                        }
                        None | Some(_) => {
                            self.state = Some(State::Default);
                            return Some(self.token(TokenType::Underscore, start_line, start_col));
                        }
                    }
                }

                State::Id {
                    ref mut chars,
                    start_line,
                    start_col,
                } => {
                    match self.peek() {
                        // [0-9A-Za-z_]
                        Some(b @ 48...57) |
                        Some(b @ 65...90) |
                        Some(b @ 97...122) |
                        Some(b @ 95) => {
                            chars.push(b);
                            self.next_byte();
                        }
                        None | Some(_) => {
                            self.state = Some(State::Default);

                            if chars[..] == b"use"[..] {
                                return Some(self.token(TokenType::Use, start_line, start_col));
                            } else if chars[..] == b"mod"[..] {
                                return Some(self.token(TokenType::Mod, start_line, start_col));
                            } else if chars[..] == b"self"[..] {
                                return Some(self.token(TokenType::Selff, start_line, start_col));
                            } else if chars[..] == b"super"[..] {
                                return Some(self.token(TokenType::Super, start_line, start_col));
                            } else if chars[..] == b"deps"[..] {
                                return Some(self.token(TokenType::Deps, start_line, start_col));
                            } else if chars[..] == b"magic"[..] {
                                return Some(self.token(TokenType::Magic, start_line, start_col));
                            } else if chars[..] == b"goto"[..] {
                                return Some(self.token(TokenType::Goto, start_line, start_col));
                            } else if chars[..] == b"label"[..] {
                                return Some(self.token(TokenType::Label, start_line, start_col));
                            } else if chars[..] == b"break"[..] {
                                return Some(self.token(TokenType::Break, start_line, start_col));
                            } else if chars[..] == b"return"[..] {
                                return Some(self.token(TokenType::Return, start_line, start_col));
                            } else if chars[..] == b"while"[..] {
                                return Some(self.token(TokenType::While, start_line, start_col));
                            } else if chars[..] == b"match"[..] {
                                return Some(self.token(TokenType::Match, start_line, start_col));
                            } else if chars[..] == b"if"[..] {
                                return Some(self.token(TokenType::If, start_line, start_col));
                            } else if chars[..] == b"then"[..] {
                                return Some(self.token(TokenType::Then, start_line, start_col));
                            } else if chars[..] == b"else"[..] {
                                return Some(self.token(TokenType::Else, start_line, start_col));
                            } else if chars[..] == b"let"[..] {
                                return Some(self.token(TokenType::Let, start_line, start_col));
                            } else if chars[..] == b"as"[..] {
                                return Some(self.token(TokenType::As, start_line, start_col));
                            } else if chars[..] == b"type"[..] {
                                return Some(self.token(TokenType::Type, start_line, start_col));
                            } else if chars[..] == b"macro"[..] {
                                return Some(self.token(TokenType::Macro, start_line, start_col));
                            } else if chars[..] == b"mut"[..] {
                                return Some(self.token(TokenType::Mut, start_line, start_col));
                            } else if chars.len() >= 128 {
                                return Some(self.token(TokenType::IdTooLong,
                                                       start_line,
                                                       start_col));
                            } else {
                                return Some(self.token(TokenType::Id(unsafe {String::from_utf8_unchecked(chars.clone())}),
                                                       start_line,
                                                       start_col));
                            }
                        }
                    }
                }

                State::Zero {
                    start_line,
                    start_col,
                } => {
                    match self.peek() {
                        // b
                        Some(98) => {
                            state = State::BinInt {
                                chars: vec![],
                                start_line,
                                start_col,
                            };
                            self.next_byte();
                        }

                        // [0-9]
                        Some(b @ 48...57) => {
                            state = State::DecInt {
                                chars: vec![48, b],
                                start_line,
                                start_col,
                            };
                            self.next_byte();
                        }

                        // .
                        Some(46) => {
                            state = State::Float {
                                chars: vec![48, 46],
                                start_line,
                                start_col,
                            };
                            self.next_byte();
                        }

                        None | Some(_) => {
                            self.state = Some(State::Default);
                            return Some(self.token(TokenType::Int(0), start_line, start_col));
                        }
                    }
                }

                State::DecInt {
                    ref mut chars,
                    start_line,
                    start_col,
                } => {
                    match self.peek() {
                        // [0-9]
                        Some(b @ 48...57) => {
                            chars.push(b);
                            self.next_byte();
                        }

                        // _
                        Some(95) => {
                            self.next_byte();
                        }

                        // .
                        Some(46) => {
                            chars.push(46);
                            self.state = Some(State::Float {
                                                  chars: chars.clone(),
                                                  start_line,
                                                  start_col,
                                              });
                            self.next_byte();
                            return self.next();
                        }

                        None | Some(_) => {
                            self.state = Some(State::Default);
                            match u64::from_str_radix(unsafe {
                                                          &String::from_utf8_unchecked(chars.clone())
                                                      },
                                                      10) {
                                Ok(int) => {
                                    return Some(self.token(TokenType::Int(int),
                                                           start_line,
                                                           start_col));
                                }
                                Err(err) => {
                                    return Some(self.token(TokenType::InvalidDecInt(err),
                                                           start_line,
                                                           start_col));
                                }
                            }
                        }
                    }
                }

                State::BinInt {
                    ref mut chars,
                    start_line,
                    start_col,
                } => {
                    match self.peek() {
                        // [01]
                        Some(b @ 48) | Some(b @ 49) => {
                            chars.push(b);
                            self.next_byte();
                        }

                        // _
                        Some(95) => {
                            self.next_byte();
                        }

                        None | Some(_) => {
                            self.state = Some(State::Default);
                            match u64::from_str_radix(unsafe {
                                                          &String::from_utf8_unchecked(chars.clone())
                                                      },
                                                      2) {
                                Ok(int) => {
                                    return Some(self.token(TokenType::Int(int),
                                                           start_line,
                                                           start_col));
                                }
                                Err(err) => {
                                    return Some(self.token(TokenType::InvalidBinInt(err),
                                                           start_line,
                                                           start_col));
                                }
                            }
                        }
                    }
                }

                State::Float {
                    ref mut chars,
                    start_line,
                    start_col,
                } => {
                    match self.peek() {
                        // [0-9]
                        Some(b @ 48...57) => {
                            chars.push(b);
                            self.next_byte();
                        }

                        // _
                        Some(95) => {
                            self.next_byte();
                        }

                        // E
                        Some(69) => {
                            chars.push(69);
                            self.state = Some(State::FloatExpMaybeSign {
                                                  chars: chars.clone(),
                                                  start_line,
                                                  start_col,
                                              });
                            self.next_byte();
                            return self.next();
                        }

                        None | Some(_) => {
                            self.state = Some(State::Default);
                            match f64::from_str(unsafe {
                                                          &String::from_utf8_unchecked(chars.clone())
                                                      }) {
                                Ok(float) => {
                                    return Some(self.token(TokenType::Float(float),
                                                           start_line,
                                                           start_col));
                                }
                                Err(err) => {
                                    return Some(self.token(TokenType::InvalidFloat(err),
                                                           start_line,
                                                           start_col));
                                }
                            }
                        }
                    }
                }

                State::FloatExpMaybeSign {
                    ref mut chars,
                    start_line,
                    start_col,
                } => {
                    match self.peek() {
                        // [0-9]
                        Some(b @ 48...57) => {
                            chars.push(b);
                            self.state = Some(State::FloatExp {
                                                  chars: chars.clone(),
                                                  start_line,
                                                  start_col,
                                              });
                            self.next_byte();
                            return self.next();
                        }

                        // [+-]
                        Some(b @ 43) | Some(b @ 45) => {
                            chars.push(b);
                            self.state = Some(State::FloatExpAfterSign {
                                                  chars: chars.clone(),
                                                  start_line,
                                                  start_col,
                                              });
                            self.next_byte();
                            return self.next();
                        }

                        // _
                        Some(95) => {
                            self.state = Some(State::FloatExp {
                                                  chars: chars.clone(),
                                                  start_line,
                                                  start_col,
                                              });
                            self.next_byte();
                            return self.next();
                        }

                        None | Some(_) => {
                            self.state = Some(State::Default);
                            return Some(self.token(TokenType::FloatEndsWithE,
                                                   start_line,
                                                   start_col));
                        }
                    }
                }

                State::FloatExpAfterSign {
                    ref mut chars,
                    start_line,
                    start_col,
                } => {
                    match self.peek() {
                        // [0-9]
                        Some(b @ 48...57) => {
                            chars.push(b);
                            self.state = Some(State::FloatExp {
                                                  chars: chars.clone(),
                                                  start_line,
                                                  start_col,
                                              });
                            self.next_byte();
                            return self.next();
                        }

                        // _
                        Some(95) => {
                            self.state = Some(State::FloatExp {
                                                  chars: chars.clone(),
                                                  start_line,
                                                  start_col,
                                              });
                            self.next_byte();
                            return self.next();
                        }

                        None | Some(_) => {
                            self.state = Some(State::Default);
                            return Some(self.token(TokenType::FloatEndsWithSign,
                                                   start_line,
                                                   start_col));
                        }
                    }
                }

                State::FloatExp {
                    ref mut chars,
                    start_line,
                    start_col,
                } => {
                    match self.peek() {
                        // [0-9]
                        Some(b @ 48...57) => {
                            chars.push(b);
                            self.next_byte();
                        }

                        // _
                        Some(95) => {
                            self.next_byte();
                        }

                        None | Some(_) => {
                            self.state = Some(State::Default);
                            match f64::from_str(unsafe {
                                                          &String::from_utf8_unchecked(chars.clone())
                                                      }) {
                                Ok(float) => {
                                    return Some(self.token(TokenType::Float(float),
                                                           start_line,
                                                           start_col));
                                }
                                Err(err) => {
                                    return Some(self.token(TokenType::InvalidFloat(err),
                                                           start_line,
                                                           start_col));
                                }
                            }
                        }
                    }
                }

                State::Quote {
                    start_line,
                    start_col,
                } => {
                    match self.next_byte() {
                        None => {
                            return Some(self.token(TokenType::UnexpectedEof,
                                                   start_line,
                                                   start_col));
                        }

                        // \
                        Some(92) => {
                            state = State::StringBackslash {
                                chars: "".to_string(),
                                start_line,
                                start_col,
                            };
                        }

                        // "
                        Some(34) => {
                            self.state = Some(State::Default);
                            return Some(self.token(TokenType::String("".to_string()),
                                                   start_line,
                                                   start_col));
                        }

                        Some(b) => {
                            let mut s = "".to_string();
                            unsafe {
                                s.as_mut_vec().push(b);
                            }
                            state = State::String {
                                chars: s,
                                start_line,
                                start_col,
                            };
                        }
                    }
                }

                State::String {
                    ref mut chars,
                    start_line,
                    start_col,
                } => {
                    match self.next_byte() {
                        None => {
                            return Some(self.token(TokenType::UnexpectedEof,
                                                   start_line,
                                                   start_col));
                        }

                        // \
                        Some(92) => {
                            self.state = Some(State::StringBackslash {
                                                  chars: chars.clone(),
                                                  start_line,
                                                  start_col,
                                              });
                            return self.next();
                        }

                        // "
                        Some(34) => {
                            self.state = Some(State::Default);
                            return Some(self.token(TokenType::String(chars.clone()),
                                                   start_line,
                                                   start_col));
                        }

                        Some(b) => unsafe {
                            chars.as_mut_vec().push(b);
                        },
                    }
                }

                State::StringBackslash {
                    ref mut chars,
                    start_line,
                    start_col,
                } => {
                    match self.peek() {
                        None => {
                            return Some(self.token(TokenType::UnexpectedEof,
                                                   start_line,
                                                   start_col));
                        }

                        // \
                        Some(92) => {
                            self.next_byte();
                            unsafe {
                                chars.as_mut_vec().push(92);
                            }
                            self.state = Some(State::String {
                                                  chars: chars.clone(),
                                                  start_line,
                                                  start_col,
                                              });
                            return self.next();
                        }

                        // "
                        Some(34) => unsafe {
                            self.next_byte();
                            chars.as_mut_vec().push(34);
                            self.state = Some(State::String {
                                                  chars: chars.clone(),
                                                  start_line,
                                                  start_col,
                                              });
                            return self.next();
                        },

                        // n
                        Some(110) => unsafe {
                            self.next_byte();
                            chars.as_mut_vec().push(10);
                            self.state = Some(State::String {
                                                  chars: chars.clone(),
                                                  start_line,
                                                  start_col,
                                              });
                            return self.next();
                        },

                        // t
                        Some(116) => unsafe {
                            self.next_byte();
                            chars.as_mut_vec().push(9);
                            self.state = Some(State::String {
                                                  chars: chars.clone(),
                                                  start_line,
                                                  start_col,
                                              });
                            return self.next();
                        },

                        // 0
                        Some(48) => unsafe {
                            self.next_byte();
                            chars.as_mut_vec().push(0);
                            self.state = Some(State::String {
                                                  chars: chars.clone(),
                                                  start_line,
                                                  start_col,
                                              });
                            return self.next();
                        },

                        // x
                        Some(120) => {
                            self.next_byte();
                            self.state = Some(State::StringEscapeXFirst {
                                                  chars: chars.clone(),
                                                  start_line,
                                                  start_col,
                                              });
                            return self.next();
                        }

                        Some(_) => {
                            self.state = Some(State::String {
                                                  chars: chars.clone(),
                                                  start_line,
                                                  start_col,
                                              });
                            return Some(self.token(TokenType::StringInvalidEscape,
                                                   start_line,
                                                   start_col));
                        }
                    }
                }

                State::StringEscapeXFirst {
                    chars,
                    start_line,
                    start_col,
                } => {
                    match self.next_byte() {
                        None => {
                            return Some(self.token(TokenType::UnexpectedEof,
                                                   start_line,
                                                   start_col));
                        }

                        // [0-7]
                        Some(b @ 48...55) => {
                            self.state = Some(State::StringEscapeXSecond {
                                                  chars: chars,
                                                  prev: b,
                                                  start_line,
                                                  start_col,
                                              });
                            return self.next();
                        }

                        Some(_) => {
                            self.state = Some(State::String {
                                                  chars,
                                                  start_line,
                                                  start_col,
                                              });
                            return Some(self.token(TokenType::StringInvalidEscape,
                                                   start_line,
                                                   start_col));
                        }
                    }
                }

                State::StringEscapeXSecond {
                    ref mut chars,
                    prev,
                    start_line,
                    start_col,
                } => {
                    match self.next_byte() {
                        None => {
                            return Some(self.token(TokenType::UnexpectedEof,
                                                   start_line,
                                                   start_col));
                        }

                        // [0-9A-F]
                        Some(b @ 48...57) |
                        Some(b @ 65...70) => {
                            let escaped =
                                u8::from_str_radix(unsafe {
                                                       &String::from_utf8_unchecked(vec![prev, b])
                                                   },
                                                   16)
                                        .unwrap();


                            unsafe {
                                chars.as_mut_vec().push(escaped);
                            }

                            self.state = Some(State::String {
                                                  chars: chars.clone(),
                                                  start_line,
                                                  start_col,
                                              });
                            return self.next();
                        }

                        Some(_) => {
                            self.state = Some(State::String {
                                                  chars: chars.clone(),
                                                  start_line,
                                                  start_col,
                                              });
                            return Some(self.token(TokenType::StringInvalidEscape,
                                                   start_line,
                                                   start_col));
                        }
                    }
                }

            }
        }
    }
}

enum State {
    Default,
    Hash { start_line: usize, start_col: usize }, // #[
    Hyphen { start_line: usize, start_col: usize }, // ->
    Slash { start_line: usize, start_col: usize }, // //
    Comment, // ignore until \n (inclusive)
    Eq { start_line: usize, start_col: usize }, // = or =>
    Colon { start_line: usize, start_col: usize }, // :, :: or :=
    Underscore { start_line: usize, start_col: usize }, // blank pattern or identifier start
    Id {
        chars: Vec<u8>,
        start_line: usize,
        start_col: usize,
    },
    Zero { start_line: usize, start_col: usize }, // binary or decimal integer literal, or float literal
    DecInt {
        chars: Vec<u8>,
        start_line: usize,
        start_col: usize,
    }, // decimal literal or float literal
    BinInt {
        chars: Vec<u8>,
        start_line: usize,
        start_col: usize,
    },
    Float {
        chars: Vec<u8>,
        start_line: usize,
        start_col: usize,
    },
    FloatExpMaybeSign {
        chars: Vec<u8>,
        start_line: usize,
        start_col: usize,
    },
    FloatExpAfterSign {
        chars: Vec<u8>,
        start_line: usize,
        start_col: usize,
    },
    FloatExp {
        chars: Vec<u8>,
        start_line: usize,
        start_col: usize,
    },
    Quote { start_line: usize, start_col: usize }, // string literal start
    String {
        chars: String,
        start_line: usize,
        start_col: usize,
    },
    StringBackslash {
        chars: String,
        start_line: usize,
        start_col: usize,
    },
    StringEscapeXFirst {
        chars: String,
        start_line: usize,
        start_col: usize,
    },
    StringEscapeXSecond {
        chars: String,
        prev: u8,
        start_line: usize,
        start_col: usize,
    },
}

#[cfg(test)]
fn assert_same_token_types(tok: Vec<Token>, types: Vec<TokenType>) -> bool {
    for (i, t) in tok.iter().enumerate() {
        if t.0 != types[i] {
            println!("Unexpected token at index {:?}", i);
            panic!("Expected {:?}, got {:?}", types[i], t.0);
        }
    }
    true
}

#[test]
fn test_tokenizer() {
    let tok = Tokenizer::new("@  =~ \n ( )[]{}<>,$:;|::->=>#[:=_");
    assert_same_token_types(tok.collect::<Vec<Token>>(),
                            vec![TokenType::At,
                                 TokenType::Eq,
                                 TokenType::Tilde,
                                 TokenType::LParen,
                                 TokenType::RParen,
                                 TokenType::LBracket,
                                 TokenType::RBracket,
                                 TokenType::LBrace,
                                 TokenType::RBrace,
                                 TokenType::LAngle,
                                 TokenType::RAngle,
                                 TokenType::Comma,
                                 TokenType::Dollar,
                                 TokenType::Colon,
                                 TokenType::Semi,
                                 TokenType::Pipe,
                                 TokenType::Scope,
                                 TokenType::Arrow,
                                 TokenType::FatArrow,
                                 TokenType::BeginAttribute,
                                 TokenType::Define,
                                 TokenType::Underscore]);

    let tok = Tokenizer::new("@//@\n~//æöŋ\n=//\t\r\n(");
    assert_same_token_types(tok.collect::<Vec<Token>>(),
                            vec![TokenType::At,
                                 TokenType::Tilde,
                                 TokenType::Eq,
                                 TokenType::LParen]);

    let tok = Tokenizer::new("abc __ _9 a_b _a a_ use mod self super deps magic goto label break return while match if then else let as type macro mut abcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFG abcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGH");
    assert_same_token_types(tok.collect::<Vec<Token>>(),
                            vec![TokenType::Id("abc".to_string()),
                                TokenType::Id("__".to_string()),
                                TokenType::Id("_9".to_string()),
                                TokenType::Id("a_b".to_string()),
                                TokenType::Id("_a".to_string()),
                                TokenType::Id("a_".to_string()),
                                 TokenType::Use,
                                 TokenType::Mod,
                                 TokenType::Selff,
                                 TokenType::Super,
                                 TokenType::Deps,
                                 TokenType::Magic,
                                 TokenType::Goto,
                                 TokenType::Label,
                                 TokenType::Break,
                                 TokenType::Return,
                                 TokenType::While,
                                 TokenType::Match,
                                 TokenType::If,
                                 TokenType::Then,
                                 TokenType::Else,
                                 TokenType::Let,
                                 TokenType::As,
                                 TokenType::Type,
                                 TokenType::Macro,
                                 TokenType::Mut,
                                 TokenType::Id("abcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFG".to_string()),
                                 TokenType::IdTooLong]);

    let tok = Tokenizer::new("0 12345 123_123 1_ 0b10_01");
    assert_same_token_types(tok.collect::<Vec<Token>>(),
                            vec![TokenType::Int(0),
                                 TokenType::Int(12345),
                                 TokenType::Int(123123),
                                 TokenType::Int(1),
                                 TokenType::Int(0b10_01)]);

    let tok = Tokenizer::new("1.2 1.2E3 1.2E+3 1.2E-3 1_._12_E+__3__5_");
    assert_same_token_types(tok.collect::<Vec<Token>>(),
                            vec![TokenType::Float(1.2),
                                 TokenType::Float(1.2E3),
                                 TokenType::Float(1.2E+3),
                                 TokenType::Float(1.2E-3),
                                 TokenType::Float(1_.12_E+__3__5_)]);

    let tok = Tokenizer::new(r#" "" "a" "'" "abc" "öäü" "💂🏾" "\"" "\\" "\n" "\t" "\0" "\x00" "\x7F" "#);
    assert_same_token_types(tok.collect::<Vec<Token>>(),
                            vec![TokenType::String("".to_string()),
                                 TokenType::String("a".to_string()),
                                 TokenType::String("'".to_string()),
                                 TokenType::String("abc".to_string()),
                                 TokenType::String("öäü".to_string()),
                                 TokenType::String("💂🏾".to_string()),
                                 TokenType::String("\"".to_string()),
                                 TokenType::String("\\".to_string()),
                                 TokenType::String("\n".to_string()),
                                 TokenType::String("\t".to_string()),
                                 TokenType::String("\0".to_string()),
                                 TokenType::String("\x00".to_string()),
                                 TokenType::String("\x7F".to_string())]);
}
