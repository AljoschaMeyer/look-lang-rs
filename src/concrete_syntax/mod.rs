#[cfg(test)]
macro_rules! works {
    ($parser:expr, $input:expr, $exp:expr) => {
        {
            if let Ok((i, _o)) = $parser($input) {
                assert!(i.len() == $exp);
            } else {
                panic!("parser did not succeed");
            }
        }
    }
}

#[cfg(test)]
macro_rules! works_eq {
    ($parser:expr, $input:expr, $exp:expr, $len:expr) => {
        {
            if let Ok((i, o)) = $parser($input) {
                assert_eq!(o, $exp);
                assert!(i.len() == $len);
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
            assert!($parser($input).is_err());
        }
    }
}

pub mod attributes;
pub mod whitespace;
pub mod identifiers;
pub mod types;
