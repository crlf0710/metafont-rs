#![macro_use]

pub(crate) type integer = i32;
pub(crate) type real = f32;
pub(crate) type word = u32;
pub(crate) type boolean = bool;

pub(crate) type text_char = char;
pub(crate) type text_char_repr = char_repr;

#[cfg(not(feature = "unicode_support"))]
#[derive(Copy, Clone, Default, PartialOrd, PartialEq)]
pub(crate) struct char(pub(crate) u8);

#[cfg(not(feature = "unicode_support"))]
type char_repr = u8;

#[cfg(not(feature = "unicode_support"))]
impl core::fmt::Debug for char {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        assert!(*self <= char::MAX);
        write!(f, "{:?}", self.0 as core::primitive::char)?;
        Ok(())
    }
}

#[cfg(not(feature = "unicode_support"))]
impl char {
    pub(crate) const MAX: char = char(255);

    pub(crate) const fn new(v: u8) -> Self {
        char(v)
    }
}

#[cfg(feature = "unicode_support")]
#[derive(Copy, Clone, Default, PartialOrd, PartialEq)]
pub(crate) struct char(pub(crate) u32);

#[cfg(feature = "unicode_support")]
impl char {
    pub(crate) const MAX: char = char(0x007F_FFFF, PhantomData);
    pub(crate) const fn new(v: u32) -> Self {
        char(v, PhantomData)
    }
}

#[cfg(feature = "unicode_support")]
type char_repr = u32;

#[cfg(feature = "unicode_support")]
impl core::fmt::Debug for char {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        assert!(*self <= char::MAX);
        f.debug_list()
            .entries(crate::unicode_support::chars_from_generalized_char(*self))
            .finish()?;
        Ok(())
    }
}

#[cfg(feature = "unicode_support")]
impl core::fmt::Display for char {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        assert!(*self <= char::MAX);
        for ch in crate::unicode_support::chars_from_generalized_char(*self) {
            write!(f, "{}", ch)?;
        }
        Ok(())
    }
}

macro_rules! define_ranged_numeric {
    ($v:vis $name:ident => $base_type:path) => {
        #[derive(Copy, Clone)]
        $v struct $name<const MIN: $base_type, const MAX: $base_type>($base_type);

        impl<const MIN: $base_type, const MAX: $base_type> $name<MIN, MAX> {
            const fn new(v: $base_type) -> Self {
                assert!(v >= MIN && v <= MAX);
                Self(v)
            }
        }

        impl<const MIN: $base_type, const MAX: $base_type> Default for $name<MIN, MAX> {
            fn default() -> Self {
                let v = <$base_type as Ord>::clamp(Default::default(), MIN, MAX);
                Self::new(v)
            }
        }
    }
}

define_ranged_numeric!(pub u8_from_m_to_n => u8);
define_ranged_numeric!(pub u16_from_m_to_n => u16);
define_ranged_numeric!(pub u32_from_m_to_n => u32);

define_ranged_numeric!(pub i8_from_m_to_n => i8);
define_ranged_numeric!(pub i16_from_m_to_n => i16);
define_ranged_numeric!(pub i32_from_m_to_n => i32);

pub type u8_from_0_to_n<const N: u8> = u8_from_m_to_n<0, N>;
pub type u16_from_0_to_n<const N: u16> = u16_from_m_to_n<0, N>;
pub type u32_from_0_to_n<const N: u32> = u32_from_m_to_n<0, N>;

#[derive(Clone, Copy, PartialEq, PartialOrd)]
pub(crate) struct LiftedInteger(integer);

#[derive(Clone, Copy, PartialEq, PartialOrd)]
pub(crate) struct LiftedWord(word);

pub(crate) trait LiftToInt {
    fn lift_to_int(self) -> LiftedInteger;
}

pub(crate) trait LiftToWord {
    fn lift_to_word(self) -> LiftedWord;
}

macro_rules! impl_lift_to_int {
    ($ty:path) => {
        impl LiftToInt for $ty {
            fn lift_to_int(self) -> LiftedInteger {
                LiftedInteger(self as _)
            }
        }
    };
}

macro_rules! impl_lift_to_word {
    ($ty:path) => {
        impl LiftToWord for $ty {
            fn lift_to_word(self) -> LiftedWord {
                LiftedWord(self as _)
            }
        }
    };
}

macro_rules! impl_partial_cmp_for_lifted_integer {
    ($ty:path) => {
        impl PartialEq<$ty> for LiftedInteger {
            fn eq(&self, other: &$ty) -> bool {
                self.0.eq(&(*other as integer))
            }
        }
        impl PartialOrd<$ty> for LiftedInteger {
            fn partial_cmp(&self, other: &$ty) -> Option<core::cmp::Ordering> {
                self.0.partial_cmp(&(*other as integer))
            }
        }
    };
}

macro_rules! impl_partial_cmp_for_lifted_word {
    ($ty:path) => {
        impl PartialEq<$ty> for LiftedWord {
            fn eq(&self, other: &$ty) -> bool {
                self.0.eq(&(*other as word))
            }
        }
        impl PartialOrd<$ty> for LiftedWord {
            fn partial_cmp(&self, other: &$ty) -> Option<core::cmp::Ordering> {
                self.0.partial_cmp(&(*other as word))
            }
        }

        impl core::ops::Add<$ty> for LiftedWord {
            type Output = Self;

            fn add(self, rhs: $ty) -> Self {
                Self(self.0.add(rhs as word))
            }
        }
    };
}

impl_lift_to_int!(u8);
impl_lift_to_int!(u16);
impl_lift_to_int!(i8);
impl_lift_to_int!(i16);
impl_lift_to_int!(i32);
impl_partial_cmp_for_lifted_integer!(u8);
impl_partial_cmp_for_lifted_integer!(u16);
impl_partial_cmp_for_lifted_integer!(i8);
impl_partial_cmp_for_lifted_integer!(i16);
impl_partial_cmp_for_lifted_integer!(i32);
impl_lift_to_word!(u8);
impl_lift_to_word!(u16);
impl_lift_to_word!(u32);
impl_partial_cmp_for_lifted_word!(u8);
impl_partial_cmp_for_lifted_word!(u16);
impl_partial_cmp_for_lifted_word!(u32);

pub(crate) trait IsOddOrEven {
    fn is_odd(&self) -> boolean;
    fn is_even(&self) -> boolean {
        !self.is_odd()
    }
}

macro_rules! impl_is_even_or_odd_for_primitive {
    ($t:path) => {
        impl IsOddOrEven for $t {
            fn is_odd(&self) -> boolean {
                self % 2 != 0
            }
        }
    };
}

impl_is_even_or_odd_for_primitive!(u8);
impl_is_even_or_odd_for_primitive!(u16);
impl_is_even_or_odd_for_primitive!(u32);
impl_is_even_or_odd_for_primitive!(i8);
impl_is_even_or_odd_for_primitive!(i16);
impl_is_even_or_odd_for_primitive!(i32);

pub(crate) unsafe trait DefaultWithZeroed {}

macro_rules! impl_zeroed_default_for_primitive {
    ($t:path) => {
        unsafe impl DefaultWithZeroed for $t {}
    };
}

impl_zeroed_default_for_primitive!(u8);
impl_zeroed_default_for_primitive!(u16);
impl_zeroed_default_for_primitive!(u32);
impl_zeroed_default_for_primitive!(i8);
impl_zeroed_default_for_primitive!(i16);
impl_zeroed_default_for_primitive!(i32);

pub(crate) trait ZeroedDefault {
    fn zeroed_default() -> Self;
}

impl<T> ZeroedDefault for Box<T>
where
    T: DefaultWithZeroed,
{
    fn zeroed_default() -> Self {
        unsafe { Box::new_zeroed().assume_init() }
    }
}

macro_rules! define_ranged_numeric_indexed_array {
    ($v:vis $name:ident => $base_type:path; $first:expr, $last:expr) => {
        #[derive(Copy, Clone)]
        $v struct $name<ELEMENT>
            ([ELEMENT; ($last as usize).checked_sub($first as usize).unwrap()]);

        unsafe impl<ELEMENT> crate::pascal::DefaultWithZeroed for $name<ELEMENT> where ELEMENT: crate::pascal::DefaultWithZeroed {
        }
        impl<ELEMENT> crate::pascal::ZeroedDefault for $name<ELEMENT> where ELEMENT: crate::pascal::DefaultWithZeroed {
            fn zeroed_default() -> Self {
                unsafe {
                    core::mem::zeroed()
                }
            }
        }

        impl<ELEMENT> $name<ELEMENT> {
        }
    };
}

pub(crate) struct file_of_text_char {
    file_state: FileState<text_char>,
    error_state: usize,
}

impl Default for file_of_text_char {
    fn default() -> Self {
        file_of_text_char {
            file_state: FileState::default(),
            error_state: usize::default(),
        }
    }
}

impl_debug_with_literal!(file_of_text_char, "file_of_text_char");

impl PascalFile for file_of_text_char {
    type Unit = text_char;

    fn is_text_file() -> bool {
        true
    }

    fn is_eoln_unit(unit: &Self::Unit) -> bool {
        unit.0 == b'\n' as text_char_repr
    }

    fn eoln_unit() -> Self::Unit {
        text_char::new(b'\n' as _)
    }

    fn convert_line_string_crlf_to_lf(input: &mut String) {
        if input.ends_with("\r\n") {
            input.pop();
            input.pop();
            input.push('\n');
        }
    }

    fn convert_line_string_to_units(input: &str, units: &mut Vec<Self::Unit>) {
        #[cfg(not(feature = "unicode_support"))]
        {
            for byte in input.bytes() {
                units.push(text_char::new(byte))
            }
        }
        #[cfg(feature = "unicode_support")]
        {
            use unicode_segmentation::UnicodeSegmentation;
            for grapheme in input.graphemes(true) {
                if grapheme.as_bytes().len() == 1 {
                    units.push(text_char::new(grapheme.as_bytes()[0] as _))
                } else {
                    let (byte_offset, ch) = grapheme.char_indices().rev().next().unwrap();
                    if byte_offset == 0 {
                        units.push(text_char::new(ch as _))
                    } else {
                        todo!();
                    }
                }
            }
        }
    }

    fn convert_blob_to_unit(_: &[u8]) -> Self::Unit {
        unreachable!();
    }

    fn convert_unit_to_blob(_: Self::Unit, _: &mut dyn for<'a> FnMut(&'a [u8])) {
        unreachable!();
    }

    fn file_state(&self) -> &FileState<text_char> {
        &self.file_state
    }

    fn file_state_mut(&mut self) -> &mut FileState<text_char> {
        &mut self.file_state
    }

    fn error_state(&self) -> usize {
        self.error_state
    }

    fn set_error_state(&mut self, error_state: usize) {
        self.error_state = error_state;
    }

    fn open_text_file_for_read(path: &str) -> Result<(Box<dyn pascal_io::ReadLine>, bool), usize> {
        use pascal_io::ReadLine;
        use std::io;
        let mut term_special_handling = false;
        let read_target: Box<dyn ReadLine> = if path == "TTY:" {
            term_special_handling = true;
            Box::new(io::stdin())
        } else if false
        /* path == crate::section_0011::pool_name */
        {
            /* Box::new(crate::string_pool::pool_file()) */
            todo!();
        } else {
            let path = path.trim_end_matches(' ');
            let file = std::fs::File::open(path).map_err(|_| 1usize)?;
            Box::new(io::BufReader::new(file))
        };
        Ok((read_target, term_special_handling))
    }

    fn open_binary_file_for_read(_: &str) -> Result<Box<dyn std::io::Read>, usize> {
        unreachable!();
    }

    fn open_file_for_write(path: &str) -> Result<Box<dyn std::io::Write>, usize> {
        use std::io::{self, Write};
        let write_target: Box<dyn Write> = if path == "TTY:" {
            Box::new(io::stdout())
        } else {
            let path = path.trim_end_matches(' ');
            let file = std::fs::File::create(path).map_err(|_| 1usize)?;
            Box::new(file)
        };
        Ok(write_target)
    }
}

pub(crate) type packed_file_of_text_char = file_of_text_char;

pub(crate) struct file_of<T> {
    file_state: FileState<T>,
    error_state: usize,
}

impl_debug_with_literal!(file_of[T], "file_of<T>");

impl<T> Default for file_of<T> {
    fn default() -> Self {
        file_of {
            file_state: FileState::default(),
            error_state: usize::default(),
        }
    }
}

impl<T: FromBlob + ToBlob> PascalFile for file_of<T> {
    type Unit = T;

    fn is_text_file() -> bool {
        false
    }

    fn is_eoln_unit(_: &T) -> bool {
        unreachable!()
    }

    fn eoln_unit() -> Self::Unit {
        unreachable!()
    }

    fn convert_line_string_crlf_to_lf(_: &mut String) {
        unreachable!()
    }

    fn convert_line_string_to_units(_: &str, _: &mut Vec<Self::Unit>) {
        unreachable!()
    }

    fn convert_blob_to_unit(input: &[u8]) -> Self::Unit {
        T::from_blob(input)
    }

    fn convert_unit_to_blob(v: Self::Unit, f: &mut dyn for<'a> FnMut(&'a [u8])) {
        use core::borrow::Borrow;
        let blob = v.to_blob();
        f(blob.borrow());
    }

    fn file_state(&self) -> &FileState<T> {
        &self.file_state
    }

    fn file_state_mut(&mut self) -> &mut FileState<T> {
        &mut self.file_state
    }

    fn error_state(&self) -> usize {
        self.error_state
    }

    fn set_error_state(&mut self, error_state: usize) {
        self.error_state = error_state;
    }

    fn open_text_file_for_read(_: &str) -> Result<(Box<dyn pascal_io::ReadLine>, bool), usize> {
        unreachable!();
    }

    fn open_binary_file_for_read(path: &str) -> Result<Box<dyn std::io::Read>, usize> {
        use std::io::{self, Read};
        let read_target: Box<dyn Read> = if path == "TTY:" {
            Box::new(io::stdin())
        } else {
            let path = path.trim_end_matches(' ');
            let file = std::fs::File::open(path).map_err(|_| 1usize)?;
            Box::new(io::BufReader::new(file))
        };
        Ok(read_target)
    }

    fn open_file_for_write(path: &str) -> Result<Box<dyn std::io::Write>, usize> {
        use std::io::{self, Write};
        let write_target: Box<dyn Write> = if path == "TTY:" {
            Box::new(io::stdout())
        } else {
            let path = path.trim_end_matches(' ');
            let file = std::fs::File::create(path).map_err(|_| 1usize)?;
            Box::new(file)
        };
        Ok(write_target)
    }
}

pub(crate) type packed_file_of<T> = file_of<T>;

use core::fmt;
use pascal_io::{FileState, FromBlob, PascalFile, ToBlob};
