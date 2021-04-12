//! @* \[4] String handling.
//! Symbolic token names and diagnostic messages are variable-length strings
//! of eight-bit characters. Since \PASCAL\ does not have a well-developed string
//! mechanism, \MF\ does all of its string processing by homegrown methods.
//!
//! Elaborate facilities for dynamic strings are not needed, so all of the
//! necessary operations can be handled with a simple data structure.
//! The array |str_pool| contains all of the (eight-bit) ASCII codes in all
//! of the strings, and the array |str_start| contains indices of the starting
//! points of each string. Strings are referred to by integer numbers, so that
//! string number |s| comprises the characters |str_pool[j]| for
//! |str_start[s]<=j<str_start[s+1]|. Additional integer variables
//! |pool_ptr| and |str_ptr| indicate the number of entries used so far
//! in |str_pool| and |str_start|, respectively; locations
//! |str_pool[pool_ptr]| and |str_start[str_ptr]| are
//! ready for the next string to be allocated.
//!
//! String numbers 0 to 255 are reserved for strings that correspond to single
//! ASCII characters. This is in accordance with the conventions of \.{WEB},
//! @.WEB@>
//! which converts single-character strings into the ASCII code number of the
//! single character involved, while it converts other strings into integers
//! and builds a string pool file. Thus, when the string constant \.{"."} appears
//! in the program below, \.{WEB} converts it into the integer 46, which is the
//! ASCII code for a period, while \.{WEB} will convert a string like \.{"hello"}
//! into some integer greater than~255. String number 46 will presumably be the
//! single character `\..'\thinspace; but some ASCII codes have no standard visible
//! representation, and \MF\ may need to be able to print an arbitrary
//! ASCII character, so the first 256 strings are used to specify exactly what
//! should be printed for each of the 256 possibilities.
//!
//! Elements of the |str_pool| array must be ASCII codes that can actually be
//! printed; i.e., they must have an |xchr| equivalent in the local
//! character set. (This restriction applies only to preloaded strings,
//! not to those generated dynamically by the user.)
//!
//! Some \PASCAL\ compilers won't pack integers into a single byte unless the
//! integers lie in the range |-128..127|. To accommodate such systems
//! we access the string pool only via macros that can easily be redefined.
//! @^system dependencies@>
//
// @d si(#) == # {convert from |ASCII_code| to |packed_ASCII_code|}
// @d so(#) == # {convert from |packed_ASCII_code| to |ASCII_code|}
//
// @<Types...@>=
// @!pool_pointer = 0..pool_size; {for variables that point into |str_pool|}
/// for variables that point into `str_pool`
#[derive(Clone, Copy, Default)]
pub(crate) struct pool_pointer(crate::pascal::u16_from_0_to_n<{pool_size as _}>);

unsafe impl crate::pascal::DefaultWithZeroed for pool_pointer {}

// @!str_number = 0..max_strings; {for variables that point into |str_start|}
/// for variables that point into `str_start`
#[derive(Clone, Copy, Default)]
pub(crate) struct str_number(crate::pascal::u16_from_0_to_n<{max_strings as _}>);
// @!packed_ASCII_code = 0..255; {elements of |str_pool| array}
/// elements of `str_pool` array
#[derive(Clone, Copy)]
pub(crate) struct packed_ASCII_code(u8);

unsafe impl crate::pascal::DefaultWithZeroed for packed_ASCII_code {}

define_ranged_numeric_indexed_array!(pub(crate) pool_pointer_indexed_array => u16; 0, pool_size);
define_ranged_numeric_indexed_array!(pub(crate) str_number_indexed_array => u16; 0, max_strings);

use crate::section_0011::pool_size;
use crate::section_0011::max_strings;