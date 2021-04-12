//! @ The following parameters can be changed at compile time to extend or
//! reduce \MF's capacity. They may have different values in \.{INIMF} and
//! in production versions of \MF.
//! @.INIMF@>
//! @^system dependencies@>

//
// @<Constants...@>=
// @!mem_max=30000; {greatest index in \MF's internal |mem| array;
//   must be strictly less than |max_halfword|;
//   must be equal to |mem_top| in \.{INIMF}, otherwise |>=mem_top|}
/// greatest index in `METAFONT`'s internal `mem` array;
/// must be strictly less than `max_halfword`;
/// must be equal to `mem_top` in `INIMF`, otherwise `>=mem_top`
pub(crate) const mem_max: word = 30000;
// @!max_internal=100; {maximum number of internal quantities}
/// maximum number of internal quantities
pub(crate) const max_internal: word = 100;
// @!buf_size=500; {maximum number of characters simultaneously present in
//   current lines of open files; must not exceed |max_halfword|}
/// maximum number of characters simultaneously present in current lines of open files; must not exceed `max_halfword`
pub(crate) const buf_size: word = 500;
// @!error_line=72; {width of context lines on terminal error messages}
/// width of context lines on terminal error messages
pub(crate) const error_line: word = 72;
// @!half_error_line=42; {width of first lines of contexts in terminal
//   error messages; should be between 30 and |error_line-15|}
/// width of first lines of contexts in terminal error messages; should be between 30 and `error_line-15`
pub(crate) const half_error_line: word = 42;
// @!max_print_line=79; {width of longest text lines output; should be at least 60}
/// width of longest text lines output; should be at least 60
pub(crate) const max_print_line: word = 79;
// @!screen_width=768; {number of pixels in each row of screen display}
// @!screen_depth=1024; {number of pixels in each column of screen display}
// @!stack_size=30; {maximum number of simultaneous input sources}
// @!max_strings=2000; {maximum number of strings; must not exceed |max_halfword|}
/// maximum number of strings; must not exceed `max_halfword`
pub(crate) const max_strings: word = 2000;
// @!string_vacancies=8000; {the minimum number of characters that should be
//   available for the user's identifier names and strings,
//   after \MF's own error messages are stored}
// @!pool_size=32000; {maximum number of characters in strings, including all
//   error messages and help texts, and the names of all identifiers;
//   must exceed |string_vacancies| by the total
//   length of \MF's own strings, which is currently about 22000}
/// maximum number of characters in strings, including all
/// error messages and help texts, and the names of all identifiers;
/// must exceed `string_vacancies` by the total
/// length of `METAFONT`'s own strings, which is currently about 22000
pub(crate) const pool_size: word = 32000;
// @!move_size=5000; {space for storing moves in a single octant}
// @!max_wiggle=300; {number of autorounded points per cycle}
// @!gf_buf_size=800; {size of the output buffer, must be a multiple of 8}
/// size of the output buffer, must be a multiple of 8
pub(crate) const gf_buf_size: word = 800;
// @!file_name_size=40; {file names shouldn't be longer than this}
/// file names shouldn't be longer than this
pub(crate) const file_name_size: word = 40;
// @!pool_name='MFbases:MF.POOL                         ';
//   {string of length |file_name_size|; tells where the string pool appears}
// @.MFbases@>
// @!path_size=300; {maximum number of knots between breakpoints of a path}
// @!bistack_size=785; {size of stack for bisection algorithms;
//   should probably be left at this value}
/// size of stack for bisection algorithms; should probably be left at this value
pub(crate) const bistack_size: word = 785;
// @!header_size=100; {maximum number of \.{TFM} header words, times~4}
/// maximum number of `TFM` header words, times 4
pub(crate) const header_size: word = 100;
// @!lig_table_size=5000; {maximum number of ligature/kern steps, must be
//   at least 255 and at most 32510}
/// maximum number of ligature/kern steps, must be at least 255 and at most 32510
pub(crate) const lig_table_size: word = 5000;
// @!max_kerns=500; {maximum number of distinct kern amounts}
// @!max_font_dimen=50; {maximum number of \&{fontdimen} parameters}
//

use crate::pascal::word;
