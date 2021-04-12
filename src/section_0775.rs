//! @ A messier routine is also needed, since base file names must be scanned
//! before \MF's string mechanism has been initialized. We shall use the
//! global variable |MF_base_default| to supply the text for default system areas
//! and extensions related to base files.
//! @^system dependencies@>
//
// @d base_default_length=18 {length of the |MF_base_default| string}
/// length of the `MF_base_default` string
pub(crate) const base_default_length: word = 18;
// @d base_area_length=8 {length of its area part}
// @d base_ext_length=5 {length of its `\.{.base}' part}
// @d base_extension=".base" {the extension, as a \.{WEB} constant}
//
// @<Glob...@>=
// @!MF_base_default:packed array[1..base_default_length] of char;
//

use crate::pascal::word;
