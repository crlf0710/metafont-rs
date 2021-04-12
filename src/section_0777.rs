//! ` `
// @<Check the ``constant'' values for consistency@>=
pub(crate) fn Check_the_constant_values_for_consistency_0777(bad: &mut usize) {
    // if base_default_length>file_name_size then bad:=41;
    if base_default_length > file_name_size {
        *bad = 41;
    }
}

use crate::section_0011::file_name_size;
use crate::section_0775::base_default_length;
