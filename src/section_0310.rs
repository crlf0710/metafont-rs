//! ` `
// @<Check the ``constant'' values...@>=
pub(crate) fn Check_the_constant_values_for_consistency_0310(bad: &mut usize) {
    // if 15*move_increment>bistack_size then bad:=31;
    if 15 * move_increment > bistack_size {
        *bad = 31;
    }
}

use crate::section_0011::bistack_size;
use crate::section_0309::move_increment;
