//! ` `

// @<Check the ``constant'' values...@>=
pub(crate) fn Check_the_constant_values_for_consistency_0204(bad: &mut usize) {
    // if hash_end+max_internal>max_halfword then bad:=21;
    if hash_end.lift_to_word() + max_internal > max_halfword {
        *bad = 21;
    }
}

use crate::pascal::LiftToWord;
use crate::section_0011::max_internal;
use crate::section_0153::max_halfword;
use crate::section_0201::hash_end;
