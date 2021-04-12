//! @ Here are the inequalities that the quarterword and halfword values
//! must satisfy (or rather, the inequalities that they mustn't satisfy):
//
// @<Check the ``constant''...@>=
pub(crate) fn Check_the_constant_values_for_consistency_0154(bad: &mut usize) {
    // init if mem_max<>mem_top then bad:=10;@+tini@;@/
    region_init! {
        if mem_max != mem_top {
            *bad = 10;
        }
    }
    // if mem_max<mem_top then bad:=10;
    if mem_max < mem_top {
        *bad = 10;
    }
    // if (min_quarterword>0)or(max_quarterword<127) then bad:=11;
    if min_quarterword > 0 || max_quarterword < 127 {
        *bad = 11;
    }
    // if (min_halfword>0)or(max_halfword<32767) then bad:=12;
    if min_halfword > 0 || max_halfword < 32767 {
        *bad = 12;
    }
    // if (min_quarterword<min_halfword)or@|
    //   (max_quarterword>max_halfword) then bad:=13;
    if min_quarterword.lift_to_word() < min_halfword || max_quarterword.lift_to_word() > max_halfword {
        *bad = 13;
    }
    // if (mem_min<min_halfword)or(mem_max>=max_halfword) then bad:=14;
    if mem_min.lift_to_word() < min_halfword || mem_max.lift_to_word() >= max_halfword {
        *bad = 14;
    }
    // if max_strings>max_halfword then bad:=15;
    if max_strings.lift_to_word() > max_halfword {
        *bad = 15;
    }
    // if buf_size>max_halfword then bad:=16;
    if buf_size.lift_to_word() > max_halfword {
        *bad = 16;
    }
    // if (max_quarterword-min_quarterword<255)or@|
    //   (max_halfword-min_halfword<65535) then bad:=17;
    if max_quarterword - min_quarterword < 255 || max_halfword - min_halfword < 65535 {
        *bad = 17;
    }
}

use crate::pascal::LiftToWord;
use crate::section_0008::region_init;
use crate::section_0011::buf_size;
use crate::section_0011::mem_max;
use crate::section_0011::max_strings;
use crate::section_0012::mem_min;
use crate::section_0012::mem_top;
use crate::section_0153::{max_halfword, min_halfword, max_quarterword, min_quarterword};
