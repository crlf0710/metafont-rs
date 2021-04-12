//! @ Later on we will say `\ignorespaces|if mem_max>=max_halfword then bad:=10|',
//! or something similar. (We can't do that until |max_halfword| has been defined.)
//
// @<Check the ``constant'' values for consistency@>=
pub(crate) fn Check_the_constant_values_for_consistency_0014(bad: &mut usize) {
    // bad:=0;
    *bad = 0;
    // if (half_error_line<30)or(half_error_line>error_line-15) then bad:=1;
    if half_error_line < 30 || half_error_line > error_line - 15 {
        *bad = 1;
    }
    // if max_print_line<60 then bad:=2;
    if max_print_line < 60 {
        *bad = 2;
    }
    // if gf_buf_size mod 8<>0 then bad:=3;
    if gf_buf_size % 8 != 0 {
        *bad = 3;
    }
    // if mem_min+1100>mem_top then bad:=4;
    if mem_min + 1100 > mem_top {
        *bad = 4;
    }
    // if hash_prime>hash_size then bad:=5;
    if hash_prime > hash_size {
        *bad = 5;
    }
    // if header_size mod 4 <> 0 then bad:=6;
    if header_size % 4 != 0 {
        *bad = 6;
    }
    // if(lig_table_size<255)or(lig_table_size>32510)then bad:=7;
    if lig_table_size < 255 || lig_table_size > 32510 {
        *bad = 7;
    }
}

use crate::section_0011::error_line;
use crate::section_0011::half_error_line;
use crate::section_0011::gf_buf_size;
use crate::section_0011::max_print_line;
use crate::section_0011::header_size;
use crate::section_0011::lig_table_size;
use crate::section_0012::mem_min;
use crate::section_0012::mem_top;
use crate::section_0012::hash_prime;
use crate::section_0012::hash_size;
