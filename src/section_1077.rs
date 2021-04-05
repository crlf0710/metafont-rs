//! ` `

// @<Glob...@>=
// @!start_sym:halfword; {a symbolic token to insert at beginning of job}
/// a symbolic token to insert at beginning of job
#[globals_struct_field(MetafontInterpreter)]
pub(crate) static start_sym: hash_pointer = hash_pointer::default();

#[globals_struct_use(MetafontInterpreter)]
use crate::section_0200::hash_pointer;

use globals_struct::{globals_struct_field, globals_struct_use};
