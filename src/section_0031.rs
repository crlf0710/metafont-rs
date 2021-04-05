//! @ The user's terminal acts essentially like other files of text, except
//! that it is used both for input and for output. When the terminal is
//! considered an input file, the file variable is called |term_in|, and when it
//! is considered an output file the file variable is |term_out|.
//! @^system dependencies@>

#[globals_struct_field(MetafontSystem)]
pub(crate) static interactive_system: MetafontInteractive = MetafontInteractive::default();

#[globals_struct_use(MetafontSystem)]
use crate::section_0031::MetafontInteractive;

#[globals_struct]
#[globals_struct_field_view(MFInteractiveIoView, make_interactive_io_view)]
pub(crate) mod MetafontInteractive {
    include!("src/section_0031.rs");
    include!("src/section_0071.rs");
}

impl MetafontInteractive {
    pub(crate) fn io_view(&mut self) -> MFInteractiveIoView<'_> {
        make_interactive_io_view!(self)
    }
}

// @<Glob...@>=
// @!term_in:alpha_file; {the terminal as an input file}
/// the terminal as an input file
#[globals_struct_field(MetafontInteractive)]
#[globals_struct_field_view(MFInteractiveIoView)]
pub(crate) static term_in: alpha_file = alpha_file::default();

// @!term_out:alpha_file; {the terminal as an output file}
/// the terminal as an output file
#[globals_struct_field(MetafontInteractive)]
#[globals_struct_field_view(MFInteractiveIoView)]
pub(crate) static term_out: alpha_file = alpha_file::default();

#[globals_struct_use(MetafontInteractive)]
pub(crate) use crate::section_0024::alpha_file;

use globals_struct::{globals_struct, globals_struct_field, globals_struct_use};
