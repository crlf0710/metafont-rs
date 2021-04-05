//! @ Here is how to open the terminal files
//! in \ph. The `\.{/I}' switch suppresses the first |get|.
//! @:PASCAL H}{\ph@>
//! @^system dependencies@>
//
// @d t_open_in==reset(term_in,'TTY:','/O/I') {open the terminal for text input}
/// open the terminal for text input
pub(crate) fn t_open_in(io_view: MFInteractiveIoView<'_>) {
    reset(io_view.term_in, "TTY:", "/O/I");
}

// @d t_open_out==rewrite(term_out,'TTY:','/O')
//  {open the terminal for text output}
/// open the terminal for text output
pub(crate) fn t_open_out(io_view: MFInteractiveIoView<'_>) {
    rewrite(io_view.term_out, "TTY:", "/O");
}

use pascal_io::{reset, rewrite};
use crate::section_0031::MFInteractiveIoView;
