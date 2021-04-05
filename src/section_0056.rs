//! @ Macro abbreviations for output to the terminal and to the log file are
//! defined here for convenience. Some systems need special conventions
//! for terminal output, and it is possible to adhere to those conventions
//! by changing |wterm|, |wterm_ln|, and |wterm_cr| here.
//! @^system dependencies@>
//
// @d wterm(#)==write(term_out,#)
pub(crate) fn wterm<T: Display>(io_view: MFInteractiveIoView<'_>, val: T) {
    write(io_view.term_out, val);
}
// @d wterm_ln(#)==write_ln(term_out,#)
pub(crate) fn wterm_ln<T: Display>(io_view: MFInteractiveIoView<'_>, val: T) {
    write_ln(io_view.term_out, val);
}
// @d wterm_cr==write_ln(term_out)
pub(crate) fn wterm_cr(io_view: MFInteractiveIoView<'_>) {
    write_ln_noargs(io_view.term_out);
}
// @d wlog(#)==write(log_file,#)
pub(crate) fn wlog<T: Display>(io_view: MFTranscriptIoView<'_>, val: T) {
    write(io_view.log_file, val);
}
// @d wlog_ln(#)==write_ln(log_file,#)
pub(crate) fn wlog_ln<T: Display>(io_view: MFTranscriptIoView<'_>, val: T) {
    write_ln(io_view.log_file, val);
}
// @d wlog_cr==write_ln(log_file)
pub(crate) fn wlog_cr(io_view: MFTranscriptIoView<'_>) {
    write_ln_noargs(io_view.log_file);
}

use core::fmt::Display;
use pascal_io::write;
use pascal_io::write_ln;
use pascal_io::write_ln_noargs;
use crate::section_0031::MFInteractiveIoView;
use crate::section_0054::MFTranscriptIoView;
