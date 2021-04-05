//! @* \[5] On-line and off-line printing.
//! Messages that are sent to a user's terminal and to the transcript-log file
//! are produced by several `|print|' procedures. These procedures will
//! direct their output to a variety of places, based on the setting of
//! the global variable |selector|, which has the following possible
//! values:
//!
//! \yskip
//! \hang |term_and_log|, the normal setting, prints on the terminal and on the
//!   transcript file.
//!
//! \hang |log_only|, prints only on the transcript file.
//!
//! \hang |term_only|, prints only on the terminal.
//!
//! \hang |no_print|, doesn't print at all. This is used only in rare cases
//!   before the transcript file is open.
//!
//! \hang |pseudo|, puts output into a cyclic buffer that is used
//!   by the |show_context| routine; when we get to that routine we shall discuss
//!   the reasoning behind this curious mode.
//!
//! \hang |new_string|, appends the output to the current string in the
//!   string pool.
//!
//! \yskip
//! \noindent The symbolic names `|term_and_log|', etc., have been assigned
//! numeric codes that satisfy the convenient relations |no_print+1=term_only|,
//! |no_print+2=log_only|, |term_only+2=log_only+1=term_and_log|.
//!
//! Three additional global variables, |tally| and |term_offset| and
//! |file_offset|, record the number of characters that have been printed
//! since they were most recently cleared to zero. We use |tally| to record
//! the length of (possibly very long) stretches of printing; |term_offset|
//! and |file_offset|, on the other hand, keep track of how many characters
//! have appeared so far on the current line that has been output to the
//! terminal or to the transcript file, respectively.

#[globals_struct]
#[globals_struct_field_view(MFTranscriptIoView, make_transcript_io_view)]
pub(crate) mod MetafontTranscript {
    include!("src/section_0054.rs");
}

// @d no_print=0 {|selector| setting that makes data disappear}
// @d term_only=1 {printing is destined for the terminal only}
// @d log_only=2 {printing is destined for the transcript file only}
// @d term_and_log=3 {normal |selector| setting}
// @d pseudo=4 {special |selector| setting for |show_context|}
// @d new_string=5 {printing is deflected to the string pool}
// @d max_selector=5 {highest selector setting}
//
// @<Glob...@>=
// @!log_file : alpha_file; {transcript of \MF\ session}
/// transcript of METAFONT session
#[globals_struct_field(MetafontTranscript)]
#[globals_struct_field_view(MFTranscriptIoView)]
pub(crate) static log_file: alpha_file = alpha_file::default();
// @!selector : 0..max_selector; {where to print a message}
// @!dig : array[0..22] of 0..15; {digits in a number being output}
// @!tally : integer; {the number of characters recently printed}
// @!term_offset : 0..max_print_line;
//   {the number of characters on the current terminal line}
// @!file_offset : 0..max_print_line;
//   {the number of characters on the current file line}
// @!trick_buf:array[0..error_line] of ASCII_code; {circular buffer for
//   pseudoprinting}
// @!trick_count: integer; {threshold for pseudoprinting, explained later}
// @!first_count: integer; {another variable for pseudoprinting}
//

#[globals_struct_use(MetafontTranscript)]
use crate::section_0031::alpha_file;

use globals_struct::{globals_struct, globals_struct_field, globals_struct_use};
