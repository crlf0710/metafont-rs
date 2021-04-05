//! @ Here we do whatever is needed to complete \MF's job gracefully on the
//! local operating system. The code here might come into play after a fatal
//! error; it must therefore consist entirely of ``safe'' operations that
//! cannot produce error messages. For example, it would be a mistake to call
//! |str_room| or |make_string| at this time, because a call on |overflow|
//! might lead to an infinite loop.
//! @^system dependencies@>
//!
//! If |final_cleanup| is bypassed, this program doesn't bother to close
//! the input files that may still be open.
//
// @<Last-minute...@>=
impl MetafontSystem {
    // procedure close_files_and_terminate;
    pub(crate) fn close_files_and_terminate(&mut self) {
        let _system = &mut *self;
        // var @!k:integer; {all-purpose index}
        // @!lh:integer; {the length of the \.{TFM} header, in words}
        // @!lk_offset:0..256; {extra words inserted at beginning of |lig_kern| array}
        // @!p:pointer; {runs through a list of \.{TFM} dimensions}
        // @!x:scaled; {a |tfm_width| value being output to the \.{GF} file}
        // begin
        // @!stat if internal[tracing_stats]>0 then
        //   @<Output statistics about this job@>;@;@+tats@/
        // wake_up_terminal; @<Finish the \.{TFM} and \.{GF} files@>;
        // if log_opened then
        //   begin wlog_cr;
        //   a_close(log_file); selector:=selector-2;
        //   if selector=term_only then
        //     begin print_nl("Transcript written on ");
        // @.Transcript written...@>
        //     slow_print(log_name); print_char(".");
        //     end;
        //   end;
        // end;
        todo!();
    }
}

use crate::section_0004::MetafontSystem;
