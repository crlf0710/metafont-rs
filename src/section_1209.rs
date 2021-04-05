//! @ We get to the |final_cleanup| routine when \&{end} or \&{dump} has
//! been scanned.
//
// @<Last-minute...@>=
impl MetafontSystem {
    // procedure final_cleanup;
    pub(crate) fn final_cleanup(&mut self) -> MFResult<()> {
        let _system = &mut* self;
        // label exit;
        // var c:small_number; {0 for \&{end}, 1 for \&{dump}}
        // begin c:=cur_mod;
        // if job_name=0 then open_log_file;
        // while input_ptr>0 do
        //   if token_state then end_token_list@+else end_file_reading;
        // while loop_ptr<>null do stop_iteration;
        // while open_parens>0 do
        //   begin print(" )"); decr(open_parens);
        //   end;
        // while cond_ptr<>null do
        //   begin print_nl("(end occurred when ");@/
        // @.end occurred...@>
        //   print_cmd_mod(fi_or_else,cur_if);
        //     {`\.{if}' or `\.{elseif}' or `\.{else}'}
        //   if if_line<>0 then
        //     begin print(" on line "); print_int(if_line);
        //     end;
        //   print(" was incomplete)");
        //   if_line:=if_line_field(cond_ptr);
        //   cur_if:=name_type(cond_ptr); loop_ptr:=cond_ptr;
        //   cond_ptr:=link(cond_ptr); free_node(loop_ptr,if_node_size);
        //   end;
        // if history<>spotless then
        //  if ((history=warning_issued)or(interaction<error_stop_mode)) then
        //   if selector=term_and_log then
        //   begin selector:=term_only;
        //   print_nl("(see the transcript file for additional information)");
        // @.see the transcript file...@>
        //   selector:=term_and_log;
        //   end;
        // if c=1 then
        //   begin @!init store_base_file; return;@+tini@/
        //   print_nl("(dump is performed only by INIMF)"); return;
        // @.dump...only by INIMF@>
        //   end;
        // exit:end;
        todo!();
    }
}

use crate::section_0004::MetafontSystem;
use crate::section_0076::MFResult;
