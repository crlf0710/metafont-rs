//! @ When we begin the following code, \MF's tables may still contain garbage;
//! the strings might not even be present. Thus we must proceed cautiously to get
//! bootstrapped in.
//!
//! But when we finish this part of the program, \MF\ is ready to call on the
//! |main_control| routine to do its work.
//
// @<Get the first line...@>=
pub(crate) macro_rules! Get_the_first_line_of_input_and_prepare_to_start {
    ($system:expr, $lbl_end_of_MF:lifetime, $lbl_final_end:lifetime) => {
        // begin @<Initialize the input routines@>;
        // if (base_ident=0)or(buffer[loc]="&") then
        //   begin if base_ident<>0 then initialize; {erase preloaded base}
        //   if not open_base_file then goto final_end;
        //   if not load_base_file then
        //     begin w_close(base_file); goto final_end;
        //     end;
        //   w_close(base_file);
        //   while (loc<limit)and(buffer[loc]=" ") do incr(loc);
        //   end;
        // buffer[limit]:="%";@/
        // fix_date_and_time; init_randoms(sys_time+sys_day*unity);@/
        // @<Initialize the print |selector|...@>;
        // if loc<limit then if buffer[loc]<>"\" then start_input; {\&{input} assumed}
        // end
        todo!();
    };
}
