//! @ The value of |history| is initially |fatal_error_stop|, but it will
//! be changed to |spotless| if \MF\ survives the initialization process.
//!
//! @<Set init...@>=
//! deletions_allowed:=true; error_count:=0; {|history| is initialized elsewhere}
//!
//! @ Since errors can be detected almost anywhere in \MF, we want to declare the
//! error procedures near the beginning of the program. But the error procedures
//! in turn use some other procedures, which need to be declared |forward|
//! before we get to |error| itself.
//!
//! It is possible for |error| to be called recursively if some error arises
//! when |get_next| is being used to delete a token, and/or if some fatal error
//! occurs while \MF\ is trying to fix a non-fatal one. But such recursion
//! @^recursion@>
//! is never more than two levels deep.
//!
//! @<Error handling...@>=
//! procedure@?normalize_selector; forward;@t\2@>@/
//! procedure@?get_next; forward;@t\2@>@/
//! procedure@?term_input; forward;@t\2@>@/
//! procedure@?show_context; forward;@t\2@>@/
//! procedure@?begin_file_reading; forward;@t\2@>@/
//! procedure@?open_log_file; forward;@t\2@>@/
//! procedure@?close_files_and_terminate; forward;@t\2@>@/
//! procedure@?clear_for_error_prompt; forward;@t\2@>@/
//! @t\4\hskip-\fontdimen2\font@>@;@+@!debug@+procedure@?debug_help;
//!   forward;@;@+gubed@;@/
//! @t\4@>@<Declare the procedure called |flush_string|@>
//!
//! @ Individual lines of help are recorded in the array |help_line|, which
//! contains entries in positions |0..(help_ptr-1)|. They should be printed
//! in reverse order, i.e., with |help_line[0]| appearing last.
//!
//! @d hlp1(#)==help_line[0]:=#;@+end
//! @d hlp2(#)==help_line[1]:=#; hlp1
//! @d hlp3(#)==help_line[2]:=#; hlp2
//! @d hlp4(#)==help_line[3]:=#; hlp3
//! @d hlp5(#)==help_line[4]:=#; hlp4
//! @d hlp6(#)==help_line[5]:=#; hlp5
//! @d help0==help_ptr:=0 {sometimes there might be no help}
//! @d help1==@+begin help_ptr:=1; hlp1 {use this with one help line}
//! @d help2==@+begin help_ptr:=2; hlp2 {use this with two help lines}
//! @d help3==@+begin help_ptr:=3; hlp3 {use this with three help lines}
//! @d help4==@+begin help_ptr:=4; hlp4 {use this with four help lines}
//! @d help5==@+begin help_ptr:=5; hlp5 {use this with five help lines}
//! @d help6==@+begin help_ptr:=6; hlp6 {use this with six help lines}
//!
//! @<Glob...@>=
//! @!help_line:array[0..5] of str_number; {helps for the next |error|}
//! @!help_ptr:0..6; {the number of help lines present}
//! @!use_err_help:boolean; {should the |err_help| string be shown?}
//! @!err_help:str_number; {a string set up by \&{errhelp}}
//!
//! @ @<Set init...@>=
//! help_ptr:=0; use_err_help:=false; err_help:=0;
//!
