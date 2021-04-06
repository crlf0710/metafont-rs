//! @ The |print_cmd_mod| routine prints a symbolic interpretation of a
//! command code and its modifier.
//! It consists of a rather tedious sequence of print
//! commands, and most of it is essentially an inverse to the |primitive|
//! routine that enters a \MF\ primitive into |hash| and |eqtb|. Therefore almost
//! all of this procedure appears elsewhere in the program, together with the
//! corresponding |primitive| calls.
//!
//! @<Declare the procedure called |print_cmd_mod|@>=
//! procedure print_cmd_mod(@!c,@!m:integer);
//! begin case c of
//! @t\4@>@<Cases of |print_cmd_mod| for symbolic printing of primitives@>@/
//! othercases print("[unknown command code!]")
//! endcases;
//! end;
//!
//! @ Here is a procedure that displays a given command in braces, in the
//! user's transcript file.
//!
//! @d show_cur_cmd_mod==show_cmd_mod(cur_cmd,cur_mod)
//!
//! @p procedure show_cmd_mod(@!c,@!m:integer);
//! begin begin_diagnostic; print_nl("{");
//! print_cmd_mod(c,m); print_char("}");
//! end_diagnostic(false);
//! end;
//!
