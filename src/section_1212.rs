//! @* \[50] Debugging.
//! Once \MF\ is working, you should be able to diagnose most errors with
//! the \.{show} commands and other diagnostic features. But for the initial
//! stages of debugging, and for the revelation of really deep mysteries, you
//! can compile \MF\ with a few more aids, including the \PASCAL\ runtime
//! checks and its debugger. An additional routine called |debug_help|
//! will also come into play when you type `\.D' after an error message;
//! |debug_help| also occurs just before a fatal error causes \MF\ to succumb.
//! @^debugging@>
//! @^system dependencies@>
//!
//! The interface to |debug_help| is primitive, but it is good enough when used
//! with a \PASCAL\ debugger that allows you to set breakpoints and to read
//! variables and change their values. After getting the prompt `\.{debug \#}', you
//! type either a negative number (this exits |debug_help|), or zero (this
//! goes to a location where you can set a breakpoint, thereby entering into
//! dialog with the \PASCAL\ debugger), or a positive number |m| followed by
//! an argument |n|. The meaning of |m| and |n| will be clear from the
//! program below. (If |m=13|, there is an additional argument, |l|.)
//! @.debug \#@>
//!
//! @d breakpoint=888 {place where a breakpoint is desirable}
//!
//! @<Last-minute...@>=
//! @!debug procedure debug_help; {routine to display various things}
//! label breakpoint,exit;
//! var @!k,@!l,@!m,@!n:integer;
//! begin clear_terminal;
//!   loop begin wake_up_terminal;
//!   print_nl("debug # (-1 to exit):"); update_terminal;
//! @.debug \#@>
//!   read(term_in,m);
//!   if m<0 then return
//!   else if m=0 then
//!     begin goto breakpoint;@/ {go to every declared label at least once}
//!     breakpoint: m:=0; @{'BREAKPOINT'@}@/
//!     end
//!   else  begin read(term_in,n);
//!     case m of
//!     @t\4@>@<Numbered cases for |debug_help|@>@;
//!     othercases print("?")
//!     endcases;
//!     end;
//!   end;
//! exit:end;
//! gubed
//!
