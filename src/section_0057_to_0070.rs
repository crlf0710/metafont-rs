//! @ To end a line of text output, we call |print_ln|.
//!
//! @<Basic print...@>=
//! procedure print_ln; {prints an end-of-line}
//! begin case selector of
//! term_and_log: begin wterm_cr; wlog_cr;
//!   term_offset:=0; file_offset:=0;
//!   end;
//! log_only: begin wlog_cr; file_offset:=0;
//!   end;
//! term_only: begin wterm_cr; term_offset:=0;
//!   end;
//! no_print,pseudo,new_string: do_nothing;
//! end; {there are no other cases}
//! end; {note that |tally| is not affected}
//!
//! @ The |print_char| procedure sends one character to the desired destination,
//! using the |xchr| array to map it into an external character compatible with
//! |input_ln|. All printing comes through |print_ln| or |print_char|.
//!
//! @<Basic printing...@>=
//! procedure print_char(@!s:ASCII_code); {prints a single character}
//! begin case selector of
//! term_and_log: begin wterm(xchr[s]); wlog(xchr[s]);
//!   incr(term_offset); incr(file_offset);
//!   if term_offset=max_print_line then
//!     begin wterm_cr; term_offset:=0;
//!     end;
//!   if file_offset=max_print_line then
//!     begin wlog_cr; file_offset:=0;
//!     end;
//!   end;
//! log_only: begin wlog(xchr[s]); incr(file_offset);
//!   if file_offset=max_print_line then print_ln;
//!   end;
//! term_only: begin wterm(xchr[s]); incr(term_offset);
//!   if term_offset=max_print_line then print_ln;
//!   end;
//! no_print: do_nothing;
//! pseudo: if tally<trick_count then trick_buf[tally mod error_line]:=s;
//! new_string: begin if pool_ptr<pool_size then append_char(s);
//!   end; {we drop characters if the string space is full}
//! end; {there are no other cases}
//! incr(tally);
//! end;
//!
//! @ An entire string is output by calling |print|. Note that if we are outputting
//! the single standard ASCII character \.c, we could call |print("c")|, since
//! |"c"=99| is the number of a single-character string, as explained above. But
//! |print_char("c")| is quicker, so \MF\ goes directly to the |print_char|
//! routine when it knows that this is safe. (The present implementation
//! assumes that it is always safe to print a visible ASCII character.)
//! @^system dependencies@>
//!
//! @<Basic print...@>=
//! procedure print(@!s:integer); {prints string |s|}
//! var @!j:pool_pointer; {current character code position}
//! begin if (s<0)or(s>=str_ptr) then s:="???"; {this can't happen}
//! @.???@>
//! if (s<256)and(selector>pseudo) then print_char(s)
//! else begin j:=str_start[s];
//!   while j<str_start[s+1] do
//!     begin print_char(so(str_pool[j])); incr(j);
//!     end;
//!   end;
//! end;
//!
//! @ Sometimes it's necessary to print a string whose characters
//! may not be visible ASCII codes. In that case |slow_print| is used.
//!
//! @<Basic print...@>=
//! procedure slow_print(@!s:integer); {prints string |s|}
//! var @!j:pool_pointer; {current character code position}
//! begin if (s<0)or(s>=str_ptr) then s:="???"; {this can't happen}
//! @.???@>
//! if (s<256)and(selector>pseudo) then print_char(s)
//! else begin j:=str_start[s];
//!   while j<str_start[s+1] do
//!     begin print(so(str_pool[j])); incr(j);
//!     end;
//!   end;
//! end;
//!
//! @ Here is the very first thing that \MF\ prints: a headline that identifies
//! the version number and base name. The |term_offset| variable is temporarily
//! incorrect, but the discrepancy is not serious since we assume that this
//! part of the program is system dependent.
//! @^system dependencies@>
//!
//! @<Initialize the output...@>=
//! wterm(banner);
//! if base_ident=0 then wterm_ln(' (no base preloaded)')
//! else  begin slow_print(base_ident); print_ln;
//!   end;
//! update_terminal;
//!
//! @ The procedure |print_nl| is like |print|, but it makes sure that the
//! string appears at the beginning of a new line.
//!
//! @<Basic print...@>=
//! procedure print_nl(@!s:str_number); {prints string |s| at beginning of line}
//! begin if ((term_offset>0)and(odd(selector)))or@|
//!   ((file_offset>0)and(selector>=log_only)) then print_ln;
//! print(s);
//! end;
//!
//! @ An array of digits in the range |0..9| is printed by |print_the_digs|.
//!
//! @<Basic print...@>=
//! procedure print_the_digs(@!k:eight_bits);
//!   {prints |dig[k-1]|$\,\ldots\,$|dig[0]|}
//! begin while k>0 do
//!   begin decr(k); print_char("0"+dig[k]);
//!   end;
//! end;
//!
//! @ The following procedure, which prints out the decimal representation of a
//! given integer |n|, has been written carefully so that it works properly
//! if |n=0| or if |(-n)| would cause overflow. It does not apply |mod| or |div|
//! to negative arguments, since such operations are not implemented consistently
//! by all \PASCAL\ compilers.
//!
//! @<Basic print...@>=
//! procedure print_int(@!n:integer); {prints an integer in decimal form}
//! var k:0..23; {index to current digit; we assume that $\vert n\vert<10^{23}$}
//! @!m:integer; {used to negate |n| in possibly dangerous cases}
//! begin k:=0;
//! if n<0 then
//!   begin print_char("-");
//!   if n>-100000000 then negate(n)
//!   else  begin m:=-1-n; n:=m div 10; m:=(m mod 10)+1; k:=1;
//!     if m<10 then dig[0]:=m
//!     else  begin dig[0]:=0; incr(n);
//!       end;
//!     end;
//!   end;
//! repeat dig[k]:=n mod 10; n:=n div 10; incr(k);
//! until n=0;
//! print_the_digs(k);
//! end;
//!
//! @ \MF\ also makes use of a trivial procedure to print two digits. The
//! following subroutine is usually called with a parameter in the range |0<=n<=99|.
//!
//! @p procedure print_dd(@!n:integer); {prints two least significant digits}
//! begin n:=abs(n) mod 100; print_char("0"+(n div 10));
//! print_char("0"+(n mod 10));
//! end;
//!
//! @ Here is a procedure that asks the user to type a line of input,
//! assuming that the |selector| setting is either |term_only| or |term_and_log|.
//! The input is placed into locations |first| through |last-1| of the
//! |buffer| array, and echoed on the transcript file if appropriate.
//!
//! This procedure is never called when |interaction<scroll_mode|.
//!
//! @d prompt_input(#)==begin wake_up_terminal; print(#); term_input;
//!     end {prints a string and gets a line of input}
//!
//! @p procedure term_input; {gets a line from the terminal}
//! var @!k:0..buf_size; {index into |buffer|}
//! begin update_terminal; {now the user sees the prompt for sure}
//! if not input_ln(term_in,true) then fatal_error("End of file on the terminal!");
//! @.End of file on the terminal@>
//! term_offset:=0; {the user's line ended with \<\rm return>}
//! decr(selector); {prepare to echo the input}
//! if last<>first then for k:=first to last-1 do print(buffer[k]);
//! print_ln; buffer[last]:="%"; incr(selector); {restore previous status}
//! end;
//!
//! @* \[6] Reporting errors.
//! When something anomalous is detected, \MF\ typically does something like this:
//! $$\vbox{\halign{#\hfil\cr
//! |print_err("Something anomalous has been detected");|\cr
//! |help3("This is the first line of my offer to help.")|\cr
//! |("This is the second line. I'm trying to")|\cr
//! |("explain the best way for you to proceed.");|\cr
//! |error;|\cr}}$$
//! A two-line help message would be given using |help2|, etc.; these informal
//! helps should use simple vocabulary that complements the words used in the
//! official error message that was printed. (Outside the U.S.A., the help
//! messages should preferably be translated into the local vernacular. Each
//! line of help is at most 60 characters long, in the present implementation,
//! so that |max_print_line| will not be exceeded.)
//!
//! The |print_err| procedure supplies a `\.!' before the official message,
//! and makes sure that the terminal is awake if a stop is going to occur.
//! The |error| procedure supplies a `\..' after the official message, then it
//! shows the location of the error; and if |interaction=error_stop_mode|,
//! it also enters into a dialog with the user, during which time the help
//! message may be printed.
//! @^system dependencies@>
//!
//! @ The global variable |interaction| has four settings, representing increasing
//! amounts of user interaction:
//!
//! @d batch_mode=0 {omits all stops and omits terminal output}
//! @d nonstop_mode=1 {omits all stops}
//! @d scroll_mode=2 {omits error stops}
//! @d error_stop_mode=3 {stops at every opportunity to interact}
//! @d print_err(#)==begin if interaction=error_stop_mode then wake_up_terminal;
//!   print_nl("! "); print(#);
//! @.!\relax@>
//!   end
//!
//! @<Glob...@>=
//! @!interaction:batch_mode..error_stop_mode; {current level of interaction}
//!
//! @ @<Set init...@>=interaction:=error_stop_mode;
//!
//! @ \MF\ is careful not to call |error| when the print |selector| setting
//! might be unusual. The only possible values of |selector| at the time of
//! error messages are
//!
//! \yskip\hang|no_print| (when |interaction=batch_mode|
//!   and |log_file| not yet open);
//!
//! \hang|term_only| (when |interaction>batch_mode| and |log_file| not yet open);
//!
//! \hang|log_only| (when |interaction=batch_mode| and |log_file| is open);
//!
//! \hang|term_and_log| (when |interaction>batch_mode| and |log_file| is open).
//!
//! @<Initialize the print |selector| based on |interaction|@>=
//! if interaction=batch_mode then selector:=no_print@+else selector:=term_only
//!
