//! @ Here now is the general |error| routine.
//!
//! @<Error hand...@>=
//! procedure error; {completes the job of error reporting}
//! label continue,exit;
//! var @!c:ASCII_code; {what the user types}
//! @!s1,@!s2,@!s3:integer; {used to save global variables when deleting tokens}
//! @!j:pool_pointer; {character position being printed}
//! begin if history<error_message_issued then history:=error_message_issued;
//! print_char("."); show_context;
//! if interaction=error_stop_mode then @<Get user's advice and |return|@>;
//! incr(error_count);
//! if error_count=100 then
//!   begin print_nl("(That makes 100 errors; please try again.)");
//! @.That makes 100 errors...@>
//!   history:=fatal_error_stop; jump_out;
//!   end;
//! @<Put help message on the transcript file@>;
//! exit:end;
//!
//! @ @<Get user's advice...@>=
//! loop@+begin continue: if interaction<>error_stop_mode then return;
//!   clear_for_error_prompt; prompt_input("? ");
//! @.?\relax@>
//!   if last=first then return;
//!   c:=buffer[first];
//!   if c>="a" then c:=c+"A"-"a"; {convert to uppercase}
//!   @<Interpret code |c| and |return| if done@>;
//!   end
//!
//! @ It is desirable to provide an `\.E' option here that gives the user
//! an easy way to return from \MF\ to the system editor, with the offending
//! line ready to be edited. But such an extension requires some system
//! wizardry, so the present implementation simply types out the name of the
//! file that should be
//! edited and the relevant line number.
//! @^system dependencies@>
//!
//! There is a secret `\.D' option available when the debugging routines haven't
//! been commented~out.
//! @^debugging@>
//!
//! @<Interpret code |c| and |return| if done@>=
//! case c of
//! "0","1","2","3","4","5","6","7","8","9": if deletions_allowed then
//!   @<Delete |c-"0"| tokens and |goto continue|@>;
//! @t\4\4@>@;@+@!debug "D":begin debug_help;goto continue;@+end;@+gubed@/
//! "E": if file_ptr>0 then if input_stack[file_ptr].name_field>=256 then
//!   begin print_nl("You want to edit file ");
//! @.You want to edit file x@>
//!   slow_print(input_stack[file_ptr].name_field);
//!   print(" at line "); print_int(line);@/
//!   interaction:=scroll_mode; jump_out;
//!   end;
//! "H": @<Print the help information and |goto continue|@>;
//! "I":@<Introduce new material from the terminal and |return|@>;
//! "Q","R","S":@<Change the interaction level and |return|@>;
//! "X":begin interaction:=scroll_mode; jump_out;
//!   end;
//! othercases do_nothing
//! endcases;@/
//! @<Print the menu of available options@>
//!
//! @ @<Print the menu...@>=
//! begin print("Type <return> to proceed, S to scroll future error messages,");@/
//! @.Type <return> to proceed...@>
//! print_nl("R to run without stopping, Q to run quietly,");@/
//! print_nl("I to insert something, ");
//! if file_ptr>0 then if input_stack[file_ptr].name_field>=256 then
//!   print("E to edit your file,");
//! if deletions_allowed then
//!   print_nl("1 or ... or 9 to ignore the next 1 to 9 tokens of input,");
//! print_nl("H for help, X to quit.");
//! end
//!
//! @ Here the author of \MF\ apologizes for making use of the numerical
//! relation between |"Q"|, |"R"|, |"S"|, and the desired interaction settings
//! |batch_mode|, |nonstop_mode|, |scroll_mode|.
//! @^Knuth, Donald Ervin@>
//!
//! @<Change the interaction...@>=
//! begin error_count:=0; interaction:=batch_mode+c-"Q";
//! print("OK, entering ");
//! case c of
//! "Q":begin print("batchmode"); decr(selector);
//!   end;
//! "R":print("nonstopmode");
//! "S":print("scrollmode");
//! end; {there are no other cases}
//! print("..."); print_ln; update_terminal; return;
//! end
//!
//! @ When the following code is executed, |buffer[(first+1)..(last-1)]| may
//! contain the material inserted by the user; otherwise another prompt will
//! be given. In order to understand this part of the program fully, you need
//! to be familiar with \MF's input stacks.
//!
//! @<Introduce new material...@>=
//! begin begin_file_reading; {enter a new syntactic level for terminal input}
//! if last>first+1 then
//!   begin loc:=first+1; buffer[first]:=" ";
//!   end
//! else  begin prompt_input("insert>"); loc:=first;
//! @.insert>@>
//!   end;
//! first:=last+1; cur_input.limit_field:=last; return;
//! end
//!
//! @ We allow deletion of up to 99 tokens at a time.
//!
//! @<Delete |c-"0"| tokens...@>=
//! begin s1:=cur_cmd; s2:=cur_mod; s3:=cur_sym; OK_to_interrupt:=false;
//! if (last>first+1) and (buffer[first+1]>="0")and(buffer[first+1]<="9") then
//!   c:=c*10+buffer[first+1]-"0"*11
//! else c:=c-"0";
//! while c>0 do
//!   begin get_next; {one-level recursive call of |error| is possible}
//!   @<Decrease the string reference count, if the current token is a string@>;
//!   decr(c);
//!   end;
//! cur_cmd:=s1; cur_mod:=s2; cur_sym:=s3; OK_to_interrupt:=true;
//! help2("I have just deleted some text, as you asked.")@/
//! ("You can now delete more, or insert, or whatever.");
//! show_context; goto continue;
//! end
//!
//! @ @<Print the help info...@>=
//! begin if use_err_help then
//!   begin @<Print the string |err_help|, possibly on several lines@>;
//!   use_err_help:=false;
//!   end
//! else  begin if help_ptr=0 then
//!     help2("Sorry, I don't know how to help in this situation.")@/
//!     @t\kern1em@>("Maybe you should try asking a human?");
//!   repeat decr(help_ptr); print(help_line[help_ptr]); print_ln;
//!   until help_ptr=0;
//!   end;
//! help4("Sorry, I already gave what help I could...")@/
//!   ("Maybe you should try asking a human?")@/
//!   ("An error might have occurred before I noticed any problems.")@/
//!   ("``If all else fails, read the instructions.''");@/
//! goto continue;
//! end
//!
//! @ @<Print the string |err_help|, possibly on several lines@>=
//! j:=str_start[err_help];
//! while j<str_start[err_help+1] do
//!   begin if str_pool[j]<>si("%") then print(so(str_pool[j]))
//!   else if j+1=str_start[err_help+1] then print_ln
//!   else if str_pool[j+1]<>si("%") then print_ln
//!   else  begin incr(j); print_char("%");
//!     end;
//!   incr(j);
//!   end
//!
//! @ @<Put help message on the transcript file@>=
//! if interaction>batch_mode then decr(selector); {avoid terminal output}
//! if use_err_help then
//!   begin print_nl("");
//!   @<Print the string |err_help|, possibly on several lines@>;
//!   end
//! else while help_ptr>0 do
//!   begin decr(help_ptr); print_nl(help_line[help_ptr]);
//!   end;
//! print_ln;
//! if interaction>batch_mode then incr(selector); {re-enable terminal output}
//! print_ln
//!
//! @ In anomalous cases, the print selector might be in an unknown state;
//! the following subroutine is called to fix things just enough to keep
//! running a bit longer.
//!
//! @p procedure normalize_selector;
//! begin if log_opened then selector:=term_and_log
//! else selector:=term_only;
//! if job_name=0 then open_log_file;
//! if interaction=batch_mode then decr(selector);
//! end;
//!
//! @ The following procedure prints \MF's last words before dying.
//!
//! @d succumb==begin if interaction=error_stop_mode then
//!     interaction:=scroll_mode; {no more interaction}
//!   if log_opened then error;
//!   @!debug if interaction>batch_mode then debug_help;@;@+gubed@;@/
//!   history:=fatal_error_stop; jump_out; {irrecoverable error}
//!   end
//!
//! @<Error hand...@>=
//! procedure fatal_error(@!s:str_number); {prints |s|, and that's it}
//! begin normalize_selector;@/
//! print_err("Emergency stop"); help1(s); succumb;
//! @.Emergency stop@>
//! end;
//!
//! @ Here is the most dreaded error message.
//!
//! @<Error hand...@>=
//! procedure overflow(@!s:str_number;@!n:integer); {stop due to finiteness}
//! begin normalize_selector;
//! print_err("METAFONT capacity exceeded, sorry [");
//! @.METAFONT capacity exceeded ...@>
//! print(s); print_char("="); print_int(n); print_char("]");
//! help2("If you really absolutely need more capacity,")@/
//!   ("you can ask a wizard to enlarge me.");
//! succumb;
//! end;
//!
//! @ The program might sometime run completely amok, at which point there is
//! no choice but to stop. If no previous error has been detected, that's bad
//! news; a message is printed that is really intended for the \MF\
//! maintenance person instead of the user (unless the user has been
//! particularly diabolical).  The index entries for `this can't happen' may
//! help to pinpoint the problem.
//! @^dry rot@>
//!
//! @<Error hand...@>=
//! procedure confusion(@!s:str_number);
//!   {consistency check violated; |s| tells where}
//! begin normalize_selector;
//! if history<error_message_issued then
//!   begin print_err("This can't happen ("); print(s); print_char(")");
//! @.This can't happen@>
//!   help1("I'm broken. Please show this to someone who can fix can fix");
//!   end
//! else  begin print_err("I can't go on meeting you like this");
//! @.I can't go on...@>
//!   help2("One of your faux pas seems to have wounded me deeply...")@/
//!     ("in fact, I'm barely conscious. Please fix it and try again.");
//!   end;
//! succumb;
//! end;
//!
//! @ Users occasionally want to interrupt \MF\ while it's running.
//! If the \PASCAL\ runtime system allows this, one can implement
//! a routine that sets the global variable |interrupt| to some nonzero value
//! when such an interrupt is signalled. Otherwise there is probably at least
//! a way to make |interrupt| nonzero using the \PASCAL\ debugger.
//! @^system dependencies@>
//! @^debugging@>
//!
//! @d check_interrupt==begin if interrupt<>0 then pause_for_instructions;
//!   end
//!
//! @<Global...@>=
//! @!interrupt:integer; {should \MF\ pause for instructions?}
//! @!OK_to_interrupt:boolean; {should interrupts be observed?}
//!
//! @ @<Set init...@>=
//! interrupt:=0; OK_to_interrupt:=true;
//!
//! @ When an interrupt has been detected, the program goes into its
//! highest interaction level and lets the user have the full flexibility of
//! the |error| routine.  \MF\ checks for interrupts only at times when it is
//! safe to do this.
//!
//! @p procedure pause_for_instructions;
//! begin if OK_to_interrupt then
//!   begin interaction:=error_stop_mode;
//!   if (selector=log_only)or(selector=no_print) then
//!     incr(selector);
//!   print_err("Interruption");
//! @.Interruption@>
//!   help3("You rang?")@/
//!   ("Try to insert an instruction for me (e.g., `I show x;'),")@/
//!   ("unless you just want to quit by typing `X'.");
//!   deletions_allowed:=false; error; deletions_allowed:=true;
//!   interrupt:=0;
//!   end;
//! end;
//!
//! @ Many of \MF's error messages state that a missing token has been
//! inserted behind the scenes. We can save string space and program space
//! by putting this common code into a subroutine.
//!
//! @p procedure missing_err(@!s:str_number);
//! begin print_err("Missing `"); print(s); print("' has been inserted");
//! @.Missing...inserted@>
//! end;
//!
