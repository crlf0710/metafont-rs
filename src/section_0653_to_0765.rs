//! @ The |back_error| routine is used when we want to restore or replace an
//! offending token just before issuing an error message.  We disable interrupts
//! during the call of |back_input| so that the help message won't be lost.
//!
//! @p procedure back_error; {back up one token and call |error|}
//! begin OK_to_interrupt:=false; back_input; OK_to_interrupt:=true; error;
//! end;
//! @#
//! procedure ins_error; {back up one inserted token and call |error|}
//! begin OK_to_interrupt:=false; back_input; token_type:=inserted;
//! OK_to_interrupt:=true; error;
//! end;
//!
//! @ The |begin_file_reading| procedure starts a new level of input for lines
//! of characters to be read from a file, or as an insertion from the
//! terminal. It does not take care of opening the file, nor does it set |loc|
//! or |limit| or |line|.
//! @^system dependencies@>
//!
//! @p procedure begin_file_reading;
//! begin if in_open=max_in_open then overflow("text input levels",max_in_open);
//! @:METAFONT capacity exceeded text input levels}{\quad text input levels@>
//! if first=buf_size then overflow("buffer size",buf_size);
//! @:METAFONT capacity exceeded buffer size}{\quad buffer size@>
//! incr(in_open); push_input; index:=in_open;
//! line_stack[index]:=line; start:=first;
//! name:=0; {|terminal_input| is now |true|}
//! end;
//!
//! @ Conversely, the variables must be downdated when such a level of input
//! is finished:
//!
//! @p procedure end_file_reading;
//! begin first:=start; line:=line_stack[index];
//! if index<>in_open then confusion("endinput");
//! @:this can't happen endinput}{\quad endinput@>
//! if name>2 then a_close(cur_file); {forget it}
//! pop_input; decr(in_open);
//! end;
//!
//! @ In order to keep the stack from overflowing during a long sequence of
//! inserted `\.{show}' commands, the following routine removes completed
//! error-inserted lines from memory.
//!
//! @p procedure clear_for_error_prompt;
//! begin while file_state and terminal_input and@|
//!   (input_ptr>0)and(loc=limit) do end_file_reading;
//! print_ln; clear_terminal;
//! end;
//!
//! @ To get \MF's whole input mechanism going, we perform the following
//! actions.
//!
//! @<Initialize the input routines@>=
//! begin input_ptr:=0; max_in_stack:=0;
//! in_open:=0; open_parens:=0; max_buf_stack:=0;
//! param_ptr:=0; max_param_stack:=0;
//! first:=1;
//! start:=1; index:=0; line:=0; name:=0;
//! force_eof:=false;
//! if not init_terminal then goto final_end;
//! limit:=last; first:=last+1; {|init_terminal| has set |loc| and |last|}
//! end;
//!
//! @* \[33] Getting the next token.
//! The heart of \MF's input mechanism is the |get_next| procedure, which
//! we shall develop in the next few sections of the program. Perhaps we
//! shouldn't actually call it the ``heart,'' however; it really acts as \MF's
//! eyes and mouth, reading the source files and gobbling them up. And it also
//! helps \MF\ to regurgitate stored token lists that are to be processed again.
//!
//! The main duty of |get_next| is to input one token and to set |cur_cmd|
//! and |cur_mod| to that token's command code and modifier. Furthermore, if
//! the input token is a symbolic token, that token's |hash| address
//! is stored in |cur_sym|; otherwise |cur_sym| is set to zero.
//!
//! Underlying this simple description is a certain amount of complexity
//! because of all the cases that need to be handled.
//! However, the inner loop of |get_next| is reasonably short and fast.
//!
//! @ Before getting into |get_next|, we need to consider a mechanism by which
//! \MF\ helps keep errors from propagating too far. Whenever the program goes
//! into a mode where it keeps calling |get_next| repeatedly until a certain
//! condition is met, it sets |scanner_status| to some value other than |normal|.
//! Then if an input file ends, or if an `\&{outer}' symbol appears,
//! an appropriate error recovery will be possible.
//!
//! The global variable |warning_info| helps in this error recovery by providing
//! additional information. For example, |warning_info| might indicate the
//! name of a macro whose replacement text is being scanned.
//!
//! @d normal=0 {|scanner_status| at ``quiet times''}
//! @d skipping=1 {|scanner_status| when false conditional text is being skipped}
//! @d flushing=2 {|scanner_status| when junk after a statement is being ignored}
//! @d absorbing=3 {|scanner_status| when a \&{text} parameter is being scanned}
//! @d var_defining=4 {|scanner_status| when a \&{vardef} is being scanned}
//! @d op_defining=5 {|scanner_status| when a macro \&{def} is being scanned}
//! @d loop_defining=6 {|scanner_status| when a \&{for} loop is being scanned}
//!
//! @<Glob...@>=
//! @!scanner_status:normal..loop_defining; {are we scanning at high speed?}
//! @!warning_info:integer; {if so, what else do we need to know,
//!     in case an error occurs?}
//!
//! @ @<Initialize the input routines@>=
//! scanner_status:=normal;
//!
//! @ The following subroutine
//! is called when an `\&{outer}' symbolic token has been scanned or
//! when the end of a file has been reached. These two cases are distinguished
//! by |cur_sym|, which is zero at the end of a file.
//!
//! @p function check_outer_validity:boolean;
//! var @!p:pointer; {points to inserted token list}
//! begin if scanner_status=normal then check_outer_validity:=true
//! else  begin deletions_allowed:=false;
//!   @<Back up an outer symbolic token so that it can be reread@>;
//!   if scanner_status>skipping then
//!     @<Tell the user what has run away and try to recover@>
//!   else  begin print_err("Incomplete if; all text was ignored after line ");
//! @.Incomplete if...@>
//!     print_int(warning_info);@/
//!     help3("A forbidden `outer' token occurred in skipped text.")@/
//!     ("This kind of error happens when you say `if...' and forget")@/
//!     ("the matching `fi'. I've inserted a `fi'; this might work.");
//!     if cur_sym=0 then help_line[2]:=@|
//!       "The file ended while I was skipping conditional text.";
//!     cur_sym:=frozen_fi; ins_error;
//!     end;
//!   deletions_allowed:=true; check_outer_validity:=false;
//!   end;
//! end;
//!
//! @ @<Back up an outer symbolic token so that it can be reread@>=
//! if cur_sym<>0 then
//!   begin p:=get_avail; info(p):=cur_sym;
//!   back_list(p); {prepare to read the symbolic token again}
//!   end
//!
//! @ @<Tell the user what has run away...@>=
//! begin runaway; {print the definition-so-far}
//! if cur_sym=0 then print_err("File ended")
//! @.File ended while scanning...@>
//! else  begin print_err("Forbidden token found");
//! @.Forbidden token found...@>
//!   end;
//! print(" while scanning ");
//! help4("I suspect you have forgotten an `enddef',")@/
//! ("causing me to read past where you wanted me to stop.")@/
//! ("I'll try to recover; but if the error is serious,")@/
//! ("you'd better type `E' or `X' now and fix your file.");@/
//! case scanner_status of
//! @t\4@>@<Complete the error message,
//!   and set |cur_sym| to a token that might help recover from the error@>@;
//! end; {there are no other cases}
//! ins_error;
//! end
//!
//! @ As we consider various kinds of errors, it is also appropriate to
//! change the first line of the help message just given; |help_line[3]|
//! points to the string that might be changed.
//!
//! @<Complete the error message,...@>=
//! flushing: begin print("to the end of the statement");
//!   help_line[3]:="A previous error seems to have propagated,";
//!   cur_sym:=frozen_semicolon;
//!   end;
//! absorbing: begin print("a text argument");
//!   help_line[3]:="It seems that a right delimiter was left out,";
//!   if warning_info=0 then cur_sym:=frozen_end_group
//!   else  begin cur_sym:=frozen_right_delimiter;
//!     equiv(frozen_right_delimiter):=warning_info;
//!     end;
//!   end;
//! var_defining, op_defining: begin print("the definition of ");
//!   if scanner_status=op_defining then slow_print(text(warning_info))
//!   else print_variable_name(warning_info);
//!   cur_sym:=frozen_end_def;
//!   end;
//! loop_defining: begin print("the text of a "); slow_print(text(warning_info));
//!   print(" loop");
//!   help_line[3]:="I suspect you have forgotten an `endfor',";
//!   cur_sym:=frozen_end_for;
//!   end;
//!
//! @ The |runaway| procedure displays the first part of the text that occurred
//! when \MF\ began its special |scanner_status|, if that text has been saved.
//!
//! @<Declare the procedure called |runaway|@>=
//! procedure runaway;
//! begin if scanner_status>flushing then
//!   begin print_nl("Runaway ");
//!   case scanner_status of
//!   absorbing: print("text?");
//!   var_defining,op_defining: print("definition?");
//!   loop_defining: print("loop?");
//!   end; {there are no other cases}
//!   print_ln; show_token_list(link(hold_head),null,error_line-10,0);
//!   end;
//! end;
//!
//! @ We need to mention a procedure that may be called by |get_next|.
//!
//! @p procedure@?firm_up_the_line; forward;
//!
//! @ And now we're ready to take the plunge into |get_next| itself.
//!
//! @d switch=25 {a label in |get_next|}
//! @d start_numeric_token=85 {another}
//! @d start_decimal_token=86 {and another}
//! @d fin_numeric_token=87
//!   {and still another, although |goto| is considered harmful}
//!
//! @p procedure get_next; {sets |cur_cmd|, |cur_mod|, |cur_sym| to next token}
//! @^inner loop@>
//! label restart, {go here to get the next input token}
//!   exit, {go here when the next input token has been got}
//!   found, {go here when the end of a symbolic token has been found}
//!   switch, {go here to branch on the class of an input character}
//!   start_numeric_token,start_decimal_token,fin_numeric_token,done;
//!     {go here at crucial stages when scanning a number}
//! var @!k:0..buf_size; {an index into |buffer|}
//! @!c:ASCII_code; {the current character in the buffer}
//! @!class:ASCII_code; {its class number}
//! @!n,@!f:integer; {registers for decimal-to-binary conversion}
//! begin restart: cur_sym:=0;
//! if file_state then
//! @<Input from external file; |goto restart| if no input found,
//!   or |return| if a non-symbolic token is found@>
//! else @<Input from token list; |goto restart| if end of list or
//!   if a parameter needs to be expanded,
//!   or |return| if a non-symbolic token is found@>;
//! @<Finish getting the symbolic token in |cur_sym|;
//!   |goto restart| if it is illegal@>;
//! exit:end;
//!
//! @ When a symbolic token is declared to be `\&{outer}', its command code
//! is increased by |outer_tag|.
//! @^inner loop@>
//!
//! @<Finish getting the symbolic token in |cur_sym|...@>=
//! cur_cmd:=eq_type(cur_sym); cur_mod:=equiv(cur_sym);
//! if cur_cmd>=outer_tag then
//!   if check_outer_validity then cur_cmd:=cur_cmd-outer_tag
//!   else goto restart
//!
//! @ A percent sign appears in |buffer[limit]|; this makes it unnecessary
//! to have a special test for end-of-line.
//! @^inner loop@>
//!
//! @<Input from external file;...@>=
//! begin switch: c:=buffer[loc]; incr(loc); class:=char_class[c];
//! case class of
//! digit_class: goto start_numeric_token;
//! period_class: begin class:=char_class[buffer[loc]];
//!   if class>period_class then goto switch
//!   else if class<period_class then {|class=digit_class|}
//!     begin n:=0; goto start_decimal_token;
//!     end;
//! @:. }{\..\ token@>
//!   end;
//! space_class: goto switch;
//! percent_class: begin @<Move to next line of file,
//!     or |goto restart| if there is no next line@>;
//!   check_interrupt;
//!   goto switch;
//!   end;
//! string_class: @<Get a string token and |return|@>;
//! isolated_classes: begin k:=loc-1; goto found;
//!   end;
//! invalid_class: @<Decry the invalid character and |goto restart|@>;
//! othercases do_nothing {letters, etc.}
//! endcases;@/
//! k:=loc-1;
//! while char_class[buffer[loc]]=class do incr(loc);
//! goto found;
//! start_numeric_token:@<Get the integer part |n| of a numeric token;
//!   set |f:=0| and |goto fin_numeric_token| if there is no decimal point@>;
//! start_decimal_token:@<Get the fraction part |f| of a numeric token@>;
//! fin_numeric_token:@<Pack the numeric and fraction parts of a numeric token
//!   and |return|@>;
//! found: cur_sym:=id_lookup(k,loc-k);
//! end
//!
//! @ We go to |restart| instead of to |switch|, because we might enter
//! |token_state| after the error has been dealt with
//! (cf.\ |clear_for_error_prompt|).
//!
//! @<Decry the invalid...@>=
//! begin print_err("Text line contains an invalid character");
//! @.Text line contains...@>
//! help2("A funny symbol that I can't read has just been input.")@/
//! ("Continue, and I'll forget that it ever happened.");@/
//! deletions_allowed:=false; error; deletions_allowed:=true;
//! goto restart;
//! end
//!
//! @ @<Get a string token and |return|@>=
//! begin if buffer[loc]="""" then cur_mod:=""
//! else  begin k:=loc; buffer[limit+1]:="""";
//!   repeat incr(loc);
//!   until buffer[loc]="""";
//!   if loc>limit then @<Decry the missing string delimiter and |goto restart|@>;
//!   if (loc=k+1) and (length(buffer[k])=1) then cur_mod:=buffer[k]
//!   else  begin str_room(loc-k);
//!     repeat append_char(buffer[k]); incr(k);
//!     until k=loc;
//!     cur_mod:=make_string;
//!     end;
//!   end;
//! incr(loc); cur_cmd:=string_token; return;
//! end
//!
//! @ We go to |restart| after this error message, not to |switch|,
//! because the |clear_for_error_prompt| routine might have reinstated
//! |token_state| after |error| has finished.
//!
//! @<Decry the missing string delimiter and |goto restart|@>=
//! begin loc:=limit; {the next character to be read on this line will be |"%"|}
//! print_err("Incomplete string token has been flushed");
//! @.Incomplete string token...@>
//! help3("Strings should finish on the same line as they began.")@/
//!   ("I've deleted the partial string; you might want to")@/
//!   ("insert another by typing, e.g., `I""new string""'.");@/
//! deletions_allowed:=false; error; deletions_allowed:=true; goto restart;
//! end
//!
//! @ @<Get the integer part |n| of a numeric token...@>=
//! n:=c-"0";
//! while char_class[buffer[loc]]=digit_class do
//!   begin if n<4096 then n:=10*n+buffer[loc]-"0";
//!   incr(loc);
//!   end;
//! if buffer[loc]="." then if char_class[buffer[loc+1]]=digit_class then goto done;
//! f:=0; goto fin_numeric_token;
//! done: incr(loc)
//!
//! @ @<Get the fraction part |f| of a numeric token@>=
//! k:=0;
//! repeat if k<17 then {digits for |k>=17| cannot affect the result}
//!   begin dig[k]:=buffer[loc]-"0"; incr(k);
//!   end;
//! incr(loc);
//! until char_class[buffer[loc]]<>digit_class;
//! f:=round_decimals(k);
//! if f=unity then
//!   begin incr(n); f:=0;
//!   end
//!
//! @ @<Pack the numeric and fraction parts of a numeric token and |return|@>=
//! if n<4096 then cur_mod:=n*unity+f
//! else  begin print_err("Enormous number has been reduced");
//! @.Enormous number...@>
//!   help2("I can't handle numbers bigger than about 4095.99998;")@/
//!   ("so I've changed your constant to that maximum amount.");@/
//!   deletions_allowed:=false; error; deletions_allowed:=true;
//!   cur_mod:=@'1777777777;
//!   end;
//! cur_cmd:=numeric_token; return
//!
//! @ Let's consider now what happens when |get_next| is looking at a token list.
//! @^inner loop@>
//!
//! @<Input from token list;...@>=
//! if loc>=hi_mem_min then {one-word token}
//!   begin cur_sym:=info(loc); loc:=link(loc); {move to next}
//!   if cur_sym>=expr_base then
//!     if cur_sym>=suffix_base then
//!       @<Insert a suffix or text parameter and |goto restart|@>
//!     else  begin cur_cmd:=capsule_token;
//!       cur_mod:=param_stack[param_start+cur_sym-(expr_base)];
//!       cur_sym:=0; return;
//!       end;
//!   end
//! else if loc>null then
//!   @<Get a stored numeric or string or capsule token and |return|@>
//! else  begin {we are done with this token list}
//!   end_token_list; goto restart; {resume previous level}
//!   end
//!
//! @ @<Insert a suffix or text parameter...@>=
//! begin if cur_sym>=text_base then cur_sym:=cur_sym-param_size;
//!   {|param_size=text_base-suffix_base|}
//! begin_token_list(param_stack[param_start+cur_sym-(suffix_base)],parameter);
//! goto restart;
//! end
//!
//! @ @<Get a stored numeric or string or capsule token...@>=
//! begin if name_type(loc)=token then
//!   begin cur_mod:=value(loc);
//!   if type(loc)=known then cur_cmd:=numeric_token
//!   else  begin cur_cmd:=string_token; add_str_ref(cur_mod);
//!     end;
//!   end
//! else  begin cur_mod:=loc; cur_cmd:=capsule_token;
//!   end;
//! loc:=link(loc); return;
//! end
//!
//! @ All of the easy branches of |get_next| have now been taken care of.
//! There is one more branch.
//!
//! @<Move to next line of file, or |goto restart|...@>=
//! if name>2 then @<Read next line of file into |buffer|, or
//!   |goto restart| if the file has ended@>
//! else  begin if input_ptr>0 then
//!      {text was inserted during error recovery or by \&{scantokens}}
//!     begin end_file_reading; goto restart; {resume previous level}
//!     end;
//!   if selector<log_only then open_log_file;
//!   if interaction>nonstop_mode then
//!     begin if limit=start then {previous line was empty}
//!       print_nl("(Please type a command or say `end')");
//! @.Please type...@>
//!     print_ln; first:=start;
//!     prompt_input("*"); {input on-line into |buffer|}
//! @.*\relax@>
//!     limit:=last; buffer[limit]:="%";
//!     first:=limit+1; loc:=start;
//!     end
//!   else fatal_error("*** (job aborted, no legal end found)");
//! @.job aborted@>
//!     {nonstop mode, which is intended for overnight batch processing,
//!     never waits for on-line input}
//!   end
//!
//! @ The global variable |force_eof| is normally |false|; it is set |true|
//! by an \&{endinput} command.
//!
//! @<Glob...@>=
//! @!force_eof:boolean; {should the next \&{input} be aborted early?}
//!
//! @ @<Read next line of file into |buffer|, or
//!   |goto restart| if the file has ended@>=
//! begin incr(line); first:=start;
//! if not force_eof then
//!   begin if input_ln(cur_file,true) then {not end of file}
//!     firm_up_the_line {this sets |limit|}
//!   else force_eof:=true;
//!   end;
//! if force_eof then
//!   begin print_char(")"); decr(open_parens);
//!   update_terminal; {show user that file has been read}
//!   force_eof:=false;
//!   end_file_reading; {resume previous level}
//!   if check_outer_validity then goto restart@+else goto restart;
//!   end;
//! buffer[limit]:="%"; first:=limit+1; loc:=start; {ready to read}
//! end
//!
//! @ If the user has set the |pausing| parameter to some positive value,
//! and if nonstop mode has not been selected, each line of input is displayed
//! on the terminal and the transcript file, followed by `\.{=>}'.
//! \MF\ waits for a response. If the response is null (i.e., if nothing is
//! typed except perhaps a few blank spaces), the original
//! line is accepted as it stands; otherwise the line typed is
//! used instead of the line in the file.
//!
//! @p procedure firm_up_the_line;
//! var @!k:0..buf_size; {an index into |buffer|}
//! begin limit:=last;
//! if internal[pausing]>0 then if interaction>nonstop_mode then
//!   begin wake_up_terminal; print_ln;
//!   if start<limit then for k:=start to limit-1 do print(buffer[k]);
//!   first:=limit; prompt_input("=>"); {wait for user response}
//! @.=>@>
//!   if last>first then
//!     begin for k:=first to last-1 do {move line down in buffer}
//!       buffer[k+start-first]:=buffer[k];
//!     limit:=start+last-first;
//!     end;
//!   end;
//! end;
//!
//! @* \[34] Scanning macro definitions.
//! \MF\ has a variety of ways to tuck tokens away into token lists for later
//! use: Macros can be defined with \&{def}, \&{vardef}, \&{primarydef}, etc.;
//! repeatable code can be defined with \&{for}, \&{forever}, \&{forsuffixes}.
//! All such operations are handled by the routines in this part of the program.
//!
//! The modifier part of each command code is zero for the ``ending delimiters''
//! like \&{enddef} and \&{endfor}.
//!
//! @d start_def=1 {command modifier for \&{def}}
//! @d var_def=2 {command modifier for \&{vardef}}
//! @d end_def=0 {command modifier for \&{enddef}}
//! @d start_forever=1 {command modifier for \&{forever}}
//! @d end_for=0 {command modifier for \&{endfor}}
//!
//! @<Put each...@>=
//! primitive("def",macro_def,start_def);@/
//! @!@:def_}{\&{def} primitive@>
//! primitive("vardef",macro_def,var_def);@/
//! @!@:var_def_}{\&{vardef} primitive@>
//! primitive("primarydef",macro_def,secondary_primary_macro);@/
//! @!@:primary_def_}{\&{primarydef} primitive@>
//! primitive("secondarydef",macro_def,tertiary_secondary_macro);@/
//! @!@:secondary_def_}{\&{secondarydef} primitive@>
//! primitive("tertiarydef",macro_def,expression_tertiary_macro);@/
//! @!@:tertiary_def_}{\&{tertiarydef} primitive@>
//! primitive("enddef",macro_def,end_def); eqtb[frozen_end_def]:=eqtb[cur_sym];@/
//! @!@:end_def_}{\&{enddef} primitive@>
//! @#
//! primitive("for",iteration,expr_base);@/
//! @!@:for_}{\&{for} primitive@>
//! primitive("forsuffixes",iteration,suffix_base);@/
//! @!@:for_suffixes_}{\&{forsuffixes} primitive@>
//! primitive("forever",iteration,start_forever);@/
//! @!@:forever_}{\&{forever} primitive@>
//! primitive("endfor",iteration,end_for); eqtb[frozen_end_for]:=eqtb[cur_sym];@/
//! @!@:end_for_}{\&{endfor} primitive@>
//!
//! @ @<Cases of |print_cmd...@>=
//! macro_def:if m<=var_def then
//!     if m=start_def then print("def")
//!     else if m<start_def then print("enddef")
//!     else print("vardef")
//!   else if m=secondary_primary_macro then print("primarydef")
//!   else if m=tertiary_secondary_macro then print("secondarydef")
//!   else print("tertiarydef");
//! iteration: if m<=start_forever then
//!     if m=start_forever then print("forever")@+else print("endfor")
//!   else if m=expr_base then print("for")@+else print("forsuffixes");
//!
//! @ Different macro-absorbing operations have different syntaxes, but they
//! also have a lot in common. There is a list of special symbols that are to
//! be replaced by parameter tokens; there is a special command code that
//! ends the definition; the quotation conventions are identical.  Therefore
//! it makes sense to have most of the work done by a single subroutine. That
//! subroutine is called |scan_toks|.
//!
//! The first parameter to |scan_toks| is the command code that will
//! terminate scanning (either |macro_def| or |iteration|).
//!
//! The second parameter, |subst_list|, points to a (possibly empty) list
//! of two-word nodes whose |info| and |value| fields specify symbol tokens
//! before and after replacement. The list will be returned to free storage
//! by |scan_toks|.
//!
//! The third parameter is simply appended to the token list that is built.
//! And the final parameter tells how many of the special operations
//! \.{\#\AT!}, \.{\AT!}, and \.{\AT!\#} are to be replaced by suffix parameters.
//! When such parameters are present, they are called \.{(SUFFIX0)},
//! \.{(SUFFIX1)}, and \.{(SUFFIX2)}.
//!
//! @p function scan_toks(@!terminator:command_code;
//!   @!subst_list,@!tail_end:pointer;@!suffix_count:small_number):pointer;
//! label done,found;
//! var @!p:pointer; {tail of the token list being built}
//! @!q:pointer; {temporary for link management}
//! @!balance:integer; {left delimiters minus right delimiters}
//! begin p:=hold_head; balance:=1; link(hold_head):=null;
//! loop@+  begin get_next;
//!   if cur_sym>0 then
//!     begin @<Substitute for |cur_sym|, if it's on the |subst_list|@>;
//!     if cur_cmd=terminator then
//!       @<Adjust the balance; |goto done| if it's zero@>
//!     else if cur_cmd=macro_special then
//!       @<Handle quoted symbols, \.{\#\AT!}, \.{\AT!}, or \.{\AT!\#}@>;
//!     end;
//!   link(p):=cur_tok; p:=link(p);
//!   end;
//! done: link(p):=tail_end; flush_node_list(subst_list);
//! scan_toks:=link(hold_head);
//! end;
//!
//! @ @<Substitute for |cur_sym|...@>=
//! begin q:=subst_list;
//! while q<>null do
//!   begin if info(q)=cur_sym then
//!     begin cur_sym:=value(q); cur_cmd:=relax; goto found;
//!     end;
//!   q:=link(q);
//!   end;
//! found:end
//!
//! @ @<Adjust the balance; |goto done| if it's zero@>=
//! if cur_mod>0 then incr(balance)
//! else  begin decr(balance);
//!   if balance=0 then goto done;
//!   end
//!
//! @ Four commands are intended to be used only within macro texts: \&{quote},
//! \.{\#\AT!}, \.{\AT!}, and \.{\AT!\#}. They are variants of a single command
//! code called |macro_special|.
//!
//! @d quote=0 {|macro_special| modifier for \&{quote}}
//! @d macro_prefix=1 {|macro_special| modifier for \.{\#\AT!}}
//! @d macro_at=2 {|macro_special| modifier for \.{\AT!}}
//! @d macro_suffix=3 {|macro_special| modifier for \.{\AT!\#}}
//!
//! @<Put each...@>=
//! primitive("quote",macro_special,quote);@/
//! @!@:quote_}{\&{quote} primitive@>
//! primitive("#@@",macro_special,macro_prefix);@/
//! @!@:]]]\#\AT!_}{\.{\#\AT!} primitive@>
//! primitive("@@",macro_special,macro_at);@/
//! @!@:]]]\AT!_}{\.{\AT!} primitive@>
//! primitive("@@#",macro_special,macro_suffix);@/
//! @!@:]]]\AT!\#_}{\.{\AT!\#} primitive@>
//!
//! @ @<Cases of |print_cmd...@>=
//! macro_special: case m of
//!   macro_prefix: print("#@@");
//!   macro_at: print_char("@@");
//!   macro_suffix: print("@@#");
//!   othercases print("quote")
//!   endcases;
//!
//! @ @<Handle quoted...@>=
//! begin if cur_mod=quote then get_next
//! else if cur_mod<=suffix_count then cur_sym:=suffix_base-1+cur_mod;
//! end
//!
//! @ Here is a routine that's used whenever a token will be redefined. If
//! the user's token is unredefinable, the `|frozen_inaccessible|' token is
//! substituted; the latter is redefinable but essentially impossible to use,
//! hence \MF's tables won't get fouled up.
//!
//! @p procedure get_symbol; {sets |cur_sym| to a safe symbol}
//! label restart;
//! begin restart: get_next;
//! if (cur_sym=0)or(cur_sym>frozen_inaccessible) then
//!   begin print_err("Missing symbolic token inserted");
//! @.Missing symbolic token...@>
//!   help3("Sorry: You can't redefine a number, string, or expr.")@/
//!     ("I've inserted an inaccessible symbol so that your")@/
//!     ("definition will be completed without mixing me up too badly.");
//!   if cur_sym>0 then
//!     help_line[2]:="Sorry: You can't redefine my error-recovery tokens."
//!   else if cur_cmd=string_token then delete_str_ref(cur_mod);
//!   cur_sym:=frozen_inaccessible; ins_error; goto restart;
//!   end;
//! end;
//!
//! @ Before we actually redefine a symbolic token, we need to clear away its
//! former value, if it was a variable. The following stronger version of
//! |get_symbol| does that.
//!
//! @p procedure get_clear_symbol;
//! begin get_symbol; clear_symbol(cur_sym,false);
//! end;
//!
//! @ Here's another little subroutine; it checks that an equals sign
//! or assignment sign comes along at the proper place in a macro definition.
//!
//! @p procedure check_equals;
//! begin if cur_cmd<>equals then if cur_cmd<>assignment then
//!   begin missing_err("=");@/
//! @.Missing `='@>
//!   help5("The next thing in this `def' should have been `=',")@/
//!     ("because I've already looked at the definition heading.")@/
//!     ("But don't worry; I'll pretend that an equals sign")@/
//!     ("was present. Everything from here to `enddef'")@/
//!     ("will be the replacement text of this macro.");
//!   back_error;
//!   end;
//! end;
//!
//! @ A \&{primarydef}, \&{secondarydef}, or \&{tertiarydef} is rather easily
//! handled now that we have |scan_toks|.  In this case there are
//! two parameters, which will be \.{EXPR0} and \.{EXPR1} (i.e.,
//! |expr_base| and |expr_base+1|).
//!
//! @p procedure make_op_def;
//! var @!m:command_code; {the type of definition}
//! @!p,@!q,@!r:pointer; {for list manipulation}
//! begin m:=cur_mod;@/
//! get_symbol; q:=get_node(token_node_size);
//! info(q):=cur_sym; value(q):=expr_base;@/
//! get_clear_symbol; warning_info:=cur_sym;@/
//! get_symbol; p:=get_node(token_node_size);
//! info(p):=cur_sym; value(p):=expr_base+1; link(p):=q;@/
//! get_next; check_equals;@/
//! scanner_status:=op_defining; q:=get_avail; ref_count(q):=null;
//! r:=get_avail; link(q):=r; info(r):=general_macro;
//! link(r):=scan_toks(macro_def,p,null,0);
//! scanner_status:=normal; eq_type(warning_info):=m;
//! equiv(warning_info):=q; get_x_next;
//! end;
//!
//! @ Parameters to macros are introduced by the keywords \&{expr},
//! \&{suffix}, \&{text}, \&{primary}, \&{secondary}, and \&{tertiary}.
//!
//! @<Put each...@>=
//! primitive("expr",param_type,expr_base);@/
//! @!@:expr_}{\&{expr} primitive@>
//! primitive("suffix",param_type,suffix_base);@/
//! @!@:suffix_}{\&{suffix} primitive@>
//! primitive("text",param_type,text_base);@/
//! @!@:text_}{\&{text} primitive@>
//! primitive("primary",param_type,primary_macro);@/
//! @!@:primary_}{\&{primary} primitive@>
//! primitive("secondary",param_type,secondary_macro);@/
//! @!@:secondary_}{\&{secondary} primitive@>
//! primitive("tertiary",param_type,tertiary_macro);@/
//! @!@:tertiary_}{\&{tertiary} primitive@>
//!
//! @ @<Cases of |print_cmd...@>=
//! param_type:if m>=expr_base then
//!     if m=expr_base then print("expr")
//!     else if m=suffix_base then print("suffix")
//!     else print("text")
//!   else if m<secondary_macro then print("primary")
//!   else if m=secondary_macro then print("secondary")
//!   else print("tertiary");
//!
//! @ Let's turn next to the more complex processing associated with \&{def}
//! and \&{vardef}. When the following procedure is called, |cur_mod|
//! should be either |start_def| or |var_def|.
//!
//! @p @t\4@>@<Declare the procedure called |check_delimiter|@>@;
//! @t\4@>@<Declare the function called |scan_declared_variable|@>@;
//! procedure scan_def;
//! var @!m:start_def..var_def; {the type of definition}
//! @!n:0..3; {the number of special suffix parameters}
//! @!k:0..param_size; {the total number of parameters}
//! @!c:general_macro..text_macro; {the kind of macro we're defining}
//! @!r:pointer; {parameter-substitution list}
//! @!q:pointer; {tail of the macro token list}
//! @!p:pointer; {temporary storage}
//! @!base:halfword; {|expr_base|, |suffix_base|, or |text_base|}
//! @!l_delim,@!r_delim:pointer; {matching delimiters}
//! begin m:=cur_mod; c:=general_macro; link(hold_head):=null;@/
//! q:=get_avail; ref_count(q):=null; r:=null;@/
//! @<Scan the token or variable to be defined;
//!   set |n|, |scanner_status|, and |warning_info|@>;
//! k:=n;
//! if cur_cmd=left_delimiter then
//!   @<Absorb delimited parameters, putting them into lists |q| and |r|@>;
//! if cur_cmd=param_type then
//!   @<Absorb undelimited parameters, putting them into list |r|@>;
//! check_equals;
//! p:=get_avail; info(p):=c; link(q):=p;
//! @<Attach the replacement text to the tail of node |p|@>;
//! scanner_status:=normal; get_x_next;
//! end;
//!
//! @ We don't put `|frozen_end_group|' into the replacement text of
//! a \&{vardef}, because the user may want to redefine `\.{endgroup}'.
//!
//! @<Attach the replacement text to the tail of node |p|@>=
//! if m=start_def then link(p):=scan_toks(macro_def,r,null,n)
//! else  begin q:=get_avail; info(q):=bg_loc; link(p):=q;
//!   p:=get_avail; info(p):=eg_loc;
//!   link(q):=scan_toks(macro_def,r,p,n);
//!   end;
//! if warning_info=bad_vardef then flush_token_list(value(bad_vardef))
//!
//! @ @<Glob...@>=
//! @!bg_loc,@!eg_loc:1..hash_end;
//!   {hash addresses of `\.{begingroup}' and `\.{endgroup}'}
//!
//! @ @<Scan the token or variable to be defined;...@>=
//! if m=start_def then
//!   begin get_clear_symbol; warning_info:=cur_sym; get_next;
//!   scanner_status:=op_defining; n:=0;
//!   eq_type(warning_info):=defined_macro; equiv(warning_info):=q;
//!   end
//! else  begin p:=scan_declared_variable;
//!   flush_variable(equiv(info(p)),link(p),true);
//!   warning_info:=find_variable(p); flush_list(p);
//!   if warning_info=null then @<Change to `\.{a bad variable}'@>;
//!   scanner_status:=var_defining; n:=2;
//!   if cur_cmd=macro_special then if cur_mod=macro_suffix then {\.{\AT!\#}}
//!     begin n:=3; get_next;
//!     end;
//!   type(warning_info):=unsuffixed_macro-2+n; value(warning_info):=q;
//!   end {|suffixed_macro=unsuffixed_macro+1|}
//!
//! @ @<Change to `\.{a bad variable}'@>=
//! begin print_err("This variable already starts with a macro");
//! @.This variable already...@>
//! help2("After `vardef a' you can't say `vardef a.b'.")@/
//!   ("So I'll have to discard this definition.");
//! error; warning_info:=bad_vardef;
//! end
//!
//! @ @<Initialize table entries...@>=
//! name_type(bad_vardef):=root; link(bad_vardef):=frozen_bad_vardef;
//! equiv(frozen_bad_vardef):=bad_vardef; eq_type(frozen_bad_vardef):=tag_token;
//!
//! @ @<Absorb delimited parameters, putting them into lists |q| and |r|@>=
//! repeat l_delim:=cur_sym; r_delim:=cur_mod; get_next;
//! if (cur_cmd=param_type)and(cur_mod>=expr_base) then base:=cur_mod
//! else  begin print_err("Missing parameter type; `expr' will be assumed");
//! @.Missing parameter type@>
//!   help1("You should've had `expr' or `suffix' or `text' here.");
//!   back_error; base:=expr_base;
//!   end;
//! @<Absorb parameter tokens for type |base|@>;
//! check_delimiter(l_delim,r_delim);
//! get_next;
//! until cur_cmd<>left_delimiter
//!
//! @ @<Absorb parameter tokens for type |base|@>=
//! repeat link(q):=get_avail; q:=link(q); info(q):=base+k;@/
//! get_symbol; p:=get_node(token_node_size); value(p):=base+k; info(p):=cur_sym;
//! if k=param_size then overflow("parameter stack size",param_size);
//! @:METAFONT capacity exceeded parameter stack size}{\quad parameter stack size@>
//! incr(k); link(p):=r; r:=p; get_next;
//! until cur_cmd<>comma
//!
//! @ @<Absorb undelimited parameters, putting them into list |r|@>=
//! begin p:=get_node(token_node_size);
//! if cur_mod<expr_base then
//!   begin c:=cur_mod; value(p):=expr_base+k;
//!   end
//! else  begin value(p):=cur_mod+k;
//!   if cur_mod=expr_base then c:=expr_macro
//!   else if cur_mod=suffix_base then c:=suffix_macro
//!   else c:=text_macro;
//!   end;
//! if k=param_size then overflow("parameter stack size",param_size);
//! incr(k); get_symbol; info(p):=cur_sym; link(p):=r; r:=p; get_next;
//! if c=expr_macro then if cur_cmd=of_token then
//!   begin c:=of_macro; p:=get_node(token_node_size);
//!   if k=param_size then overflow("parameter stack size",param_size);
//!   value(p):=expr_base+k; get_symbol; info(p):=cur_sym;
//!   link(p):=r; r:=p; get_next;
//!   end;
//! end
//!
//! @* \[35] Expanding the next token.
//! Only a few command codes |<min_command| can possibly be returned by
//! |get_next|; in increasing order, they are
//! |if_test|, |fi_or_else|, |input|, |iteration|, |repeat_loop|,
//! |exit_test|, |relax|, |scan_tokens|, |expand_after|, and |defined_macro|.
//!
//! \MF\ usually gets the next token of input by saying |get_x_next|. This is
//! like |get_next| except that it keeps getting more tokens until
//! finding |cur_cmd>=min_command|. In other words, |get_x_next| expands
//! macros and removes conditionals or iterations or input instructions that
//! might be present.
//!
//! It follows that |get_x_next| might invoke itself recursively. In fact,
//! there is massive recursion, since macro expansion can involve the
//! scanning of arbitrarily complex expressions, which in turn involve
//! macro expansion and conditionals, etc.
//! @^recursion@>
//!
//! Therefore it's necessary to declare a whole bunch of |forward|
//! procedures at this point, and to insert some other procedures
//! that will be invoked by |get_x_next|.
//!
//! @p procedure@?scan_primary; forward;@t\2@>
//! procedure@?scan_secondary; forward;@t\2@>
//! procedure@?scan_tertiary; forward;@t\2@>
//! procedure@?scan_expression; forward;@t\2@>
//! procedure@?scan_suffix; forward;@t\2@>@/
//! @t\4@>@<Declare the procedure called |macro_call|@>@;@/
//! procedure@?get_boolean; forward;@t\2@>
//! procedure@?pass_text; forward;@t\2@>
//! procedure@?conditional; forward;@t\2@>
//! procedure@?start_input; forward;@t\2@>
//! procedure@?begin_iteration; forward;@t\2@>
//! procedure@?resume_iteration; forward;@t\2@>
//! procedure@?stop_iteration; forward;@t\2@>
//!
//! @ An auxiliary subroutine called |expand| is used by |get_x_next|
//! when it has to do exotic expansion commands.
//!
//! @p procedure expand;
//! var @!p:pointer; {for list manipulation}
//! @!k:integer; {something that we hope is |<=buf_size|}
//! @!j:pool_pointer; {index into |str_pool|}
//! begin if internal[tracing_commands]>unity then if cur_cmd<>defined_macro then
//!   show_cur_cmd_mod;
//! case cur_cmd of
//! if_test:conditional; {this procedure is discussed in Part 36 below}
//! fi_or_else:@<Terminate the current conditional and skip to \&{fi}@>;
//! input:@<Initiate or terminate input from a file@>;
//! iteration:if cur_mod=end_for then
//!     @<Scold the user for having an extra \&{endfor}@>
//!   else begin_iteration; {this procedure is discussed in Part 37 below}
//! repeat_loop: @<Repeat a loop@>;
//! exit_test: @<Exit a loop if the proper time has come@>;
//! relax: do_nothing;
//! expand_after: @<Expand the token after the next token@>;
//! scan_tokens: @<Put a string into the input buffer@>;
//! defined_macro:macro_call(cur_mod,null,cur_sym);
//! end; {there are no other cases}
//! end;
//!
//! @ @<Scold the user...@>=
//! begin print_err("Extra `endfor'");
//! @.Extra `endfor'@>
//! help2("I'm not currently working on a for loop,")@/
//!   ("so I had better not try to end anything.");@/
//! error;
//! end
//!
//! @ The processing of \&{input} involves the |start_input| subroutine,
//! which will be declared later; the processing of \&{endinput} is trivial.
//!
//! @<Put each...@>=
//! primitive("input",input,0);@/
//! @!@:input_}{\&{input} primitive@>
//! primitive("endinput",input,1);@/
//! @!@:end_input_}{\&{endinput} primitive@>
//!
//! @ @<Cases of |print_cmd_mod|...@>=
//! input: if m=0 then print("input")@+else print("endinput");
//!
//! @ @<Initiate or terminate input...@>=
//! if cur_mod>0 then force_eof:=true
//! else start_input
//!
//! @ We'll discuss the complicated parts of loop operations later. For now
//! it suffices to know that there's a global variable called |loop_ptr|
//! that will be |null| if no loop is in progress.
//!
//! @<Repeat a loop@>=
//! begin while token_state and(loc=null) do end_token_list; {conserve stack space}
//! if loop_ptr=null then
//!   begin print_err("Lost loop");
//! @.Lost loop@>
//!   help2("I'm confused; after exiting from a loop, I still seem")@/
//!     ("to want to repeat it. I'll try to forget the problem.");@/
//!   error;
//!   end
//! else resume_iteration; {this procedure is in Part 37 below}
//! end
//!
//! @ @<Exit a loop if the proper time has come@>=
//! begin get_boolean;
//! if internal[tracing_commands]>unity then show_cmd_mod(nullary,cur_exp);
//! if cur_exp=true_code then
//!   if loop_ptr=null then
//!     begin print_err("No loop is in progress");
//! @.No loop is in progress@>
//!     help1("Why say `exitif' when there's nothing to exit from?");
//!     if cur_cmd=semicolon then error@+else back_error;
//!     end
//!   else @<Exit prematurely from an iteration@>
//! else if cur_cmd<>semicolon then
//!   begin missing_err(";");@/
//! @.Missing `;'@>
//!   help2("After `exitif <boolean expr>' I expect to see a semicolon.")@/
//!   ("I shall pretend that one was there."); back_error;
//!   end;
//! end
//!
//! @ Here we use the fact that |forever_text| is the only |token_type| that
//! is less than |loop_text|.
//!
//! @<Exit prematurely...@>=
//! begin p:=null;
//! repeat if file_state then end_file_reading
//! else  begin if token_type<=loop_text then p:=start;
//!   end_token_list;
//!   end;
//! until p<>null;
//! if p<>info(loop_ptr) then fatal_error("*** (loop confusion)");
//! @.loop confusion@>
//! stop_iteration; {this procedure is in Part 37 below}
//! end
//!
//! @ @<Expand the token after the next token@>=
//! begin get_next;
//! p:=cur_tok; get_next;
//! if cur_cmd<min_command then expand else back_input;
//! back_list(p);
//! end
//!
//! @ @<Put a string into the input buffer@>=
//! begin get_x_next; scan_primary;
//! if cur_type<>string_type then
//!   begin disp_err(null,"Not a string");
//! @.Not a string@>
//!   help2("I'm going to flush this expression, since")@/
//!     ("scantokens should be followed by a known string.");
//!   put_get_flush_error(0);
//!   end
//! else  begin back_input;
//!   if length(cur_exp)>0 then @<Pretend we're reading a new one-line file@>;
//!   end;
//! end
//!
//! @ @<Pretend we're reading a new one-line file@>=
//! begin begin_file_reading; name:=2;
//! k:=first+length(cur_exp);
//! if k>=max_buf_stack then
//!   begin if k>=buf_size then
//!     begin max_buf_stack:=buf_size;
//!     overflow("buffer size",buf_size);
//! @:METAFONT capacity exceeded buffer size}{\quad buffer size@>
//!     end;
//!   max_buf_stack:=k+1;
//!   end;
//! j:=str_start[cur_exp]; limit:=k;
//! while first<limit do
//!   begin buffer[first]:=so(str_pool[j]); incr(j); incr(first);
//!   end;
//! buffer[limit]:="%"; first:=limit+1; loc:=start; flush_cur_exp(0);
//! end
//!
//! @ Here finally is |get_x_next|.
//!
//! The expression scanning routines to be considered later
//! communicate via the global quantities |cur_type| and |cur_exp|;
//! we must be very careful to save and restore these quantities while
//! macros are being expanded.
//! @^inner loop@>
//!
//! @p procedure get_x_next;
//! var @!save_exp:pointer; {a capsule to save |cur_type| and |cur_exp|}
//! begin get_next;
//! if cur_cmd<min_command then
//!   begin save_exp:=stash_cur_exp;
//!   repeat if cur_cmd=defined_macro then macro_call(cur_mod,null,cur_sym)
//!   else expand;
//!   get_next;
//!   until cur_cmd>=min_command;
//!   unstash_cur_exp(save_exp); {that restores |cur_type| and |cur_exp|}
//!   end;
//! end;
//!
//! @ Now let's consider the |macro_call| procedure, which is used to start up
//! all user-defined macros. Since the arguments to a macro might be expressions,
//! |macro_call| is recursive.
//! @^recursion@>
//!
//! The first parameter to |macro_call| points to the reference count of the
//! token list that defines the macro. The second parameter contains any
//! arguments that have already been parsed (see below).  The third parameter
//! points to the symbolic token that names the macro. If the third parameter
//! is |null|, the macro was defined by \&{vardef}, so its name can be
//! reconstructed from the prefix and ``at'' arguments found within the
//! second parameter.
//!
//! What is this second parameter? It's simply a linked list of one-word items,
//! whose |info| fields point to the arguments. In other words, if |arg_list=null|,
//! no arguments have been scanned yet; otherwise |info(arg_list)| points to
//! the first scanned argument, and |link(arg_list)| points to the list of
//! further arguments (if any).
//!
//! Arguments of type \&{expr} are so-called capsules, which we will
//! discuss later when we concentrate on expressions; they can be
//! recognized easily because their |link| field is |void|. Arguments of type
//! \&{suffix} and \&{text} are token lists without reference counts.
//!
//! @ After argument scanning is complete, the arguments are moved to the
//! |param_stack|. (They can't be put on that stack any sooner, because
//! the stack is growing and shrinking in unpredictable ways as more arguments
//! are being acquired.)  Then the macro body is fed to the scanner; i.e.,
//! the replacement text of the macro is placed at the top of the \MF's
//! input stack, so that |get_next| will proceed to read it next.
//!
//! @<Declare the procedure called |macro_call|@>=
//! @t\4@>@<Declare the procedure called |print_macro_name|@>@;
//! @t\4@>@<Declare the procedure called |print_arg|@>@;
//! @t\4@>@<Declare the procedure called |scan_text_arg|@>@;
//! procedure macro_call(@!def_ref,@!arg_list,@!macro_name:pointer);
//!   {invokes a user-defined sequence of commands}
//! label found;
//! var @!r:pointer; {current node in the macro's token list}
//! @!p,@!q:pointer; {for list manipulation}
//! @!n:integer; {the number of arguments}
//! @!l_delim,@!r_delim:pointer; {a delimiter pair}
//! @!tail:pointer; {tail of the argument list}
//! begin r:=link(def_ref); add_mac_ref(def_ref);
//! if arg_list=null then n:=0
//! else @<Determine the number |n| of arguments already supplied,
//!   and set |tail| to the tail of |arg_list|@>;
//! if internal[tracing_macros]>0 then
//!   @<Show the text of the macro being expanded, and the existing arguments@>;
//! @<Scan the remaining arguments, if any; set |r| to the first token
//!   of the replacement text@>;
//! @<Feed the arguments and replacement text to the scanner@>;
//! end;
//!
//! @ @<Show the text of the macro...@>=
//! begin begin_diagnostic; print_ln; print_macro_name(arg_list,macro_name);
//! if n=3 then print("@@#"); {indicate a suffixed macro}
//! show_macro(def_ref,null,100000);
//! if arg_list<>null then
//!   begin n:=0; p:=arg_list;
//!   repeat q:=info(p);
//!   print_arg(q,n,0);
//!   incr(n); p:=link(p);
//!   until p=null;
//!   end;
//! end_diagnostic(false);
//! end
//!
//! @ @<Declare the procedure called |print_macro_name|@>=
//! procedure print_macro_name(@!a,@!n:pointer);
//! var @!p,@!q:pointer; {they traverse the first part of |a|}
//! begin if n<>null then slow_print(text(n))
//! else  begin p:=info(a);
//!   if p=null then slow_print(text(info(info(link(a)))))
//!   else  begin q:=p;
//!     while link(q)<>null do q:=link(q);
//!     link(q):=info(link(a));
//!     show_token_list(p,null,1000,0);
//!     link(q):=null;
//!     end;
//!   end;
//! end;
//!
//! @ @<Declare the procedure called |print_arg|@>=
//! procedure print_arg(@!q:pointer;@!n:integer;@!b:pointer);
//! begin if link(q)=void then print_nl("(EXPR")
//! else if (b<text_base)and(b<>text_macro) then print_nl("(SUFFIX")
//! else print_nl("(TEXT");
//! print_int(n); print(")<-");
//! if link(q)=void then print_exp(q,1)
//! else show_token_list(q,null,1000,0);
//! end;
//!
//! @ @<Determine the number |n| of arguments already supplied...@>=
//! begin n:=1; tail:=arg_list;
//! while link(tail)<>null do
//!   begin incr(n); tail:=link(tail);
//!   end;
//! end
//!
//! @ @<Scan the remaining arguments, if any; set |r|...@>=
//! cur_cmd:=comma+1; {anything |<>comma| will do}
//! while info(r)>=expr_base do
//!   begin @<Scan the delimited argument represented by |info(r)|@>;
//!   r:=link(r);
//!   end;
//! if cur_cmd=comma then
//!   begin print_err("Too many arguments to ");
//! @.Too many arguments...@>
//!   print_macro_name(arg_list,macro_name); print_char(";");
//!   print_nl("  Missing `"); slow_print(text(r_delim));
//! @.Missing `)'...@>
//!   print("' has been inserted");
//!   help3("I'm going to assume that the comma I just read was a")@/
//!    ("right delimiter, and then I'll begin expanding the macro.")@/
//!    ("You might want to delete some tokens before continuing.");
//!   error;
//!   end;
//! if info(r)<>general_macro then @<Scan undelimited argument(s)@>;
//! r:=link(r)
//!
//! @ At this point, the reader will find it advisable to review the explanation
//! of token list format that was presented earlier, paying special attention to
//! the conventions that apply only at the beginning of a macro's token list.
//!
//! On the other hand, the reader will have to take the expression-parsing
//! aspects of the following program on faith; we will explain |cur_type|
//! and |cur_exp| later. (Several things in this program depend on each other,
//! and it's necessary to jump into the circle somewhere.)
//!
//! @<Scan the delimited argument represented by |info(r)|@>=
//! if cur_cmd<>comma then
//!   begin get_x_next;
//!   if cur_cmd<>left_delimiter then
//!     begin print_err("Missing argument to ");
//! @.Missing argument...@>
//!     print_macro_name(arg_list,macro_name);
//!     help3("That macro has more parameters than you thought.")@/
//!      ("I'll continue by pretending that each missing argument")@/
//!      ("is either zero or null.");
//!     if info(r)>=suffix_base then
//!       begin cur_exp:=null; cur_type:=token_list;
//!       end
//!     else  begin cur_exp:=0; cur_type:=known;
//!       end;
//!     back_error; cur_cmd:=right_delimiter; goto found;
//!     end;
//!   l_delim:=cur_sym; r_delim:=cur_mod;
//!   end;
//! @<Scan the argument represented by |info(r)|@>;
//! if cur_cmd<>comma then @<Check that the proper right delimiter was present@>;
//! found:  @<Append the current expression to |arg_list|@>
//!
//! @ @<Check that the proper right delim...@>=
//! if (cur_cmd<>right_delimiter)or(cur_mod<>l_delim) then
//!   if info(link(r))>=expr_base then
//!     begin missing_err(",");
//! @.Missing `,'@>
//!     help3("I've finished reading a macro argument and am about to")@/
//!       ("read another; the arguments weren't delimited correctly.")@/
//!        ("You might want to delete some tokens before continuing.");
//!     back_error; cur_cmd:=comma;
//!     end
//!   else  begin missing_err(text(r_delim));
//! @.Missing `)'@>
//!     help2("I've gotten to the end of the macro parameter list.")@/
//!        ("You might want to delete some tokens before continuing.");
//!     back_error;
//!     end
//!
//! @ A \&{suffix} or \&{text} parameter will have been scanned as
//! a token list pointed to by |cur_exp|, in which case we will have
//! |cur_type=token_list|.
//!
//! @<Append the current expression to |arg_list|@>=
//! begin p:=get_avail;
//! if cur_type=token_list then info(p):=cur_exp
//! else info(p):=stash_cur_exp;
//! if internal[tracing_macros]>0 then
//!   begin begin_diagnostic; print_arg(info(p),n,info(r)); end_diagnostic(false);
//!   end;
//! if arg_list=null then arg_list:=p
//! else link(tail):=p;
//! tail:=p; incr(n);
//! end
//!
//! @ @<Scan the argument represented by |info(r)|@>=
//! if info(r)>=text_base then scan_text_arg(l_delim,r_delim)
//! else  begin get_x_next;
//!   if info(r)>=suffix_base then scan_suffix
//!   else scan_expression;
//!   end
//!
//! @ The parameters to |scan_text_arg| are either a pair of delimiters
//! or zero; the latter case is for undelimited text arguments, which
//! end with the first semicolon or \&{endgroup} or \&{end} that is not
//! contained in a group.
//!
//! @<Declare the procedure called |scan_text_arg|@>=
//! procedure scan_text_arg(@!l_delim,@!r_delim:pointer);
//! label done;
//! var @!balance:integer; {excess of |l_delim| over |r_delim|}
//! @!p:pointer; {list tail}
//! begin warning_info:=l_delim; scanner_status:=absorbing;
//! p:=hold_head; balance:=1; link(hold_head):=null;
//! loop@+  begin get_next;
//!   if l_delim=0 then @<Adjust the balance for an undelimited argument;
//!     |goto done| if done@>
//!   else @<Adjust the balance for a delimited argument;
//!     |goto done| if done@>;
//!   link(p):=cur_tok; p:=link(p);
//!   end;
//! done: cur_exp:=link(hold_head); cur_type:=token_list;
//! scanner_status:=normal;
//! end;
//!
//! @ @<Adjust the balance for a delimited argument...@>=
//! begin if cur_cmd=right_delimiter then
//!   begin if cur_mod=l_delim then
//!     begin decr(balance);
//!     if balance=0 then goto done;
//!     end;
//!   end
//! else if cur_cmd=left_delimiter then if cur_mod=r_delim then incr(balance);
//! end
//!
//! @ @<Adjust the balance for an undelimited...@>=
//! begin if end_of_statement then {|cur_cmd=semicolon|, |end_group|, or |stop|}
//!   begin if balance=1 then goto done
//!   else if cur_cmd=end_group then decr(balance);
//!   end
//! else if cur_cmd=begin_group then incr(balance);
//! end
//!
//! @ @<Scan undelimited argument(s)@>=
//! begin if info(r)<text_macro then
//!   begin get_x_next;
//!   if info(r)<>suffix_macro then
//!     if (cur_cmd=equals)or(cur_cmd=assignment) then get_x_next;
//!   end;
//! case info(r) of
//! primary_macro:scan_primary;
//! secondary_macro:scan_secondary;
//! tertiary_macro:scan_tertiary;
//! expr_macro:scan_expression;
//! of_macro:@<Scan an expression followed by `\&{of} $\langle$primary$\rangle$'@>;
//! suffix_macro:@<Scan a suffix with optional delimiters@>;
//! text_macro:scan_text_arg(0,0);
//! end; {there are no other cases}
//! back_input; @<Append the current expression to |arg_list|@>;
//! end
//!
//! @ @<Scan an expression followed by `\&{of} $\langle$primary$\rangle$'@>=
//! begin scan_expression; p:=get_avail; info(p):=stash_cur_exp;
//! if internal[tracing_macros]>0 then
//!   begin begin_diagnostic; print_arg(info(p),n,0); end_diagnostic(false);
//!   end;
//! if arg_list=null then arg_list:=p@+else link(tail):=p;
//! tail:=p;incr(n);
//! if cur_cmd<>of_token then
//!   begin missing_err("of"); print(" for ");
//! @.Missing `of'@>
//!   print_macro_name(arg_list,macro_name);
//!   help1("I've got the first argument; will look now for the other.");
//!   back_error;
//!   end;
//! get_x_next; scan_primary;
//! end
//!
//! @ @<Scan a suffix with optional delimiters@>=
//! begin if cur_cmd<>left_delimiter then l_delim:=null
//! else  begin l_delim:=cur_sym; r_delim:=cur_mod; get_x_next;
//!   end;
//! scan_suffix;
//! if l_delim<>null then
//!   begin if(cur_cmd<>right_delimiter)or(cur_mod<>l_delim) then
//!     begin missing_err(text(r_delim));
//! @.Missing `)'@>
//!     help2("I've gotten to the end of the macro parameter list.")@/
//!        ("You might want to delete some tokens before continuing.");
//!     back_error;
//!     end;
//!   get_x_next;
//!   end;
//! end
//!
//! @ Before we put a new token list on the input stack, it is wise to clean off
//! all token lists that have recently been depleted. Then a user macro that ends
//! with a call to itself will not require unbounded stack space.
//!
//! @<Feed the arguments and replacement text to the scanner@>=
//! while token_state and(loc=null) do end_token_list; {conserve stack space}
//! if param_ptr+n>max_param_stack then
//!   begin max_param_stack:=param_ptr+n;
//!   if max_param_stack>param_size then
//!     overflow("parameter stack size",param_size);
//! @:METAFONT capacity exceeded parameter stack size}{\quad parameter stack size@>
//!   end;
//! begin_token_list(def_ref,macro); name:=macro_name; loc:=r;
//! if n>0 then
//!   begin p:=arg_list;
//!   repeat param_stack[param_ptr]:=info(p); incr(param_ptr); p:=link(p);
//!   until p=null;
//!   flush_list(arg_list);
//!   end
//!
//! @ It's sometimes necessary to put a single argument onto |param_stack|.
//! The |stack_argument| subroutine does this.
//!
//! @p procedure stack_argument(@!p:pointer);
//! begin if param_ptr=max_param_stack then
//!   begin incr(max_param_stack);
//!   if max_param_stack>param_size then
//!     overflow("parameter stack size",param_size);
//! @:METAFONT capacity exceeded parameter stack size}{\quad parameter stack size@>
//!   end;
//! param_stack[param_ptr]:=p; incr(param_ptr);
//! end;
//!
//! @* \[36] Conditional processing.
//! Let's consider now the way \&{if} commands are handled.
//!
//! Conditions can be inside conditions, and this nesting has a stack
//! that is independent of other stacks.
//! Four global variables represent the top of the condition stack:
//! |cond_ptr| points to pushed-down entries, if~any; |cur_if| tells whether
//! we are processing \&{if} or \&{elseif}; |if_limit| specifies
//! the largest code of a |fi_or_else| command that is syntactically legal;
//! and |if_line| is the line number at which the current conditional began.
//!
//! If no conditions are currently in progress, the condition stack has the
//! special state |cond_ptr=null|, |if_limit=normal|, |cur_if=0|, |if_line=0|.
//! Otherwise |cond_ptr| points to a two-word node; the |type|, |name_type|, and
//! |link| fields of the first word contain |if_limit|, |cur_if|, and
//! |cond_ptr| at the next level, and the second word contains the
//! corresponding |if_line|.
//!
//! @d if_node_size=2 {number of words in stack entry for conditionals}
//! @d if_line_field(#)==mem[#+1].int
//! @d if_code=1 {code for \&{if} being evaluated}
//! @d fi_code=2 {code for \&{fi}}
//! @d else_code=3 {code for \&{else}}
//! @d else_if_code=4 {code for \&{elseif}}
//!
//! @<Glob...@>=
//! @!cond_ptr:pointer; {top of the condition stack}
//! @!if_limit:normal..else_if_code; {upper bound on |fi_or_else| codes}
//! @!cur_if:small_number; {type of conditional being worked on}
//! @!if_line:integer; {line where that conditional began}
//!
//! @ @<Set init...@>=
//! cond_ptr:=null; if_limit:=normal; cur_if:=0; if_line:=0;
//!
//! @ @<Put each...@>=
//! primitive("if",if_test,if_code);@/
//! @!@:if_}{\&{if} primitive@>
//! primitive("fi",fi_or_else,fi_code); eqtb[frozen_fi]:=eqtb[cur_sym];@/
//! @!@:fi_}{\&{fi} primitive@>
//! primitive("else",fi_or_else,else_code);@/
//! @!@:else_}{\&{else} primitive@>
//! primitive("elseif",fi_or_else,else_if_code);@/
//! @!@:else_if_}{\&{elseif} primitive@>
//!
//! @ @<Cases of |print_cmd_mod|...@>=
//! if_test,fi_or_else: case m of
//!   if_code:print("if");
//!   fi_code:print("fi");
//!   else_code:print("else");
//!   othercases print("elseif")
//!   endcases;
//!
//! @ Here is a procedure that ignores text until coming to an \&{elseif},
//! \&{else}, or \&{fi} at the current level of $\&{if}\ldots\&{fi}$
//! nesting. After it has acted, |cur_mod| will indicate the token that
//! was found.
//!
//! \MF's smallest two command codes are |if_test| and |fi_or_else|; this
//! makes the skipping process a bit simpler.
//!
//! @p procedure pass_text;
//! label done;
//! var l:integer;
//! begin scanner_status:=skipping; l:=0; warning_info:=line;
//! loop@+  begin get_next;
//!   if cur_cmd<=fi_or_else then
//!     if cur_cmd<fi_or_else then incr(l)
//!     else  begin if l=0 then goto done;
//!       if cur_mod=fi_code then decr(l);
//!       end
//!   else @<Decrease the string reference count,
//!     if the current token is a string@>;
//!   end;
//! done: scanner_status:=normal;
//! end;
//!
//! @ @<Decrease the string reference count...@>=
//! if cur_cmd=string_token then delete_str_ref(cur_mod)
//!
//! @ When we begin to process a new \&{if}, we set |if_limit:=if_code|; then
//! if \&{elseif} or \&{else} or \&{fi} occurs before the current \&{if}
//! condition has been evaluated, a colon will be inserted.
//! A construction like `\.{if fi}' would otherwise get \MF\ confused.
//!
//! @<Push the condition stack@>=
//! begin p:=get_node(if_node_size); link(p):=cond_ptr; type(p):=if_limit;
//! name_type(p):=cur_if; if_line_field(p):=if_line;
//! cond_ptr:=p; if_limit:=if_code; if_line:=line; cur_if:=if_code;
//! end
//!
//! @ @<Pop the condition stack@>=
//! begin p:=cond_ptr; if_line:=if_line_field(p);
//! cur_if:=name_type(p); if_limit:=type(p); cond_ptr:=link(p);
//! free_node(p,if_node_size);
//! end
//!
//! @ Here's a procedure that changes the |if_limit| code corresponding to
//! a given value of |cond_ptr|.
//!
//! @p procedure change_if_limit(@!l:small_number;@!p:pointer);
//! label exit;
//! var q:pointer;
//! begin if p=cond_ptr then if_limit:=l {that's the easy case}
//! else  begin q:=cond_ptr;
//!   loop@+  begin if q=null then confusion("if");
//! @:this can't happen if}{\quad if@>
//!     if link(q)=p then
//!       begin type(q):=l; return;
//!       end;
//!     q:=link(q);
//!     end;
//!   end;
//! exit:end;
//!
//! @ The user is supposed to put colons into the proper parts of conditional
//! statements. Therefore, \MF\ has to check for their presence.
//!
//! @p procedure check_colon;
//! begin if cur_cmd<>colon then
//!   begin missing_err(":");@/
//! @.Missing `:'@>
//!   help2("There should've been a colon after the condition.")@/
//!     ("I shall pretend that one was there.");@;
//!   back_error;
//!   end;
//! end;
//!
//! @ A condition is started when the |get_x_next| procedure encounters
//! an |if_test| command; in that case |get_x_next| calls |conditional|,
//! which is a recursive procedure.
//! @^recursion@>
//!
//! @p procedure conditional;
//! label exit,done,reswitch,found;
//! var @!save_cond_ptr:pointer; {|cond_ptr| corresponding to this conditional}
//! @!new_if_limit:fi_code..else_if_code; {future value of |if_limit|}
//! @!p:pointer; {temporary register}
//! begin @<Push the condition stack@>;@+save_cond_ptr:=cond_ptr;
//! reswitch: get_boolean; new_if_limit:=else_if_code;
//! if internal[tracing_commands]>unity then
//!   @<Display the boolean value of |cur_exp|@>;
//! found: check_colon;
//! if cur_exp=true_code then
//!   begin change_if_limit(new_if_limit,save_cond_ptr);
//!   return; {wait for \&{elseif}, \&{else}, or \&{fi}}
//!   end;
//! @<Skip to \&{elseif} or \&{else} or \&{fi}, then |goto done|@>;
//! done: cur_if:=cur_mod; if_line:=line;
//! if cur_mod=fi_code then @<Pop the condition stack@>
//! else if cur_mod=else_if_code then goto reswitch
//! else  begin cur_exp:=true_code; new_if_limit:=fi_code; get_x_next; goto found;
//!   end;
//! exit:end;
//!
//! @ In a construction like `\&{if} \&{if} \&{true}: $0=1$: \\{foo}
//! \&{else}: \\{bar} \&{fi}', the first \&{else}
//! that we come to after learning that the \&{if} is false is not the
//! \&{else} we're looking for. Hence the following curious logic is needed.
//!
//! @<Skip to \&{elseif}...@>=
//! loop@+  begin pass_text;
//!   if cond_ptr=save_cond_ptr then goto done
//!   else if cur_mod=fi_code then @<Pop the condition stack@>;
//!   end
//!
//!
//! @ @<Display the boolean value...@>=
//! begin begin_diagnostic;
//! if cur_exp=true_code then print("{true}")@+else print("{false}");
//! end_diagnostic(false);
//! end
//!
//! @ The processing of conditionals is complete except for the following
//! code, which is actually part of |get_x_next|. It comes into play when
//! \&{elseif}, \&{else}, or \&{fi} is scanned.
//!
//! @<Terminate the current conditional and skip to \&{fi}@>=
//! if cur_mod>if_limit then
//!   if if_limit=if_code then {condition not yet evaluated}
//!     begin missing_err(":");
//! @.Missing `:'@>
//!     back_input; cur_sym:=frozen_colon; ins_error;
//!     end
//!   else  begin print_err("Extra "); print_cmd_mod(fi_or_else,cur_mod);
//! @.Extra else@>
//! @.Extra elseif@>
//! @.Extra fi@>
//!     help1("I'm ignoring this; it doesn't match any if.");
//!     error;
//!     end
//! else  begin while cur_mod<>fi_code do pass_text; {skip to \&{fi}}
//!   @<Pop the condition stack@>;
//!   end
//!
//! @* \[37] Iterations.
//! To bring our treatment of |get_x_next| to a close, we need to consider what
//! \MF\ does when it sees \&{for}, \&{forsuffixes}, and \&{forever}.
//!
//! There's a global variable |loop_ptr| that keeps track of the \&{for} loops
//! that are currently active. If |loop_ptr=null|, no loops are in progress;
//! otherwise |info(loop_ptr)| points to the iterative text of the current
//! (innermost) loop, and |link(loop_ptr)| points to the data for any other
//! loops that enclose the current one.
//!
//! A loop-control node also has two other fields, called |loop_type| and
//! |loop_list|, whose contents depend on the type of loop:
//!
//! \yskip\indent|loop_type(loop_ptr)=null| means that |loop_list(loop_ptr)|
//! points to a list of one-word nodes whose |info| fields point to the
//! remaining argument values of a suffix list and expression list.
//!
//! \yskip\indent|loop_type(loop_ptr)=void| means that the current loop is
//! `\&{forever}'.
//!
//! \yskip\indent|loop_type(loop_ptr)=p>void| means that |value(p)|,
//! |step_size(p)|, and |final_value(p)| contain the data for an arithmetic
//! progression.
//!
//! \yskip\noindent In the latter case, |p| points to a ``progression node''
//! whose first word is not used. (No value could be stored there because the
//! link field of words in the dynamic memory area cannot be arbitrary.)
//!
//! @d loop_list_loc(#)==#+1 {where the |loop_list| field resides}
//! @d loop_type(#)==info(loop_list_loc(#)) {the type of \&{for} loop}
//! @d loop_list(#)==link(loop_list_loc(#)) {the remaining list elements}
//! @d loop_node_size=2 {the number of words in a loop control node}
//! @d progression_node_size=4 {the number of words in a progression node}
//! @d step_size(#)==mem[#+2].sc {the step size in an arithmetic progression}
//! @d final_value(#)==mem[#+3].sc {the final value in an arithmetic progression}
//!
//! @<Glob...@>=
//! @!loop_ptr:pointer; {top of the loop-control-node stack}
//!
//! @ @<Set init...@>=
//! loop_ptr:=null;
//!
//! @ If the expressions that define an arithmetic progression in
//! a \&{for} loop don't have known numeric values, the |bad_for|
//! subroutine screams at the user.
//!
//! @p procedure bad_for(@!s:str_number);
//! begin disp_err(null,"Improper "); {show the bad expression above the message}
//! @.Improper...replaced by 0@>
//! print(s); print(" has been replaced by 0");
//! help4("When you say `for x=a step b until c',")@/
//!   ("the initial value `a' and the step size `b'")@/
//!   ("and the final value `c' must have known numeric values.")@/
//!   ("I'm zeroing this one. Proceed, with fingers crossed.");
//! put_get_flush_error(0);
//! end;
//!
//! @ Here's what \MF\ does when \&{for}, \&{forsuffixes}, or \&{forever}
//! has just been scanned. (This code requires slight familiarity with
//! expression-parsing routines that we have not yet discussed; but it seems
//! to belong in the present part of the program, even though the author
//! didn't write it until later. The reader may wish to come back to it.)
//!
//! @p procedure begin_iteration;
//! label continue,done,found;
//! var @!m:halfword; {|expr_base| (\&{for}) or |suffix_base| (\&{forsuffixes})}
//! @!n:halfword; {hash address of the current symbol}
//! @!p,@!q,@!s,@!pp:pointer; {link manipulation registers}
//! begin m:=cur_mod; n:=cur_sym; s:=get_node(loop_node_size);
//! if m=start_forever then
//!   begin loop_type(s):=void; p:=null; get_x_next; goto found;
//!   end;
//! get_symbol; p:=get_node(token_node_size); info(p):=cur_sym; value(p):=m;@/
//! get_x_next;
//! if (cur_cmd<>equals)and(cur_cmd<>assignment) then
//!   begin missing_err("=");@/
//! @.Missing `='@>
//!   help3("The next thing in this loop should have been `=' or `:='.")@/
//!     ("But don't worry; I'll pretend that an equals sign")@/
//!     ("was present, and I'll look for the values next.");@/
//!   back_error;
//!   end;
//! @<Scan the values to be used in the loop@>;
//! found:@<Check for the presence of a colon@>;
//! @<Scan the loop text and put it on the loop control stack@>;
//! resume_iteration;
//! end;
//!
//! @ @<Check for the presence of a colon@>=
//! if cur_cmd<>colon then
//!   begin missing_err(":");@/
//! @.Missing `:'@>
//!   help3("The next thing in this loop should have been a `:'.")@/
//!     ("So I'll pretend that a colon was present;")@/
//!     ("everything from here to `endfor' will be iterated.");
//!   back_error;
//!   end
//!
//! @ We append a special |frozen_repeat_loop| token in place of the
//! `\&{endfor}' at the end of the loop. This will come through \MF's scanner
//! at the proper time to cause the loop to be repeated.
//!
//! (A user who tries some shenanigan like `\&{for} $\ldots$ \&{let} \&{endfor}'
//! will be foiled by the |get_symbol| routine, which keeps frozen
//! tokens unchanged. Furthermore the |frozen_repeat_loop| is an \&{outer}
//! token, so it won't be lost accidentally.)
//!
//! @ @<Scan the loop text...@>=
//! q:=get_avail; info(q):=frozen_repeat_loop;
//! scanner_status:=loop_defining; warning_info:=n;
//! info(s):=scan_toks(iteration,p,q,0); scanner_status:=normal;@/
//! link(s):=loop_ptr; loop_ptr:=s
//!
//! @ @<Initialize table...@>=
//! eq_type(frozen_repeat_loop):=repeat_loop+outer_tag;
//! text(frozen_repeat_loop):=" ENDFOR";
//!
//! @ The loop text is inserted into \MF's scanning apparatus by the
//! |resume_iteration| routine.
//!
//! @p procedure resume_iteration;
//! label not_found,exit;
//! var @!p,@!q:pointer; {link registers}
//! begin p:=loop_type(loop_ptr);
//! if p>void then {|p| points to a progression node}
//!   begin cur_exp:=value(p);
//!   if @<The arithmetic progression has ended@> then goto not_found;
//!   cur_type:=known; q:=stash_cur_exp; {make |q| an \&{expr} argument}
//!   value(p):=cur_exp+step_size(p); {set |value(p)| for the next iteration}
//!   end
//! else if p<void then
//!   begin p:=loop_list(loop_ptr);
//!   if p=null then goto not_found;
//!   loop_list(loop_ptr):=link(p); q:=info(p); free_avail(p);
//!   end
//! else  begin begin_token_list(info(loop_ptr),forever_text); return;
//!   end;
//! begin_token_list(info(loop_ptr),loop_text);
//! stack_argument(q);
//! if internal[tracing_commands]>unity then @<Trace the start of a loop@>;
//! return;
//! not_found:stop_iteration;
//! exit:end;
//!
//! @ @<The arithmetic progression has ended@>=
//! ((step_size(p)>0)and(cur_exp>final_value(p)))or@|
//!  ((step_size(p)<0)and(cur_exp<final_value(p)))
//!
//! @ @<Trace the start of a loop@>=
//! begin begin_diagnostic; print_nl("{loop value=");
//! @.loop value=n@>
//! if (q<>null)and(link(q)=void) then print_exp(q,1)
//! else show_token_list(q,null,50,0);
//! print_char("}"); end_diagnostic(false);
//! end
//!
//! @ A level of loop control disappears when |resume_iteration| has decided
//! not to resume, or when an \&{exitif} construction has removed the loop text
//! from the input stack.
//!
//! @p procedure stop_iteration;
//! var @!p,@!q:pointer; {the usual}
//! begin p:=loop_type(loop_ptr);
//! if p>void then free_node(p,progression_node_size)
//! else if p<void then
//!   begin q:=loop_list(loop_ptr);
//!   while q<>null do
//!     begin p:=info(q);
//!     if p<>null then
//!       if link(p)=void then {it's an \&{expr} parameter}
//!         begin recycle_value(p); free_node(p,value_node_size);
//!         end
//!       else flush_token_list(p); {it's a \&{suffix} or \&{text} parameter}
//!     p:=q; q:=link(q); free_avail(p);
//!     end;
//!   end;
//! p:=loop_ptr; loop_ptr:=link(p); flush_token_list(info(p));
//! free_node(p,loop_node_size);
//! end;
//!
//! @ Now that we know all about loop control, we can finish up
//! the missing portion of |begin_iteration| and we'll be done.
//!
//! The following code is performed after the `\.=' has been scanned in
//! a \&{for} construction (if |m=expr_base|) or a \&{forsuffixes} construction
//! (if |m=suffix_base|).
//!
//! @<Scan the values to be used in the loop@>=
//! loop_type(s):=null; q:=loop_list_loc(s); link(q):=null; {|link(q)=loop_list(s)|}
//! repeat get_x_next;
//! if m<>expr_base then scan_suffix
//! else  begin if cur_cmd>=colon then if cur_cmd<=comma then goto continue;
//!   scan_expression;
//!   if cur_cmd=step_token then if q=loop_list_loc(s) then
//!     @<Prepare for step-until construction and |goto done|@>;
//!   cur_exp:=stash_cur_exp;
//!   end;
//! link(q):=get_avail; q:=link(q); info(q):=cur_exp; cur_type:=vacuous;
//! continue: until cur_cmd<>comma;
//! done:
//!
//! @ @<Prepare for step-until construction and |goto done|@>=
//! begin if cur_type<>known then bad_for("initial value");
//! pp:=get_node(progression_node_size); value(pp):=cur_exp;@/
//! get_x_next; scan_expression;
//! if cur_type<>known then bad_for("step size");
//! step_size(pp):=cur_exp;
//! if cur_cmd<>until_token then
//!   begin missing_err("until");@/
//! @.Missing `until'@>
//!   help2("I assume you meant to say `until' after `step'.")@/
//!     ("So I'll look for the final value and colon next.");
//!   back_error;
//!   end;
//! get_x_next; scan_expression;
//! if cur_type<>known then bad_for("final value");
//! final_value(pp):=cur_exp; loop_type(s):=pp; goto done;
//! end
//!
