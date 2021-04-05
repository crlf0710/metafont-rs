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
//! @* \[38] File names.
//! It's time now to fret about file names.  Besides the fact that different
//! operating systems treat files in different ways, we must cope with the
//! fact that completely different naming conventions are used by different
//! groups of people. The following programs show what is required for one
//! particular operating system; similar routines for other systems are not
//! difficult to devise.
//! @^system dependencies@>
//!
//! \MF\ assumes that a file name has three parts: the name proper; its
//! ``extension''; and a ``file area'' where it is found in an external file
//! system.  The extension of an input file is assumed to be
//! `\.{.mf}' unless otherwise specified; it is `\.{.log}' on the
//! transcript file that records each run of \MF; it is `\.{.tfm}' on the font
//! metric files that describe characters in the fonts \MF\ creates; it is
//! `\.{.gf}' on the output files that specify generic font information; and it
//! is `\.{.base}' on the base files written by \.{INIMF} to initialize \MF.
//! The file area can be arbitrary on input files, but files are usually
//! output to the user's current area.  If an input file cannot be
//! found on the specified area, \MF\ will look for it on a special system
//! area; this special area is intended for commonly used input files.
//!
//! Simple uses of \MF\ refer only to file names that have no explicit
//! extension or area. For example, a person usually says `\.{input} \.{cmr10}'
//! instead of `\.{input} \.{cmr10.new}'. Simple file
//! names are best, because they make the \MF\ source files portable;
//! whenever a file name consists entirely of letters and digits, it should be
//! treated in the same way by all implementations of \MF. However, users
//! need the ability to refer to other files in their environment, especially
//! when responding to error messages concerning unopenable files; therefore
//! we want to let them use the syntax that appears in their favorite
//! operating system.
//!
//! @ \MF\ uses the same conventions that have proved to be satisfactory for
//! \TeX. In order to isolate the system-dependent aspects of file names, the
//! @^system dependencies@>
//! system-independent parts of \MF\ are expressed in terms
//! of three system-dependent
//! procedures called |begin_name|, |more_name|, and |end_name|. In
//! essence, if the user-specified characters of the file name are $c_1\ldots c_n$,
//! the system-independent driver program does the operations
//! $$|begin_name|;\,|more_name|(c_1);\,\ldots\,;\,|more_name|(c_n);
//! \,|end_name|.$$
//! These three procedures communicate with each other via global variables.
//! Afterwards the file name will appear in the string pool as three strings
//! called |cur_name|\penalty10000\hskip-.05em,
//! |cur_area|, and |cur_ext|; the latter two are null (i.e.,
//! |""|), unless they were explicitly specified by the user.
//!
//! Actually the situation is slightly more complicated, because \MF\ needs
//! to know when the file name ends. The |more_name| routine is a function
//! (with side effects) that returns |true| on the calls |more_name|$(c_1)$,
//! \dots, |more_name|$(c_{n-1})$. The final call |more_name|$(c_n)$
//! returns |false|; or, it returns |true| and $c_n$ is the last character
//! on the current input line. In other words,
//! |more_name| is supposed to return |true| unless it is sure that the
//! file name has been completely scanned; and |end_name| is supposed to be able
//! to finish the assembly of |cur_name|, |cur_area|, and |cur_ext| regardless of
//! whether $|more_name|(c_n)$ returned |true| or |false|.
//!
//! @<Glob...@>=
//! @!cur_name:str_number; {name of file just scanned}
//! @!cur_area:str_number; {file area just scanned, or \.{""}}
//! @!cur_ext:str_number; {file extension just scanned, or \.{""}}
//!
//! @ The file names we shall deal with for illustrative purposes have the
//! following structure:  If the name contains `\.>' or `\.:', the file area
//! consists of all characters up to and including the final such character;
//! otherwise the file area is null.  If the remaining file name contains
//! `\..', the file extension consists of all such characters from the first
//! remaining `\..' to the end, otherwise the file extension is null.
//! @^system dependencies@>
//!
//! We can scan such file names easily by using two global variables that keep track
//! of the occurrences of area and extension delimiters:
//!
//! @<Glob...@>=
//! @!area_delimiter:pool_pointer; {the most recent `\.>' or `\.:', if any}
//! @!ext_delimiter:pool_pointer; {the relevant `\..', if any}
//!
//! @ Input files that can't be found in the user's area may appear in a standard
//! system area called |MF_area|.
//! This system area name will, of course, vary from place to place.
//! @^system dependencies@>
//!
//! @d MF_area=="MFinputs:"
//! @.MFinputs@>
//!
//! @ Here now is the first of the system-dependent routines for file name scanning.
//! @^system dependencies@>
//!
//! @p procedure begin_name;
//! begin area_delimiter:=0; ext_delimiter:=0;
//! end;
//!
//! @ And here's the second.
//! @^system dependencies@>
//!
//! @p function more_name(@!c:ASCII_code):boolean;
//! begin if c=" " then more_name:=false
//! else  begin if (c=">")or(c=":") then
//!     begin area_delimiter:=pool_ptr; ext_delimiter:=0;
//!     end
//!   else if (c=".")and(ext_delimiter=0) then ext_delimiter:=pool_ptr;
//!   str_room(1); append_char(c); {contribute |c| to the current string}
//!   more_name:=true;
//!   end;
//! end;
//!
//! @ The third.
//! @^system dependencies@>
//!
//! @p procedure end_name;
//! begin if str_ptr+3>max_str_ptr then
//!   begin if str_ptr+3>max_strings then
//!     overflow("number of strings",max_strings-init_str_ptr);
//! @:METAFONT capacity exceeded number of strings}{\quad number of strings@>
//!   max_str_ptr:=str_ptr+3;
//!   end;
//! if area_delimiter=0 then cur_area:=""
//! else  begin cur_area:=str_ptr; incr(str_ptr);
//!   str_start[str_ptr]:=area_delimiter+1;
//!   end;
//! if ext_delimiter=0 then
//!   begin cur_ext:=""; cur_name:=make_string;
//!   end
//! else  begin cur_name:=str_ptr; incr(str_ptr);
//!   str_start[str_ptr]:=ext_delimiter; cur_ext:=make_string;
//!   end;
//! end;
//!
//! @ Conversely, here is a routine that takes three strings and prints a file
//! name that might have produced them. (The routine is system dependent, because
//! some operating systems put the file area last instead of first.)
//! @^system dependencies@>
//!
//! @<Basic printing...@>=
//! procedure print_file_name(@!n,@!a,@!e:integer);
//! begin slow_print(a); slow_print(n); slow_print(e);
//! end;
//!
//! @ Another system-dependent routine is needed to convert three internal
//! \MF\ strings
//! to the |name_of_file| value that is used to open files. The present code
//! allows both lowercase and uppercase letters in the file name.
//! @^system dependencies@>
//!
//! @d append_to_name(#)==begin c:=#; incr(k);
//!   if k<=file_name_size then name_of_file[k]:=xchr[c];
//!   end
//!
//! @p procedure pack_file_name(@!n,@!a,@!e:str_number);
//! var @!k:integer; {number of positions filled in |name_of_file|}
//! @!c: ASCII_code; {character being packed}
//! @!j:pool_pointer; {index into |str_pool|}
//! begin k:=0;
//! for j:=str_start[a] to str_start[a+1]-1 do append_to_name(so(str_pool[j]));
//! for j:=str_start[n] to str_start[n+1]-1 do append_to_name(so(str_pool[j]));
//! for j:=str_start[e] to str_start[e+1]-1 do append_to_name(so(str_pool[j]));
//! if k<=file_name_size then name_length:=k@+else name_length:=file_name_size;
//! for k:=name_length+1 to file_name_size do name_of_file[k]:=' ';
//! end;
//!
//! @ A messier routine is also needed, since base file names must be scanned
//! before \MF's string mechanism has been initialized. We shall use the
//! global variable |MF_base_default| to supply the text for default system areas
//! and extensions related to base files.
//! @^system dependencies@>
//!
//! @d base_default_length=18 {length of the |MF_base_default| string}
//! @d base_area_length=8 {length of its area part}
//! @d base_ext_length=5 {length of its `\.{.base}' part}
//! @d base_extension=".base" {the extension, as a \.{WEB} constant}
//!
//! @<Glob...@>=
//! @!MF_base_default:packed array[1..base_default_length] of char;
//!
//! @ @<Set init...@>=
//! MF_base_default:='MFbases:plain.base';
//! @.MFbases@>
//! @.plain@>
//! @^system dependencies@>
//!
//! @ @<Check the ``constant'' values for consistency@>=
//! if base_default_length>file_name_size then bad:=41;
//!
//! @ Here is the messy routine that was just mentioned. It sets |name_of_file|
//! from the first |n| characters of |MF_base_default|, followed by
//! |buffer[a..b]|, followed by the last |base_ext_length| characters of
//! |MF_base_default|.
//!
//! We dare not give error messages here, since \MF\ calls this routine before
//! the |error| routine is ready to roll. Instead, we simply drop excess characters,
//! since the error will be detected in another way when a strange file name
//! isn't found.
//! @^system dependencies@>
//!
//! @p procedure pack_buffered_name(@!n:small_number;@!a,@!b:integer);
//! var @!k:integer; {number of positions filled in |name_of_file|}
//! @!c: ASCII_code; {character being packed}
//! @!j:integer; {index into |buffer| or |MF_base_default|}
//! begin if n+b-a+1+base_ext_length>file_name_size then
//!   b:=a+file_name_size-n-1-base_ext_length;
//! k:=0;
//! for j:=1 to n do append_to_name(xord[MF_base_default[j]]);
//! for j:=a to b do append_to_name(buffer[j]);
//! for j:=base_default_length-base_ext_length+1 to base_default_length do
//!   append_to_name(xord[MF_base_default[j]]);
//! if k<=file_name_size then name_length:=k@+else name_length:=file_name_size;
//! for k:=name_length+1 to file_name_size do name_of_file[k]:=' ';
//! end;
//!
//! @ Here is the only place we use |pack_buffered_name|. This part of the program
//! becomes active when a ``virgin'' \MF\ is trying to get going, just after
//! the preliminary initialization, or when the user is substituting another
//! base file by typing `\.\&' after the initial `\.{**}' prompt.  The buffer
//! contains the first line of input in |buffer[loc..(last-1)]|, where
//! |loc<last| and |buffer[loc]<>" "|.
//!
//! @<Declare the function called |open_base_file|@>=
//! function open_base_file:boolean;
//! label found,exit;
//! var @!j:0..buf_size; {the first space after the file name}
//! begin j:=loc;
//! if buffer[loc]="&" then
//!   begin incr(loc); j:=loc; buffer[last]:=" ";
//!   while buffer[j]<>" " do incr(j);
//!   pack_buffered_name(0,loc,j-1); {try first without the system file area}
//!   if w_open_in(base_file) then goto found;
//!   pack_buffered_name(base_area_length,loc,j-1);
//!     {now try the system base file area}
//!   if w_open_in(base_file) then goto found;
//!   wake_up_terminal;
//!   wterm_ln('Sorry, I can''t find that base;',' will try PLAIN.');
//! @.Sorry, I can't find...@>
//!   update_terminal;
//!   end;
//!   {now pull out all the stops: try for the system \.{plain} file}
//! pack_buffered_name(base_default_length-base_ext_length,1,0);
//! if not w_open_in(base_file) then
//!   begin wake_up_terminal;
//!   wterm_ln('I can''t find the PLAIN base file!');
//! @.I can't find PLAIN...@>
//! @.plain@>
//!   open_base_file:=false; return;
//!   end;
//! found:loc:=j; open_base_file:=true;
//! exit:end;
//!
//! @ Operating systems often make it possible to determine the exact name (and
//! possible version number) of a file that has been opened. The following routine,
//! which simply makes a \MF\ string from the value of |name_of_file|, should
//! ideally be changed to deduce the full name of file~|f|, which is the file
//! most recently opened, if it is possible to do this in a \PASCAL\ program.
//! @^system dependencies@>
//!
//! This routine might be called after string memory has overflowed, hence
//! we dare not use `|str_room|'.
//!
//! @p function make_name_string:str_number;
//! var @!k:1..file_name_size; {index into |name_of_file|}
//! begin if (pool_ptr+name_length>pool_size)or(str_ptr=max_strings) then
//!   make_name_string:="?"
//! else  begin for k:=1 to name_length do append_char(xord[name_of_file[k]]);
//!   make_name_string:=make_string;
//!   end;
//! end;
//! function a_make_name_string(var @!f:alpha_file):str_number;
//! begin a_make_name_string:=make_name_string;
//! end;
//! function b_make_name_string(var @!f:byte_file):str_number;
//! begin b_make_name_string:=make_name_string;
//! end;
//! function w_make_name_string(var @!f:word_file):str_number;
//! begin w_make_name_string:=make_name_string;
//! end;
//!
//! @ Now let's consider the ``driver''
//! routines by which \MF\ deals with file names
//! in a system-independent manner.  First comes a procedure that looks for a
//! file name in the input by taking the information from the input buffer.
//! (We can't use |get_next|, because the conversion to tokens would
//! destroy necessary information.)
//!
//! This procedure doesn't allow semicolons or percent signs to be part of
//! file names, because of other conventions of \MF. The manual doesn't
//! use semicolons or percents immediately after file names, but some users
//! no doubt will find it natural to do so; therefore system-dependent
//! changes to allow such characters in file names should probably
//! be made with reluctance, and only when an entire file name that
//! includes special characters is ``quoted'' somehow.
//! @^system dependencies@>
//!
//! @p procedure scan_file_name;
//! label done;
//! begin begin_name;
//! while buffer[loc]=" " do incr(loc);
//! loop@+begin if (buffer[loc]=";")or(buffer[loc]="%") then goto done;
//!   if not more_name(buffer[loc]) then goto done;
//!   incr(loc);
//!   end;
//! done: end_name;
//! end;
//!
//! @ The global variable |job_name| contains the file name that was first
//! \&{input} by the user. This name is extended by `\.{.log}' and `\.{.gf}' and
//! `\.{.base}' and `\.{.tfm}' in the names of \MF's output files.
//!
//! @<Glob...@>=
//! @!job_name:str_number; {principal file name}
//! @!log_opened:boolean; {has the transcript file been opened?}
//! @!log_name:str_number; {full name of the log file}
//!
//! @ Initially |job_name=0|; it becomes nonzero as soon as the true name is known.
//! We have |job_name=0| if and only if the `\.{log}' file has not been opened,
//! except of course for a short time just after |job_name| has become nonzero.
//!
//! @<Initialize the output...@>=job_name:=0; log_opened:=false;
//!
//! @ Here is a routine that manufactures the output file names, assuming that
//! |job_name<>0|. It ignores and changes the current settings of |cur_area|
//! and |cur_ext|.
//!
//! @d pack_cur_name==pack_file_name(cur_name,cur_area,cur_ext)
//!
//! @p procedure pack_job_name(@!s:str_number); {|s = ".log"|, |".gf"|,
//!   |".tfm"|, or |base_extension|}
//! begin cur_area:=""; cur_ext:=s;
//! cur_name:=job_name; pack_cur_name;
//! end;
//!
//! @ Actually the main output file extension is usually something like
//! |".300gf"| instead of just |".gf"|; the additional number indicates the
//! resolution in pixels per inch, based on the setting of |hppp| when
//! the file is opened.
//!
//! @<Glob...@>=
//! @!gf_ext:str_number; {default extension for the output file}
//!
//! @ If some trouble arises when \MF\ tries to open a file, the following
//! routine calls upon the user to supply another file name. Parameter~|s|
//! is used in the error message to identify the type of file; parameter~|e|
//! is the default extension if none is given. Upon exit from the routine,
//! variables |cur_name|, |cur_area|, |cur_ext|, and |name_of_file| are
//! ready for another attempt at file opening.
//!
//! @p procedure prompt_file_name(@!s,@!e:str_number);
//! label done;
//! var @!k:0..buf_size; {index into |buffer|}
//! begin if interaction=scroll_mode then wake_up_terminal;
//! if s="input file name" then print_err("I can't find file `")
//! @.I can't find file x@>
//! else print_err("I can't write on file `");
//! @.I can't write on file x@>
//! print_file_name(cur_name,cur_area,cur_ext); print("'.");
//! if e=".mf" then show_context;
//! print_nl("Please type another "); print(s);
//! @.Please type...@>
//! if interaction<scroll_mode then
//!   fatal_error("*** (job aborted, file error in nonstop mode)");
//! @.job aborted, file error...@>
//! clear_terminal; prompt_input(": "); @<Scan file name in the buffer@>;
//! if cur_ext="" then cur_ext:=e;
//! pack_cur_name;
//! end;
//!
//! @ @<Scan file name in the buffer@>=
//! begin begin_name; k:=first;
//! while (buffer[k]=" ")and(k<last) do incr(k);
//! loop@+  begin if k=last then goto done;
//!   if not more_name(buffer[k]) then goto done;
//!   incr(k);
//!   end;
//! done:end_name;
//! end
//!
//! @ The |open_log_file| routine is used to open the transcript file and to help
//! it catch up to what has previously been printed on the terminal.
//!
//! @p procedure open_log_file;
//! var @!old_setting:0..max_selector; {previous |selector| setting}
//! @!k:0..buf_size; {index into |months| and |buffer|}
//! @!l:0..buf_size; {end of first input line}
//! @!m:integer; {the current month}
//! @!months:packed array [1..36] of char; {abbreviations of month names}
//! begin old_setting:=selector;
//! if job_name=0 then job_name:="mfput";
//! @.mfput@>
//! pack_job_name(".log");
//! while not a_open_out(log_file) do @<Try to get a different log file name@>;
//! log_name:=a_make_name_string(log_file);
//! selector:=log_only; log_opened:=true;
//! @<Print the banner line, including the date and time@>;
//! input_stack[input_ptr]:=cur_input; {make sure bottom level is in memory}
//! print_nl("**");
//! @.**@>
//! l:=input_stack[0].limit_field-1; {last position of first line}
//! for k:=1 to l do print(buffer[k]);
//! print_ln; {now the transcript file contains the first line of input}
//! selector:=old_setting+2; {|log_only| or |term_and_log|}
//! end;
//!
//! @ Sometimes |open_log_file| is called at awkward moments when \MF\ is
//! unable to print error messages or even to |show_context|.
//! The |prompt_file_name| routine can result in a |fatal_error|, but the |error|
//! routine will not be invoked because |log_opened| will be false.
//!
//! The normal idea of |batch_mode| is that nothing at all should be written
//! on the terminal. However, in the unusual case that
//! no log file could be opened, we make an exception and allow
//! an explanatory message to be seen.
//!
//! Incidentally, the program always refers to the log file as a `\.{transcript
//! file}', because some systems cannot use the extension `\.{.log}' for
//! this file.
//!
//! @<Try to get a different log file name@>=
//! begin selector:=term_only;
//! prompt_file_name("transcript file name",".log");
//! end
//!
//! @ @<Print the banner...@>=
//! begin wlog(banner);
//! slow_print(base_ident); print("  ");
//! print_int(sys_day); print_char(" ");
//! months:='JANFEBMARAPRMAYJUNJULAUGSEPOCTNOVDEC';
//! for k:=3*sys_month-2 to 3*sys_month do wlog(months[k]);
//! print_char(" "); print_int(sys_year); print_char(" ");
//! print_dd(sys_time div 60); print_char(":"); print_dd(sys_time mod 60);
//! end
//!
//! @ Here's an example of how these file-name-parsing routines work in practice.
//! We shall use the macro |set_output_file_name| when it is time to
//! crank up the output file.
//!
//! @d set_output_file_name==
//!   begin if job_name=0 then open_log_file;
//!   pack_job_name(gf_ext);
//!   while not b_open_out(gf_file) do
//!     prompt_file_name("file name for output",gf_ext);
//!   output_file_name:=b_make_name_string(gf_file);
//!   end
//!
//! @<Glob...@>=
//! @!gf_file: byte_file; {the generic font output goes here}
//! @!output_file_name: str_number; {full name of the output file}
//!
//! @ @<Initialize the output...@>=output_file_name:=0;
//!
//! @ Let's turn now to the procedure that is used to initiate file reading
//! when an `\.{input}' command is being processed.
//! Beware: For historic reasons, this code foolishly conserves a tiny bit
//! of string pool space; but that can confuse the interactive `\.E' option.
//! @^system dependencies@>
//!
//! @p procedure start_input; {\MF\ will \.{input} something}
//! label done;
//! begin @<Put the desired file name in |(cur_name,cur_ext,cur_area)|@>;
//! if cur_ext="" then cur_ext:=".mf";
//! pack_cur_name;
//! loop@+  begin begin_file_reading; {set up |cur_file| and new level of input}
//!   if a_open_in(cur_file) then goto done;
//!   if cur_area="" then
//!     begin pack_file_name(cur_name,MF_area,cur_ext);
//!     if a_open_in(cur_file) then goto done;
//!     end;
//!   end_file_reading; {remove the level that didn't work}
//!   prompt_file_name("input file name",".mf");
//!   end;
//! done: name:=a_make_name_string(cur_file); str_ref[cur_name]:=max_str_ref;
//! if job_name=0 then
//!   begin job_name:=cur_name; open_log_file;
//!   end; {|open_log_file| doesn't |show_context|, so |limit|
//!     and |loc| needn't be set to meaningful values yet}
//! if term_offset+length(name)>max_print_line-2 then print_ln
//! else if (term_offset>0)or(file_offset>0) then print_char(" ");
//! print_char("("); incr(open_parens); slow_print(name); update_terminal;
//! if name=str_ptr-1 then {conserve string pool space (but see note above)}
//!   begin flush_string(name); name:=cur_name;
//!   end;
//! @<Read the first line of the new file@>;
//! end;
//!
//! @ Here we have to remember to tell the |input_ln| routine not to
//! start with a |get|. If the file is empty, it is considered to
//! contain a single blank line.
//! @^system dependencies@>
//!
//! @<Read the first line...@>=
//! begin line:=1;
//! if input_ln(cur_file,false) then do_nothing;
//! firm_up_the_line;
//! buffer[limit]:="%"; first:=limit+1; loc:=start;
//! end
//!
//! @ @<Put the desired file name in |(cur_name,cur_ext,cur_area)|@>=
//! while token_state and(loc=null) do end_token_list;
//! if token_state then
//!   begin print_err("File names can't appear within macros");
//! @.File names can't...@>
//!   help3("Sorry...I've converted what follows to tokens,")@/
//!     ("possibly garbaging the name you gave.")@/
//!     ("Please delete the tokens and insert the name again.");@/
//!   error;
//!   end;
//! if file_state then scan_file_name
//! else  begin cur_name:=""; cur_ext:=""; cur_area:="";
//!   end
//!
//! @* \[39] Introduction to the parsing routines.
//! We come now to the central nervous system that sparks many of \MF's activities.
//! By evaluating expressions, from their primary constituents to ever larger
//! subexpressions, \MF\ builds the structures that ultimately define fonts of type.
//!
//! Four mutually recursive subroutines are involved in this process: We call them
//! $$\hbox{|scan_primary|, |scan_secondary|, |scan_tertiary|,
//! and |scan_expression|.}$$
//! @^recursion@>
//! Each of them is parameterless and begins with the first token to be scanned
//! already represented in |cur_cmd|, |cur_mod|, and |cur_sym|. After execution,
//! the value of the primary or secondary or tertiary or expression that was
//! found will appear in the global variables |cur_type| and |cur_exp|. The
//! token following the expression will be represented in |cur_cmd|, |cur_mod|,
//! and |cur_sym|.
//!
//! Technically speaking, the parsing algorithms are ``LL(1),'' more or less;
//! backup mechanisms have been added in order to provide reasonable error
//! recovery.
//!
//! @<Glob...@>=
//! @!cur_type:small_number; {the type of the expression just found}
//! @!cur_exp:integer; {the value of the expression just found}
//!
//! @ @<Set init...@>=
//! cur_exp:=0;
//!
//! @ Many different kinds of expressions are possible, so it is wise to have
//! precise descriptions of what |cur_type| and |cur_exp| mean in all cases:
//!
//! \smallskip\hang
//! |cur_type=vacuous| means that this expression didn't turn out to have a
//! value at all, because it arose from a \&{begingroup}$\,\ldots\,$\&{endgroup}
//! construction in which there was no expression before the \&{endgroup}.
//! In this case |cur_exp| has some irrelevant value.
//!
//! \smallskip\hang
//! |cur_type=boolean_type| means that |cur_exp| is either |true_code|
//! or |false_code|.
//!
//! \smallskip\hang
//! |cur_type=unknown_boolean| means that |cur_exp| points to a capsule
//! node that is in
//! a ring of equivalent booleans whose value has not yet been defined.
//!
//! \smallskip\hang
//! |cur_type=string_type| means that |cur_exp| is a string number (i.e., an
//! integer in the range |0<=cur_exp<str_ptr|). That string's reference count
//! includes this particular reference.
//!
//! \smallskip\hang
//! |cur_type=unknown_string| means that |cur_exp| points to a capsule
//! node that is in
//! a ring of equivalent strings whose value has not yet been defined.
//!
//! \smallskip\hang
//! |cur_type=pen_type| means that |cur_exp| points to a pen header node. This
//! node contains a reference count, which takes account of this particular
//! reference.
//!
//! \smallskip\hang
//! |cur_type=unknown_pen| means that |cur_exp| points to a capsule
//! node that is in
//! a ring of equivalent pens whose value has not yet been defined.
//!
//! \smallskip\hang
//! |cur_type=future_pen| means that |cur_exp| points to a knot list that
//! should eventually be made into a pen. Nobody else points to this particular
//! knot list. The |future_pen| option occurs only as an output of |scan_primary|
//! and |scan_secondary|, not as an output of |scan_tertiary| or |scan_expression|.
//!
//! \smallskip\hang
//! |cur_type=path_type| means that |cur_exp| points to the first node of
//! a path; nobody else points to this particular path. The control points of
//! the path will have been chosen.
//!
//! \smallskip\hang
//! |cur_type=unknown_path| means that |cur_exp| points to a capsule
//! node that is in
//! a ring of equivalent paths whose value has not yet been defined.
//!
//! \smallskip\hang
//! |cur_type=picture_type| means that |cur_exp| points to an edges header node.
//! Nobody else points to this particular set of edges.
//!
//! \smallskip\hang
//! |cur_type=unknown_picture| means that |cur_exp| points to a capsule
//! node that is in
//! a ring of equivalent pictures whose value has not yet been defined.
//!
//! \smallskip\hang
//! |cur_type=transform_type| means that |cur_exp| points to a |transform_type|
//! capsule node. The |value| part of this capsule
//! points to a transform node that contains six numeric values,
//! each of which is |independent|, |dependent|, |proto_dependent|, or |known|.
//!
//! \smallskip\hang
//! |cur_type=pair_type| means that |cur_exp| points to a capsule
//! node whose type is |pair_type|. The |value| part of this capsule
//! points to a pair node that contains two numeric values,
//! each of which is |independent|, |dependent|, |proto_dependent|, or |known|.
//!
//! \smallskip\hang
//! |cur_type=known| means that |cur_exp| is a |scaled| value.
//!
//! \smallskip\hang
//! |cur_type=dependent| means that |cur_exp| points to a capsule node whose type
//! is |dependent|. The |dep_list| field in this capsule points to the associated
//! dependency list.
//!
//! \smallskip\hang
//! |cur_type=proto_dependent| means that |cur_exp| points to a |proto_dependent|
//! capsule node. The |dep_list| field in this capsule
//! points to the associated dependency list.
//!
//! \smallskip\hang
//! |cur_type=independent| means that |cur_exp| points to a capsule node
//! whose type is |independent|. This somewhat unusual case can arise, for
//! example, in the expression
//! `$x+\&{begingroup}\penalty0\,\&{string}\,x; 0\,\&{endgroup}$'.
//!
//! \smallskip\hang
//! |cur_type=token_list| means that |cur_exp| points to a linked list of
//! tokens.
//!
//! \smallskip\noindent
//! The possible settings of |cur_type| have been listed here in increasing
//! numerical order. Notice that |cur_type| will never be |numeric_type| or
//! |suffixed_macro| or |unsuffixed_macro|, although variables of those types
//! are allowed.  Conversely, \MF\ has no variables of type |vacuous| or
//! |token_list|.
//!
//! @ Capsules are two-word nodes that have a similar meaning
//! to |cur_type| and |cur_exp|. Such nodes have |name_type=capsule|,
//! and their |type| field is one of the possibilities for |cur_type| listed above.
//! Also |link<=void| in capsules that aren't part of a token list.
//!
//! The |value| field of a capsule is, in most cases, the value that
//! corresponds to its |type|, as |cur_exp| corresponds to |cur_type|.
//! However, when |cur_exp| would point to a capsule,
//! no extra layer of indirection is present; the |value|
//! field is what would have been called |value(cur_exp)| if it had not been
//! encapsulated.  Furthermore, if the type is |dependent| or
//! |proto_dependent|, the |value| field of a capsule is replaced by
//! |dep_list| and |prev_dep| fields, since dependency lists in capsules are
//! always part of the general |dep_list| structure.
//!
//! The |get_x_next| routine is careful not to change the values of |cur_type|
//! and |cur_exp| when it gets an expanded token. However, |get_x_next| might
//! call a macro, which might parse an expression, which might execute lots of
//! commands in a group; hence it's possible that |cur_type| might change
//! from, say, |unknown_boolean| to |boolean_type|, or from |dependent| to
//! |known| or |independent|, during the time |get_x_next| is called. The
//! programs below are careful to stash sensitive intermediate results in
//! capsules, so that \MF's generality doesn't cause trouble.
//!
//! Here's a procedure that illustrates these conventions. It takes
//! the contents of $(|cur_type|\kern-.3pt,|cur_exp|\kern-.3pt)$
//! and stashes them away in a
//! capsule. It is not used when |cur_type=token_list|.
//! After the operation, |cur_type=vacuous|; hence there is no need to
//! copy path lists or to update reference counts, etc.
//!
//! The special link |void| is put on the capsule returned by
//! |stash_cur_exp|, because this procedure is used to store macro parameters
//! that must be easily distinguishable from token lists.
//!
//! @<Declare the stashing/unstashing routines@>=
//! function stash_cur_exp:pointer;
//! var @!p:pointer; {the capsule that will be returned}
//! begin case cur_type of
//! unknown_types,transform_type,pair_type,dependent,proto_dependent,
//!   independent:p:=cur_exp;
//! othercases begin  p:=get_node(value_node_size); name_type(p):=capsule;
//!   type(p):=cur_type; value(p):=cur_exp;
//!   end
//! endcases;@/
//! cur_type:=vacuous; link(p):=void; stash_cur_exp:=p;
//! end;
//!
//! @ The inverse of |stash_cur_exp| is the following procedure, which
//! deletes an unnecessary capsule and puts its contents into |cur_type|
//! and |cur_exp|.
//!
//! The program steps of \MF\ can be divided into two categories: those in
//! which |cur_type| and |cur_exp| are ``alive'' and those in which they are
//! ``dead,'' in the sense that |cur_type| and |cur_exp| contain relevant
//! information or not. It's important not to ignore them when they're alive,
//! and it's important not to pay attention to them when they're dead.
//!
//! There's also an intermediate category: If |cur_type=vacuous|, then
//! |cur_exp| is irrelevant, hence we can proceed without caring if |cur_type|
//! and |cur_exp| are alive or dead. In such cases we say that |cur_type|
//! and |cur_exp| are {\sl dormant}. It is permissible to call |get_x_next|
//! only when they are alive or dormant.
//!
//! The \\{stash} procedure above assumes that |cur_type| and |cur_exp|
//! are alive or dormant. The \\{unstash} procedure assumes that they are
//! dead or dormant; it resuscitates them.
//!
//! @<Declare the stashing/unstashing...@>=
//! procedure unstash_cur_exp(@!p:pointer);
//! begin cur_type:=type(p);
//! case cur_type of
//! unknown_types,transform_type,pair_type,dependent,proto_dependent,
//!   independent: cur_exp:=p;
//! othercases begin cur_exp:=value(p);
//!   free_node(p,value_node_size);
//!   end
//! endcases;@/
//! end;
//!
//! @ The following procedure prints the values of expressions in an
//! abbreviated format. If its first parameter |p| is null, the value of
//! |(cur_type,cur_exp)| is displayed; otherwise |p| should be a capsule
//! containing the desired value. The second parameter controls the amount of
//! output. If it is~0, dependency lists will be abbreviated to
//! `\.{linearform}' unless they consist of a single term.  If it is greater
//! than~1, complicated structures (pens, pictures, and paths) will be displayed
//! in full.
//! @.linearform@>
//!
//! @<Declare subroutines for printing expressions@>=
//! @t\4@>@<Declare the procedure called |print_dp|@>@;
//! @t\4@>@<Declare the stashing/unstashing routines@>@;
//! procedure print_exp(@!p:pointer;@!verbosity:small_number);
//! var @!restore_cur_exp:boolean; {should |cur_exp| be restored?}
//! @!t:small_number; {the type of the expression}
//! @!v:integer; {the value of the expression}
//! @!q:pointer; {a big node being displayed}
//! begin if p<>null then restore_cur_exp:=false
//! else  begin p:=stash_cur_exp; restore_cur_exp:=true;
//!   end;
//! t:=type(p);
//! if t<dependent then v:=value(p)@+else if t<independent then v:=dep_list(p);
//! @<Print an abbreviated value of |v| with format depending on |t|@>;
//! if restore_cur_exp then unstash_cur_exp(p);
//! end;
//!
//! @ @<Print an abbreviated value of |v| with format depending on |t|@>=
//! case t of
//! vacuous:print("vacuous");
//! boolean_type:if v=true_code then print("true")@+else print("false");
//! unknown_types,numeric_type:@<Display a variable
//!   that's been declared but not defined@>;
//! string_type:begin print_char(""""); slow_print(v); print_char("""");
//!   end;
//! pen_type,future_pen,path_type,picture_type:@<Display a complex type@>;
//! transform_type,pair_type:if v=null then print_type(t)
//!   else @<Display a big node@>;
//! known:print_scaled(v);
//! dependent,proto_dependent:print_dp(t,v,verbosity);
//! independent:print_variable_name(p);
//! othercases confusion("exp")
//! @:this can't happen exp}{\quad exp@>
//! endcases
//!
//! @ @<Display a big node@>=
//! begin print_char("("); q:=v+big_node_size[t];
//! repeat if type(v)=known then print_scaled(value(v))
//! else if type(v)=independent then print_variable_name(v)
//! else print_dp(type(v),dep_list(v),verbosity);
//! v:=v+2;
//! if v<>q then print_char(",");
//! until v=q;
//! print_char(")");
//! end
//!
//! @ Values of type \&{picture}, \&{path}, and \&{pen} are displayed verbosely
//! in the log file only, unless the user has given a positive value to
//! \\{tracingonline}.
//!
//! @<Display a complex type@>=
//! if verbosity<=1 then print_type(t)
//! else  begin if selector=term_and_log then
//!    if internal[tracing_online]<=0 then
//!     begin selector:=term_only;
//!     print_type(t); print(" (see the transcript file)");
//!     selector:=term_and_log;
//!     end;
//!   case t of
//!   pen_type:print_pen(v,"",false);
//!   future_pen:print_path(v," (future pen)",false);
//!   path_type:print_path(v,"",false);
//!   picture_type:begin cur_edges:=v; print_edges("",false,0,0);
//!     end;
//!   end; {there are no other cases}
//!   end
//!
//! @ @<Declare the procedure called |print_dp|@>=
//! procedure print_dp(@!t:small_number;@!p:pointer;@!verbosity:small_number);
//! var @!q:pointer; {the node following |p|}
//! begin q:=link(p);
//! if (info(q)=null) or (verbosity>0) then print_dependency(p,t)
//! else print("linearform");
//! @.linearform@>
//! end;
//!
//! @ The displayed name of a variable in a ring will not be a capsule unless
//! the ring consists entirely of capsules.
//!
//! @<Display a variable that's been declared but not defined@>=
//! begin print_type(t);
//! if v<>null then
//!   begin print_char(" ");
//!   while (name_type(v)=capsule) and (v<>p) do v:=value(v);
//!   print_variable_name(v);
//!   end;
//! end
//!
//! @ When errors are detected during parsing, it is often helpful to
//! display an expression just above the error message, using |exp_err|
//! or |disp_err| instead of |print_err|.
//!
//! @d exp_err(#)==disp_err(null,#) {displays the current expression}
//!
//! @<Declare subroutines for printing expressions@>=
//! procedure disp_err(@!p:pointer;@!s:str_number);
//! begin if interaction=error_stop_mode then wake_up_terminal;
//! print_nl(">> ");
//! @.>>@>
//! print_exp(p,1); {``medium verbose'' printing of the expression}
//! if s<>"" then
//!   begin print_nl("! "); print(s);
//! @.!\relax@>
//!   end;
//! end;
//!
//! @ If |cur_type| and |cur_exp| contain relevant information that should
//! be recycled, we will use the following procedure, which changes |cur_type|
//! to |known| and stores a given value in |cur_exp|. We can think of |cur_type|
//! and |cur_exp| as either alive or dormant after this has been done,
//! because |cur_exp| will not contain a pointer value.
//!
//! @<Declare the procedure called |flush_cur_exp|@>=
//! procedure flush_cur_exp(@!v:scaled);
//! begin case cur_type of
//! unknown_types,transform_type,pair_type,@|dependent,proto_dependent,independent:
//!   begin recycle_value(cur_exp); free_node(cur_exp,value_node_size);
//!   end;
//! pen_type: delete_pen_ref(cur_exp);
//! string_type:delete_str_ref(cur_exp);
//! future_pen,path_type: toss_knot_list(cur_exp);
//! picture_type:toss_edges(cur_exp);
//! othercases do_nothing
//! endcases;@/
//! cur_type:=known; cur_exp:=v;
//! end;
//!
//! @ There's a much more general procedure that is capable of releasing
//! the storage associated with any two-word value packet.
//!
//! @<Declare the recycling subroutines@>=
//! procedure recycle_value(@!p:pointer);
//! label done;
//! var @!t:small_number; {a type code}
//! @!v:integer; {a value}
//! @!vv:integer; {another value}
//! @!q,@!r,@!s,@!pp:pointer; {link manipulation registers}
//! begin t:=type(p);
//! if t<dependent then v:=value(p);
//! case t of
//! undefined,vacuous,boolean_type,known,numeric_type:do_nothing;
//! unknown_types:ring_delete(p);
//! string_type:delete_str_ref(v);
//! pen_type:delete_pen_ref(v);
//! path_type,future_pen:toss_knot_list(v);
//! picture_type:toss_edges(v);
//! pair_type,transform_type:@<Recycle a big node@>;
//! dependent,proto_dependent:@<Recycle a dependency list@>;
//! independent:@<Recycle an independent variable@>;
//! token_list,structured:confusion("recycle");
//! @:this can't happen recycle}{\quad recycle@>
//! unsuffixed_macro,suffixed_macro:delete_mac_ref(value(p));
//! end; {there are no other cases}
//! type(p):=undefined;
//! end;
//!
//! @ @<Recycle a big node@>=
//! if v<>null then
//!   begin q:=v+big_node_size[t];
//!   repeat q:=q-2; recycle_value(q);
//!   until q=v;
//!   free_node(v,big_node_size[t]);
//!   end
//!
//! @ @<Recycle a dependency list@>=
//! begin q:=dep_list(p);
//! while info(q)<>null do q:=link(q);
//! link(prev_dep(p)):=link(q);
//! prev_dep(link(q)):=prev_dep(p);
//! link(q):=null; flush_node_list(dep_list(p));
//! end
//!
//! @ When an independent variable disappears, it simply fades away, unless
//! something depends on it. In the latter case, a dependent variable whose
//! coefficient of dependence is maximal will take its place.
//! The relevant algorithm is due to Ignacio~A. Zabala, who implemented it
//! as part of his Ph.D. thesis (Stanford University, December 1982).
//! @^Zabala Salelles, Ignacio Andr\'es@>
//!
//! For example, suppose that variable $x$ is being recycled, and that the
//! only variables depending on~$x$ are $y=2x+a$ and $z=x+b$. In this case
//! we want to make $y$ independent and $z=.5y-.5a+b$; no other variables
//! will depend on~$y$. If $\\{tracingequations}>0$ in this situation,
//! we will print `\.{\#\#\# -2x=-y+a}'.
//!
//! There's a slight complication, however: An independent variable $x$
//! can occur both in dependency lists and in proto-dependency lists.
//! This makes it necessary to be careful when deciding which coefficient
//! is maximal.
//!
//! Furthermore, this complication is not so slight when
//! a proto-dependent variable is chosen to become independent. For example,
//! suppose that $y=2x+100a$ is proto-dependent while $z=x+b$ is dependent;
//! then we must change $z=.5y-50a+b$ to a proto-dependency, because of the
//! large coefficient `50'.
//!
//! In order to deal with these complications without wasting too much time,
//! we shall link together the occurrences of~$x$ among all the linear
//! dependencies, maintaining separate lists for the dependent and
//! proto-dependent cases.
//!
//! @<Recycle an independent variable@>=
//! begin max_c[dependent]:=0; max_c[proto_dependent]:=0;@/
//! max_link[dependent]:=null; max_link[proto_dependent]:=null;@/
//! q:=link(dep_head);
//! while q<>dep_head do
//!   begin s:=value_loc(q); {now |link(s)=dep_list(q)|}
//!   loop@+  begin r:=link(s);
//!     if info(r)=null then goto done;
//!     if info(r)<>p then s:=r
//!     else  begin t:=type(q); link(s):=link(r); info(r):=q;
//!       if abs(value(r))>max_c[t] then
//!         @<Record a new maximum coefficient of type |t|@>
//!       else  begin link(r):=max_link[t]; max_link[t]:=r;
//!         end;
//!       end;
//!     end;
//! done:  q:=link(r);
//!   end;
//! if (max_c[dependent]>0)or(max_c[proto_dependent]>0) then
//!   @<Choose a dependent variable to take the place of the disappearing
//!     independent variable, and change all remaining dependencies
//!     accordingly@>;
//! end
//!
//! @ The code for independency removal makes use of three two-word arrays.
//!
//! @<Glob...@>=
//! @!max_c:array[dependent..proto_dependent] of integer;
//!   {max coefficient magnitude}
//! @!max_ptr:array[dependent..proto_dependent] of pointer;
//!   {where |p| occurs with |max_c|}
//! @!max_link:array[dependent..proto_dependent] of pointer;
//!   {other occurrences of |p|}
//!
//! @ @<Record a new maximum coefficient...@>=
//! begin if max_c[t]>0 then
//!   begin link(max_ptr[t]):=max_link[t]; max_link[t]:=max_ptr[t];
//!   end;
//! max_c[t]:=abs(value(r)); max_ptr[t]:=r;
//! end
//!
//! @ @<Choose a dependent...@>=
//! begin if (max_c[dependent] div @'10000 >=
//!           max_c[proto_dependent]) then
//!   t:=dependent
//! else t:=proto_dependent;
//! @<Determine the dependency list |s| to substitute for the independent
//!   variable~|p|@>;
//! t:=dependent+proto_dependent-t; {complement |t|}
//! if max_c[t]>0 then {we need to pick up an unchosen dependency}
//!   begin link(max_ptr[t]):=max_link[t]; max_link[t]:=max_ptr[t];
//!   end;
//! if t<>dependent then @<Substitute new dependencies in place of |p|@>
//! else @<Substitute new proto-dependencies in place of |p|@>;
//! flush_node_list(s);
//! if fix_needed then fix_dependencies;
//! check_arith;
//! end
//!
//! @ Let |s=max_ptr[t]|. At this point we have $|value|(s)=\pm|max_c|[t]$,
//! and |info(s)| points to the dependent variable~|pp| of type~|t| from
//! whose dependency list we have removed node~|s|. We must reinsert
//! node~|s| into the dependency list, with coefficient $-1.0$, and with
//! |pp| as the new independent variable. Since |pp| will have a larger serial
//! number than any other variable, we can put node |s| at the head of the
//! list.
//!
//! @<Determine the dep...@>=
//! s:=max_ptr[t]; pp:=info(s); v:=value(s);
//! if t=dependent then value(s):=-fraction_one@+else value(s):=-unity;
//! r:=dep_list(pp); link(s):=r;
//! while info(r)<>null do r:=link(r);
//! q:=link(r); link(r):=null;
//! prev_dep(q):=prev_dep(pp); link(prev_dep(pp)):=q;
//! new_indep(pp);
//! if cur_exp=pp then if cur_type=t then cur_type:=independent;
//! if internal[tracing_equations]>0 then @<Show the transformed dependency@>
//!
//! @ Now $(-v)$ times the formerly independent variable~|p| is being replaced
//! by the dependency list~|s|.
//!
//! @<Show the transformed...@>=
//! if interesting(p) then
//!   begin begin_diagnostic; print_nl("### ");
//! @:]]]\#\#\#_}{\.{\#\#\#}@>
//!   if v>0 then print_char("-");
//!   if t=dependent then vv:=round_fraction(max_c[dependent])
//!   else vv:=max_c[proto_dependent];
//!   if vv<>unity then print_scaled(vv);
//!   print_variable_name(p);
//!   while value(p) mod s_scale>0 do
//!     begin print("*4"); value(p):=value(p)-2;
//!     end;
//!   if t=dependent then print_char("=")@+else print(" = ");
//!   print_dependency(s,t);
//!   end_diagnostic(false);
//!   end
//!
//! @ Finally, there are dependent and proto-dependent variables whose
//! dependency lists must be brought up to date.
//!
//! @<Substitute new dependencies...@>=
//! for t:=dependent to proto_dependent do
//!   begin r:=max_link[t];
//!   while r<>null do
//!     begin q:=info(r);
//!     dep_list(q):=p_plus_fq(dep_list(q),@|
//!      make_fraction(value(r),-v),s,t,dependent);
//!     if dep_list(q)=dep_final then make_known(q,dep_final);
//!     q:=r; r:=link(r); free_node(q,dep_node_size);
//!     end;
//!   end
//!
//! @ @<Substitute new proto...@>=
//! for t:=dependent to proto_dependent do
//!   begin r:=max_link[t];
//!   while r<>null do
//!     begin q:=info(r);
//!     if t=dependent then {for safety's sake, we change |q| to |proto_dependent|}
//!       begin if cur_exp=q then if cur_type=dependent then
//!         cur_type:=proto_dependent;
//!       dep_list(q):=p_over_v(dep_list(q),unity,dependent,proto_dependent);
//!       type(q):=proto_dependent; value(r):=round_fraction(value(r));
//!       end;
//!     dep_list(q):=p_plus_fq(dep_list(q),@|
//!      make_scaled(value(r),-v),s,proto_dependent,proto_dependent);
//!     if dep_list(q)=dep_final then make_known(q,dep_final);
//!     q:=r; r:=link(r); free_node(q,dep_node_size);
//!     end;
//!   end
//!
//! @ Here are some routines that provide handy combinations of actions
//! that are often needed during error recovery. For example,
//! `|flush_error|' flushes the current expression, replaces it by
//! a given value, and calls |error|.
//!
//! Errors often are detected after an extra token has already been scanned.
//! The `\\{put\_get}' routines put that token back before calling |error|;
//! then they get it back again. (Or perhaps they get another token, if
//! the user has changed things.)
//!
//! @<Declare the procedure called |flush_cur_exp|@>=
//! procedure flush_error(@!v:scaled);@+begin error; flush_cur_exp(v);@+end;
//! @#
//! procedure@?back_error; forward;@t\2@>@/
//! procedure@?get_x_next; forward;@t\2@>@/
//! @#
//! procedure put_get_error;@+begin back_error; get_x_next;@+end;
//! @#
//! procedure put_get_flush_error(@!v:scaled);@+begin put_get_error;
//!  flush_cur_exp(v);@+end;
//!
//! @ A global variable called |var_flag| is set to a special command code
//! just before \MF\ calls |scan_expression|, if the expression should be
//! treated as a variable when this command code immediately follows. For
//! example, |var_flag| is set to |assignment| at the beginning of a
//! statement, because we want to know the {\sl location\/} of a variable at
//! the left of `\.{:=}', not the {\sl value\/} of that variable.
//!
//! The |scan_expression| subroutine calls |scan_tertiary|,
//! which calls |scan_secondary|, which calls |scan_primary|, which sets
//! |var_flag:=0|. In this way each of the scanning routines ``knows''
//! when it has been called with a special |var_flag|, but |var_flag| is
//! usually zero.
//!
//! A variable preceding a command that equals |var_flag| is converted to a
//! token list rather than a value. Furthermore, an `\.{=}' sign following an
//! expression with |var_flag=assignment| is not considered to be a relation
//! that produces boolean expressions.
//!
//!
//! @<Glob...@>=
//! @!var_flag:0..max_command_code; {command that wants a variable}
//!
//! @ @<Set init...@>=
//! var_flag:=0;
//!
//! @* \[40] Parsing primary expressions.
//! The first parsing routine, |scan_primary|, is also the most complicated one,
//! since it involves so many different cases. But each case---with one
//! exception---is fairly simple by itself.
//!
//! When |scan_primary| begins, the first token of the primary to be scanned
//! should already appear in |cur_cmd|, |cur_mod|, and |cur_sym|. The values
//! of |cur_type| and |cur_exp| should be either dead or dormant, as explained
//! earlier. If |cur_cmd| is not between |min_primary_command| and
//! |max_primary_command|, inclusive, a syntax error will be signalled.
//!
//! @<Declare the basic parsing subroutines@>=
//! procedure scan_primary;
//! label restart, done, done1, done2;
//! var @!p,@!q,@!r:pointer; {for list manipulation}
//! @!c:quarterword; {a primitive operation code}
//! @!my_var_flag:0..max_command_code; {initial value of |var_flag|}
//! @!l_delim,@!r_delim:pointer; {hash addresses of a delimiter pair}
//! @<Other local variables for |scan_primary|@>@;
//! begin my_var_flag:=var_flag; var_flag:=0;
//! restart:check_arith;
//! @<Supply diagnostic information, if requested@>;
//! case cur_cmd of
//! left_delimiter:@<Scan a delimited primary@>;
//! begin_group:@<Scan a grouped primary@>;
//! string_token:@<Scan a string constant@>;
//! numeric_token:@<Scan a primary that starts with a numeric token@>;
//! nullary:@<Scan a nullary operation@>;
//! unary,type_name,cycle,plus_or_minus:@<Scan a unary operation@>;
//! primary_binary:@<Scan a binary operation with `\&{of}' between its operands@>;
//! str_op:@<Convert a suffix to a string@>;
//! internal_quantity:@<Scan an internal numeric quantity@>;
//! capsule_token:make_exp_copy(cur_mod);
//! tag_token:@<Scan a variable primary;
//!   |goto restart| if it turns out to be a macro@>;
//! othercases begin bad_exp("A primary"); goto restart;
//! @.A primary expression...@>
//!   end
//! endcases;@/
//! get_x_next; {the routines |goto done| if they don't want this}
//! done: if cur_cmd=left_bracket then
//!   if cur_type>=known then @<Scan a mediation construction@>;
//! end;
//!
//! @ Errors at the beginning of expressions are flagged by |bad_exp|.
//!
//! @p procedure bad_exp(@!s:str_number);
//! var save_flag:0..max_command_code;
//! begin print_err(s); print(" expression can't begin with `");
//! print_cmd_mod(cur_cmd,cur_mod); print_char("'");
//! help4("I'm afraid I need some sort of value in order to continue,")@/
//!   ("so I've tentatively inserted `0'. You may want to")@/
//!   ("delete this zero and insert something else;")@/
//!   ("see Chapter 27 of The METAFONTbook for an example.");
//! @:METAFONTbook}{\sl The {\logos METAFONT\/}book@>
//! back_input; cur_sym:=0; cur_cmd:=numeric_token; cur_mod:=0; ins_error;@/
//! save_flag:=var_flag; var_flag:=0; get_x_next;
//! var_flag:=save_flag;
//! end;
//!
//! @ @<Supply diagnostic information, if requested@>=
//! debug if panicking then check_mem(false);@+gubed@;@/
//! if interrupt<>0 then if OK_to_interrupt then
//!   begin back_input; check_interrupt; get_x_next;
//!   end
//!
//! @ @<Scan a delimited primary@>=
//! begin l_delim:=cur_sym; r_delim:=cur_mod; get_x_next; scan_expression;
//! if (cur_cmd=comma) and (cur_type>=known) then
//!   @<Scan the second of a pair of numerics@>
//! else check_delimiter(l_delim,r_delim);
//! end
//!
//! @ The |stash_in| subroutine puts the current (numeric) expression into a field
//! within a ``big node.''
//!
//! @p procedure stash_in(@!p:pointer);
//! var @!q:pointer; {temporary register}
//! begin type(p):=cur_type;
//! if cur_type=known then value(p):=cur_exp
//! else  begin if cur_type=independent then
//!     @<Stash an independent |cur_exp| into a big node@>
//!   else  begin mem[value_loc(p)]:=mem[value_loc(cur_exp)];
//!      {|dep_list(p):=dep_list(cur_exp)| and |prev_dep(p):=prev_dep(cur_exp)|}
//!     link(prev_dep(p)):=p;
//!     end;
//!   free_node(cur_exp,value_node_size);
//!   end;
//! cur_type:=vacuous;
//! end;
//!
//! @ In rare cases the current expression can become |independent|. There
//! may be many dependency lists pointing to such an independent capsule,
//! so we can't simply move it into place within a big node. Instead,
//! we copy it, then recycle it.
//!
//! @ @<Stash an independent |cur_exp|...@>=
//! begin q:=single_dependency(cur_exp);
//! if q=dep_final then
//!   begin type(p):=known; value(p):=0; free_node(q,dep_node_size);
//!   end
//! else  begin type(p):=dependent; new_dep(p,q);
//!   end;
//! recycle_value(cur_exp);
//! end
//!
//! @ @<Scan the second of a pair of numerics@>=
//! begin p:=get_node(value_node_size); type(p):=pair_type; name_type(p):=capsule;
//! init_big_node(p); q:=value(p); stash_in(x_part_loc(q));@/
//! get_x_next; scan_expression;
//! if cur_type<known then
//!   begin exp_err("Nonnumeric ypart has been replaced by 0");
//! @.Nonnumeric...replaced by 0@>
//!   help4("I thought you were giving me a pair `(x,y)'; but")@/
//!     ("after finding a nice xpart `x' I found a ypart `y'")@/
//!     ("that isn't of numeric type. So I've changed y to zero.")@/
//!     ("(The y that I didn't like appears above the error message.)");
//!   put_get_flush_error(0);
//!   end;
//! stash_in(y_part_loc(q));
//! check_delimiter(l_delim,r_delim);
//! cur_type:=pair_type; cur_exp:=p;
//! end
//!
//! @ The local variable |group_line| keeps track of the line
//! where a \&{begingroup} command occurred; this will be useful
//! in an error message if the group doesn't actually end.
//!
//! @<Other local variables for |scan_primary|@>=
//! @!group_line:integer; {where a group began}
//!
//! @ @<Scan a grouped primary@>=
//! begin group_line:=line;
//! if internal[tracing_commands]>0 then show_cur_cmd_mod;
//! save_boundary_item(p);
//! repeat do_statement; {ends with |cur_cmd>=semicolon|}
//! until cur_cmd<>semicolon;
//! if cur_cmd<>end_group then
//!   begin print_err("A group begun on line ");
//! @.A group...never ended@>
//!   print_int(group_line);
//!   print(" never ended");
//!   help2("I saw a `begingroup' back there that hasn't been matched")@/
//!     ("by `endgroup'. So I've inserted `endgroup' now.");
//!   back_error; cur_cmd:=end_group;
//!   end;
//! unsave; {this might change |cur_type|, if independent variables are recycled}
//! if internal[tracing_commands]>0 then show_cur_cmd_mod;
//! end
//!
//! @ @<Scan a string constant@>=
//! begin cur_type:=string_type; cur_exp:=cur_mod;
//! end
//!
//! @ Later we'll come to procedures that perform actual operations like
//! addition, square root, and so on; our purpose now is to do the parsing.
//! But we might as well mention those future procedures now, so that the
//! suspense won't be too bad:
//!
//! \smallskip
//! |do_nullary(c)| does primitive operations that have no operands (e.g.,
//! `\&{true}' or `\&{pencircle}');
//!
//! \smallskip
//! |do_unary(c)| applies a primitive operation to the current expression;
//!
//! \smallskip
//! |do_binary(p,c)| applies a primitive operation to the capsule~|p|
//! and the current expression.
//!
//! @<Scan a nullary operation@>=do_nullary(cur_mod)
//!
//! @ @<Scan a unary operation@>=
//! begin c:=cur_mod; get_x_next; scan_primary; do_unary(c); goto done;
//! end
//!
//! @ A numeric token might be a primary by itself, or it might be the
//! numerator of a fraction composed solely of numeric tokens, or it might
//! multiply the primary that follows (provided that the primary doesn't begin
//! with a plus sign or a minus sign). The code here uses the facts that
//! |max_primary_command=plus_or_minus| and
//! |max_primary_command-1=numeric_token|. If a fraction is found that is less
//! than unity, we try to retain higher precision when we use it in scalar
//! multiplication.
//!
//! @<Other local variables for |scan_primary|@>=
//! @!num,@!denom:scaled; {for primaries that are fractions, like `1/2'}
//!
//! @ @<Scan a primary that starts with a numeric token@>=
//! begin cur_exp:=cur_mod; cur_type:=known; get_x_next;
//! if cur_cmd<>slash then
//!   begin num:=0; denom:=0;
//!   end
//! else  begin get_x_next;
//!   if cur_cmd<>numeric_token then
//!     begin back_input;
//!     cur_cmd:=slash; cur_mod:=over; cur_sym:=frozen_slash;
//!     goto done;
//!     end;
//!   num:=cur_exp; denom:=cur_mod;
//!   if denom=0 then @<Protest division by zero@>
//!   else cur_exp:=make_scaled(num,denom);
//!   check_arith; get_x_next;
//!   end;
//! if cur_cmd>=min_primary_command then
//!  if cur_cmd<numeric_token then {in particular, |cur_cmd<>plus_or_minus|}
//!   begin p:=stash_cur_exp; scan_primary;
//!   if (abs(num)>=abs(denom))or(cur_type<pair_type) then do_binary(p,times)
//!   else  begin frac_mult(num,denom);
//!     free_node(p,value_node_size);
//!     end;
//!   end;
//! goto done;
//! end
//!
//! @ @<Protest division...@>=
//! begin print_err("Division by zero");
//! @.Division by zero@>
//! help1("I'll pretend that you meant to divide by 1."); error;
//! end
//!
//! @ @<Scan a binary operation with `\&{of}' between its operands@>=
//! begin c:=cur_mod; get_x_next; scan_expression;
//! if cur_cmd<>of_token then
//!   begin missing_err("of"); print(" for "); print_cmd_mod(primary_binary,c);
//! @.Missing `of'@>
//!   help1("I've got the first argument; will look now for the other.");
//!   back_error;
//!   end;
//! p:=stash_cur_exp; get_x_next; scan_primary; do_binary(p,c); goto done;
//! end
//!
//! @ @<Convert a suffix to a string@>=
//! begin get_x_next; scan_suffix; old_setting:=selector; selector:=new_string;
//! show_token_list(cur_exp,null,100000,0); flush_token_list(cur_exp);
//! cur_exp:=make_string; selector:=old_setting; cur_type:=string_type;
//! goto done;
//! end
//!
//! @ If an internal quantity appears all by itself on the left of an
//! assignment, we return a token list of length one, containing the address
//! of the internal quantity plus |hash_end|. (This accords with the conventions
//! of the save stack, as described earlier.)
//!
//! @<Scan an internal...@>=
//! begin q:=cur_mod;
//! if my_var_flag=assignment then
//!   begin get_x_next;
//!   if cur_cmd=assignment then
//!     begin cur_exp:=get_avail;
//!     info(cur_exp):=q+hash_end; cur_type:=token_list; goto done;
//!     end;
//!   back_input;
//!   end;
//! cur_type:=known; cur_exp:=internal[q];
//! end
//!
//! @ The most difficult part of |scan_primary| has been saved for last, since
//! it was necessary to build up some confidence first. We can now face the task
//! of scanning a variable.
//!
//! As we scan a variable, we build a token list containing the relevant
//! names and subscript values, simultaneously following along in the
//! ``collective'' structure to see if we are actually dealing with a macro
//! instead of a value.
//!
//! The local variables |pre_head| and |post_head| will point to the beginning
//! of the prefix and suffix lists; |tail| will point to the end of the list
//! that is currently growing.
//!
//! Another local variable, |tt|, contains partial information about the
//! declared type of the variable-so-far. If |tt>=unsuffixed_macro|, the
//! relation |tt=type(q)| will always hold. If |tt=undefined|, the routine
//! doesn't bother to update its information about type. And if
//! |undefined<tt<unsuffixed_macro|, the precise value of |tt| isn't critical.
//!
//! @ @<Other local variables for |scan_primary|@>=
//! @!pre_head,@!post_head,@!tail:pointer;
//!   {prefix and suffix list variables}
//! @!tt:small_number; {approximation to the type of the variable-so-far}
//! @!t:pointer; {a token}
//! @!macro_ref:pointer; {reference count for a suffixed macro}
//!
//! @ @<Scan a variable primary...@>=
//! begin fast_get_avail(pre_head); tail:=pre_head; post_head:=null; tt:=vacuous;
//! loop@+  begin t:=cur_tok; link(tail):=t;
//!   if tt<>undefined then
//!     begin @<Find the approximate type |tt| and corresponding~|q|@>;
//!     if tt>=unsuffixed_macro then
//!       @<Either begin an unsuffixed macro call or
//!         prepare for a suffixed one@>;
//!     end;
//!   get_x_next; tail:=t;
//!   if cur_cmd=left_bracket then
//!     @<Scan for a subscript; replace |cur_cmd| by |numeric_token| if found@>;
//!   if cur_cmd>max_suffix_token then goto done1;
//!   if cur_cmd<min_suffix_token then goto done1;
//!   end; {now |cur_cmd| is |internal_quantity|, |tag_token|, or |numeric_token|}
//! done1:@<Handle unusual cases that masquerade as variables, and |goto restart|
//!   or |goto done| if appropriate;
//!   otherwise make a copy of the variable and |goto done|@>;
//! end
//!
//! @ @<Either begin an unsuffixed macro call or...@>=
//! begin link(tail):=null;
//! if tt>unsuffixed_macro then {|tt=suffixed_macro|}
//!   begin post_head:=get_avail; tail:=post_head; link(tail):=t;@/
//!   tt:=undefined; macro_ref:=value(q); add_mac_ref(macro_ref);
//!   end
//! else @<Set up unsuffixed macro call and |goto restart|@>;
//! end
//!
//! @ @<Scan for a subscript; replace |cur_cmd| by |numeric_token| if found@>=
//! begin get_x_next; scan_expression;
//! if cur_cmd<>right_bracket then
//!   @<Put the left bracket and the expression back to be rescanned@>
//! else  begin if cur_type<>known then bad_subscript;
//!   cur_cmd:=numeric_token; cur_mod:=cur_exp; cur_sym:=0;
//!   end;
//! end
//!
//! @ The left bracket that we thought was introducing a subscript might have
//! actually been the left bracket in a mediation construction like `\.{x[a,b]}'.
//! So we don't issue an error message at this point; but we do want to back up
//! so as to avoid any embarrassment about our incorrect assumption.
//!
//! @<Put the left bracket and the expression back to be rescanned@>=
//! begin back_input; {that was the token following the current expression}
//! back_expr; cur_cmd:=left_bracket; cur_mod:=0; cur_sym:=frozen_left_bracket;
//! end
//!
//! @ Here's a routine that puts the current expression back to be read again.
//!
//! @p procedure back_expr;
//! var @!p:pointer; {capsule token}
//! begin p:=stash_cur_exp; link(p):=null; back_list(p);
//! end;
//!
//! @ Unknown subscripts lead to the following error message.
//!
//! @p procedure bad_subscript;
//! begin exp_err("Improper subscript has been replaced by zero");
//! @.Improper subscript...@>
//! help3("A bracketed subscript must have a known numeric value;")@/
//!   ("unfortunately, what I found was the value that appears just")@/
//!   ("above this error message. So I'll try a zero subscript.");
//! flush_error(0);
//! end;
//!
//! @ Every time we call |get_x_next|, there's a chance that the variable we've
//! been looking at will disappear. Thus, we cannot safely keep |q| pointing
//! into the variable structure; we need to start searching from the root each time.
//!
//! @<Find the approximate type |tt| and corresponding~|q|@>=
//! @^inner loop@>
//! begin p:=link(pre_head); q:=info(p); tt:=undefined;
//! if eq_type(q) mod outer_tag=tag_token then
//!   begin q:=equiv(q);
//!   if q=null then goto done2;
//!   loop@+  begin p:=link(p);
//!     if p=null then
//!       begin tt:=type(q); goto done2;
//!       end;
//!     if type(q)<>structured then goto done2;
//!     q:=link(attr_head(q)); {the |collective_subscript| attribute}
//!     if p>=hi_mem_min then {it's not a subscript}
//!       begin repeat q:=link(q);
//!       until attr_loc(q)>=info(p);
//!       if attr_loc(q)>info(p) then goto done2;
//!       end;
//!     end;
//!   end;
//! done2:end
//!
//! @ How do things stand now? Well, we have scanned an entire variable name,
//! including possible subscripts and/or attributes; |cur_cmd|, |cur_mod|, and
//! |cur_sym| represent the token that follows. If |post_head=null|, a
//! token list for this variable name starts at |link(pre_head)|, with all
//! subscripts evaluated. But if |post_head<>null|, the variable turned out
//! to be a suffixed macro; |pre_head| is the head of the prefix list, while
//! |post_head| is the head of a token list containing both `\.{\AT!}' and
//! the suffix.
//!
//! Our immediate problem is to see if this variable still exists. (Variable
//! structures can change drastically whenever we call |get_x_next|; users
//! aren't supposed to do this, but the fact that it is possible means that
//! we must be cautious.)
//!
//! The following procedure prints an error message when a variable
//! unexpectedly disappears. Its help message isn't quite right for
//! our present purposes, but we'll be able to fix that up.
//!
//! @p procedure obliterated(@!q:pointer);
//! begin print_err("Variable "); show_token_list(q,null,1000,0);
//! print(" has been obliterated");
//! @.Variable...obliterated@>
//! help5("It seems you did a nasty thing---probably by accident,")@/
//!   ("but nevertheless you nearly hornswoggled me...")@/
//!   ("While I was evaluating the right-hand side of this")@/
//!   ("command, something happened, and the left-hand side")@/
//!   ("is no longer a variable! So I won't change anything.");
//! end;
//!
//! @ If the variable does exist, we also need to check
//! for a few other special cases before deciding that a plain old ordinary
//! variable has, indeed, been scanned.
//!
//! @<Handle unusual cases that masquerade as variables...@>=
//! if post_head<>null then @<Set up suffixed macro call and |goto restart|@>;
//! q:=link(pre_head); free_avail(pre_head);
//! if cur_cmd=my_var_flag then
//!   begin cur_type:=token_list; cur_exp:=q; goto done;
//!   end;
//! p:=find_variable(q);
//! if p<>null then make_exp_copy(p)
//! else  begin obliterated(q);@/
//!   help_line[2]:="While I was evaluating the suffix of this variable,";
//!   help_line[1]:="something was redefined, and it's no longer a variable!";
//!   help_line[0]:="In order to get back on my feet, I've inserted `0' instead.";
//!   put_get_flush_error(0);
//!   end;
//! flush_node_list(q); goto done
//!
//! @ The only complication associated with macro calling is that the prefix
//! and ``at'' parameters must be packaged in an appropriate list of lists.
//!
//! @<Set up unsuffixed macro call and |goto restart|@>=
//! begin p:=get_avail; info(pre_head):=link(pre_head); link(pre_head):=p;
//! info(p):=t; macro_call(value(q),pre_head,null); get_x_next; goto restart;
//! end
//!
//! @ If the ``variable'' that turned out to be a suffixed macro no longer exists,
//! we don't care, because we have reserved a pointer (|macro_ref|) to its
//! token list.
//!
//! @<Set up suffixed macro call and |goto restart|@>=
//! begin back_input; p:=get_avail; q:=link(post_head);
//! info(pre_head):=link(pre_head); link(pre_head):=post_head;
//! info(post_head):=q; link(post_head):=p; info(p):=link(q); link(q):=null;
//! macro_call(macro_ref,pre_head,null); decr(ref_count(macro_ref));
//! get_x_next; goto restart;
//! end
//!
//! @ Our remaining job is simply to make a copy of the value that has been
//! found. Some cases are harder than others, but complexity arises solely
//! because of the multiplicity of possible cases.
//!
//! @<Declare the procedure called |make_exp_copy|@>=
//! @t\4@>@<Declare subroutines needed by |make_exp_copy|@>@;
//! procedure make_exp_copy(@!p:pointer);
//! label restart;
//! var @!q,@!r,@!t:pointer; {registers for list manipulation}
//! begin restart: cur_type:=type(p);
//! case cur_type of
//! vacuous,boolean_type,known:cur_exp:=value(p);
//! unknown_types:cur_exp:=new_ring_entry(p);
//! string_type:begin cur_exp:=value(p); add_str_ref(cur_exp);
//!   end;
//! pen_type:begin cur_exp:=value(p); add_pen_ref(cur_exp);
//!   end;
//! picture_type:cur_exp:=copy_edges(value(p));
//! path_type,future_pen:cur_exp:=copy_path(value(p));
//! transform_type,pair_type:@<Copy the big node |p|@>;
//! dependent,proto_dependent:encapsulate(copy_dep_list(dep_list(p)));
//! numeric_type:begin new_indep(p); goto restart;
//!   end;
//! independent: begin q:=single_dependency(p);
//!   if q=dep_final then
//!     begin cur_type:=known; cur_exp:=0; free_node(q,dep_node_size);
//!     end
//!   else  begin cur_type:=dependent; encapsulate(q);
//!     end;
//!   end;
//! othercases confusion("copy")
//! @:this can't happen copy}{\quad copy@>
//! endcases;
//! end;
//!
//! @ The |encapsulate| subroutine assumes that |dep_final| is the
//! tail of dependency list~|p|.
//!
//! @<Declare subroutines needed by |make_exp_copy|@>=
//! procedure encapsulate(@!p:pointer);
//! begin cur_exp:=get_node(value_node_size); type(cur_exp):=cur_type;
//! name_type(cur_exp):=capsule; new_dep(cur_exp,p);
//! end;
//!
//! @ The most tedious case arises when the user refers to a
//! \&{pair} or \&{transform} variable; we must copy several fields,
//! each of which can be |independent|, |dependent|, |proto_dependent|,
//! or |known|.
//!
//! @<Copy the big node |p|@>=
//! begin if value(p)=null then init_big_node(p);
//! t:=get_node(value_node_size); name_type(t):=capsule; type(t):=cur_type;
//! init_big_node(t);@/
//! q:=value(p)+big_node_size[cur_type]; r:=value(t)+big_node_size[cur_type];
//! repeat q:=q-2; r:=r-2; install(r,q);
//! until q=value(p);
//! cur_exp:=t;
//! end
//!
//! @ The |install| procedure copies a numeric field~|q| into field~|r| of
//! a big node that will be part of a capsule.
//!
//! @<Declare subroutines needed by |make_exp_copy|@>=
//! procedure install(@!r,@!q:pointer);
//! var p:pointer; {temporary register}
//! begin if type(q)=known then
//!   begin value(r):=value(q); type(r):=known;
//!   end
//! else  if type(q)=independent then
//!     begin p:=single_dependency(q);
//!     if p=dep_final then
//!       begin type(r):=known; value(r):=0; free_node(p,dep_node_size);
//!       end
//!     else  begin type(r):=dependent; new_dep(r,p);
//!       end;
//!     end
//!   else  begin type(r):=type(q); new_dep(r,copy_dep_list(dep_list(q)));
//!     end;
//! end;
//!
//! @ Expressions of the form `\.{a[b,c]}' are converted into
//! `\.{b+a*(c-b)}', without checking the types of \.b~or~\.c,
//! provided that \.a is numeric.
//!
//! @<Scan a mediation...@>=
//! begin p:=stash_cur_exp; get_x_next; scan_expression;
//! if cur_cmd<>comma then
//!   begin @<Put the left bracket and the expression back...@>;
//!   unstash_cur_exp(p);
//!   end
//! else  begin q:=stash_cur_exp; get_x_next; scan_expression;
//!   if cur_cmd<>right_bracket then
//!     begin missing_err("]");@/
//! @.Missing `]'@>
//!     help3("I've scanned an expression of the form `a[b,c',")@/
//!       ("so a right bracket should have come next.")@/
//!       ("I shall pretend that one was there.");@/
//!     back_error;
//!     end;
//!   r:=stash_cur_exp; make_exp_copy(q);@/
//!   do_binary(r,minus); do_binary(p,times); do_binary(q,plus); get_x_next;
//!   end;
//! end
//!
//! @ Here is a comparatively simple routine that is used to scan the
//! \&{suffix} parameters of a macro.
//!
//! @<Declare the basic parsing subroutines@>=
//! procedure scan_suffix;
//! label done;
//! var @!h,@!t:pointer; {head and tail of the list being built}
//! @!p:pointer; {temporary register}
//! begin h:=get_avail; t:=h;
//! loop@+  begin if cur_cmd=left_bracket then
//!     @<Scan a bracketed subscript and set |cur_cmd:=numeric_token|@>;
//!   if cur_cmd=numeric_token then p:=new_num_tok(cur_mod)
//!   else if (cur_cmd=tag_token)or(cur_cmd=internal_quantity) then
//!     begin p:=get_avail; info(p):=cur_sym;
//!     end
//!   else goto done;
//!   link(t):=p; t:=p; get_x_next;
//!   end;
//! done: cur_exp:=link(h); free_avail(h); cur_type:=token_list;
//! end;
//!
//! @ @<Scan a bracketed subscript and set |cur_cmd:=numeric_token|@>=
//! begin get_x_next; scan_expression;
//! if cur_type<>known then bad_subscript;
//! if cur_cmd<>right_bracket then
//!   begin missing_err("]");@/
//! @.Missing `]'@>
//!   help3("I've seen a `[' and a subscript value, in a suffix,")@/
//!     ("so a right bracket should have come next.")@/
//!     ("I shall pretend that one was there.");@/
//!   back_error;
//!   end;
//! cur_cmd:=numeric_token; cur_mod:=cur_exp;
//! end
//!
//! @* \[41] Parsing secondary and higher expressions.
//! After the intricacies of |scan_primary|\kern-1pt,
//! the |scan_secondary| routine is
//! refreshingly simple. It's not trivial, but the operations are relatively
//! straightforward; the main difficulty is, again, that expressions and data
//! structures might change drastically every time we call |get_x_next|, so a
//! cautious approach is mandatory. For example, a macro defined by
//! \&{primarydef} might have disappeared by the time its second argument has
//! been scanned; we solve this by increasing the reference count of its token
//! list, so that the macro can be called even after it has been clobbered.
//!
//! @<Declare the basic parsing subroutines@>=
//! procedure scan_secondary;
//! label restart,continue;
//! var @!p:pointer; {for list manipulation}
//! @!c,@!d:halfword; {operation codes or modifiers}
//! @!mac_name:pointer; {token defined with \&{primarydef}}
//! begin restart:if(cur_cmd<min_primary_command)or@|
//!  (cur_cmd>max_primary_command) then
//!   bad_exp("A secondary");
//! @.A secondary expression...@>
//! scan_primary;
//! continue: if cur_cmd<=max_secondary_command then
//!  if cur_cmd>=min_secondary_command then
//!   begin p:=stash_cur_exp; c:=cur_mod; d:=cur_cmd;
//!   if d=secondary_primary_macro then
//!     begin mac_name:=cur_sym; add_mac_ref(c);
//!     end;
//!   get_x_next; scan_primary;
//!   if d<>secondary_primary_macro then do_binary(p,c)
//!   else  begin back_input; binary_mac(p,c,mac_name);
//!     decr(ref_count(c)); get_x_next; goto restart;
//!     end;
//!   goto continue;
//!   end;
//! end;
//!
//! @ The following procedure calls a macro that has two parameters,
//! |p| and |cur_exp|.
//!
//! @p procedure binary_mac(@!p,@!c,@!n:pointer);
//! var @!q,@!r:pointer; {nodes in the parameter list}
//! begin q:=get_avail; r:=get_avail; link(q):=r;@/
//! info(q):=p; info(r):=stash_cur_exp;@/
//! macro_call(c,q,n);
//! end;
//!
//! @ The next procedure, |scan_tertiary|, is pretty much the same deal.
//!
//! @<Declare the basic parsing subroutines@>=
//! procedure scan_tertiary;
//! label restart,continue;
//! var @!p:pointer; {for list manipulation}
//! @!c,@!d:halfword; {operation codes or modifiers}
//! @!mac_name:pointer; {token defined with \&{secondarydef}}
//! begin restart:if(cur_cmd<min_primary_command)or@|
//!  (cur_cmd>max_primary_command) then
//!   bad_exp("A tertiary");
//! @.A tertiary expression...@>
//! scan_secondary;
//! if cur_type=future_pen then materialize_pen;
//! continue: if cur_cmd<=max_tertiary_command then
//!  if cur_cmd>=min_tertiary_command then
//!   begin p:=stash_cur_exp; c:=cur_mod; d:=cur_cmd;
//!   if d=tertiary_secondary_macro then
//!     begin mac_name:=cur_sym; add_mac_ref(c);
//!     end;
//!   get_x_next; scan_secondary;
//!   if d<>tertiary_secondary_macro then do_binary(p,c)
//!   else  begin back_input; binary_mac(p,c,mac_name);
//!     decr(ref_count(c)); get_x_next; goto restart;
//!     end;
//!   goto continue;
//!   end;
//! end;
//!
//! @ A |future_pen| becomes a full-fledged pen here.
//!
//! @p procedure materialize_pen;
//! label common_ending;
//! var @!a_minus_b,@!a_plus_b,@!major_axis,@!minor_axis:scaled; {ellipse variables}
//! @!theta:angle; {amount by which the ellipse has been rotated}
//! @!p:pointer; {path traverser}
//! @!q:pointer; {the knot list to be made into a pen}
//! begin q:=cur_exp;
//! if left_type(q)=endpoint then
//!   begin print_err("Pen path must be a cycle");
//! @.Pen path must be a cycle@>
//!   help2("I can't make a pen from the given path.")@/
//!   ("So I've replaced it by the trivial path `(0,0)..cycle'.");
//!   put_get_error; cur_exp:=null_pen; goto common_ending;
//!   end
//! else if left_type(q)=open then
//!   @<Change node |q| to a path for an elliptical pen@>;
//! cur_exp:=make_pen(q);
//! common_ending: toss_knot_list(q); cur_type:=pen_type;
//! end;
//!
//! @ We placed the three points $(0,0)$, $(1,0)$, $(0,1)$ into a \&{pencircle},
//! and they have now been transformed to $(u,v)$, $(A+u,B+v)$, $(C+u,D+v)$;
//! this gives us enough information to deduce the transformation
//! $(x,y)\mapsto(Ax+Cy+u,Bx+Dy+v)$.
//!
//! Given ($A,B,C,D)$ we can always find $(a,b,\theta,\phi)$ such that
//! $$\eqalign{A&=a\cos\phi\cos\theta-b\sin\phi\sin\theta;\cr
//! B&=a\cos\phi\sin\theta+b\sin\phi\cos\theta;\cr
//! C&=-a\sin\phi\cos\theta-b\cos\phi\sin\theta;\cr
//! D&=-a\sin\phi\sin\theta+b\cos\phi\cos\theta.\cr}$$
//! In this notation, the unit circle $(\cos t,\sin t)$ is transformed into
//! $$\bigl(a\cos(\phi+t)\cos\theta-b\sin(\phi+t)\sin\theta,\;
//! a\cos(\phi+t)\sin\theta+b\sin(\phi+t)\cos\theta\bigr)\;+\;(u,v),$$
//! which is an ellipse with semi-axes~$(a,b)$, rotated by~$\theta$ and
//! shifted by~$(u,v)$. To solve the stated equations, we note that it is
//! necessary and sufficient to solve
//! $$\eqalign{A-D&=(a-b)\cos(\theta-\phi),\cr
//! B+C&=(a-b)\sin(\theta-\phi),\cr}
//! \qquad
//! \eqalign{A+D&=(a+b)\cos(\theta+\phi),\cr
//! B-C&=(a+b)\sin(\theta+\phi);\cr}$$
//! and it is easy to find $a-b$, $a+b$, $\theta-\phi$, and $\theta+\phi$
//! from these formulas.
//!
//! The code below uses |(txx,tyx,txy,tyy,tx,ty)| to stand for
//! $(A,B,C,D,u,v)$.
//!
//! @<Change node |q|...@>=
//! begin tx:=x_coord(q); ty:=y_coord(q);
//! txx:=left_x(q)-tx; tyx:=left_y(q)-ty;
//! txy:=right_x(q)-tx; tyy:=right_y(q)-ty;
//! a_minus_b:=pyth_add(txx-tyy,tyx+txy); a_plus_b:=pyth_add(txx+tyy,tyx-txy);
//! major_axis:=half(a_minus_b+a_plus_b); minor_axis:=half(abs(a_plus_b-a_minus_b));
//! if major_axis=minor_axis then theta:=0 {circle}
//! else theta:=half(n_arg(txx-tyy,tyx+txy)+n_arg(txx+tyy,tyx-txy));
//! free_node(q,knot_node_size);
//! q:=make_ellipse(major_axis,minor_axis,theta);
//! if (tx<>0)or(ty<>0) then @<Shift the coordinates of path |q|@>;
//! end
//!
//! @ @<Shift the coordinates of path |q|@>=
//! begin p:=q;
//! repeat x_coord(p):=x_coord(p)+tx; y_coord(p):=y_coord(p)+ty; p:=link(p);
//! until p=q;
//! end
//!
//! @ Finally we reach the deepest level in our quartet of parsing routines.
//! This one is much like the others; but it has an extra complication from
//! paths, which materialize here.
//!
//! @d continue_path=25 {a label inside of |scan_expression|}
//! @d finish_path=26 {another}
//!
//! @<Declare the basic parsing subroutines@>=
//! procedure scan_expression;
//! label restart,done,continue,continue_path,finish_path,exit;
//! var @!p,@!q,@!r,@!pp,@!qq:pointer; {for list manipulation}
//! @!c,@!d:halfword; {operation codes or modifiers}
//! @!my_var_flag:0..max_command_code; {initial value of |var_flag|}
//! @!mac_name:pointer; {token defined with \&{tertiarydef}}
//! @!cycle_hit:boolean; {did a path expression just end with `\&{cycle}'?}
//! @!x,@!y:scaled; {explicit coordinates or tension at a path join}
//! @!t:endpoint..open; {knot type following a path join}
//! begin my_var_flag:=var_flag;
//! restart:if(cur_cmd<min_primary_command)or@|
//!  (cur_cmd>max_primary_command) then
//!   bad_exp("An");
//! @.An expression...@>
//! scan_tertiary;
//! continue: if cur_cmd<=max_expression_command then
//!  if cur_cmd>=min_expression_command then
//!   if (cur_cmd<>equals)or(my_var_flag<>assignment) then
//!   begin p:=stash_cur_exp; c:=cur_mod; d:=cur_cmd;
//!   if d=expression_tertiary_macro then
//!     begin mac_name:=cur_sym; add_mac_ref(c);
//!     end;
//!   if (d<ampersand)or((d=ampersand)and@|
//!    ((type(p)=pair_type)or(type(p)=path_type))) then
//!     @<Scan a path construction operation;
//!       but |return| if |p| has the wrong type@>
//!   else  begin get_x_next; scan_tertiary;
//!     if d<>expression_tertiary_macro then do_binary(p,c)
//!     else  begin back_input; binary_mac(p,c,mac_name);
//!       decr(ref_count(c)); get_x_next; goto restart;
//!       end;
//!     end;
//!   goto continue;
//!   end;
//! exit:end;
//!
//! @ The reader should review the data structure conventions for paths before
//! hoping to understand the next part of this code.
//!
//! @<Scan a path construction operation...@>=
//! begin cycle_hit:=false;
//! @<Convert the left operand, |p|, into a partial path ending at~|q|;
//!   but |return| if |p| doesn't have a suitable type@>;
//! continue_path: @<Determine the path join parameters;
//!   but |goto finish_path| if there's only a direction specifier@>;
//! if cur_cmd=cycle then @<Get ready to close a cycle@>
//! else  begin scan_tertiary;
//!   @<Convert the right operand, |cur_exp|,
//!     into a partial path from |pp| to~|qq|@>;
//!   end;
//! @<Join the partial paths and reset |p| and |q| to the head and tail
//!   of the result@>;
//! if cur_cmd>=min_expression_command then
//!  if cur_cmd<=ampersand then if not cycle_hit then goto continue_path;
//! finish_path:
//! @<Choose control points for the path and put the result into |cur_exp|@>;
//! end
//!
//! @ @<Convert the left operand, |p|, into a partial path ending at~|q|...@>=
//! begin unstash_cur_exp(p);
//! if cur_type=pair_type then p:=new_knot
//! else if cur_type=path_type then p:=cur_exp
//! else return;
//! q:=p;
//! while link(q)<>p do q:=link(q);
//! if left_type(p)<>endpoint then {open up a cycle}
//!   begin r:=copy_knot(p); link(q):=r; q:=r;
//!   end;
//! left_type(p):=open; right_type(q):=open;
//! end
//!
//! @ A pair of numeric values is changed into a knot node for a one-point path
//! when \MF\ discovers that the pair is part of a path.
//!
//! @p@t\4@>@<Declare the procedure called |known_pair|@>@;
//! function new_knot:pointer; {convert a pair to a knot with two endpoints}
//! var @!q:pointer; {the new node}
//! begin q:=get_node(knot_node_size); left_type(q):=endpoint;
//! right_type(q):=endpoint; link(q):=q;@/
//! known_pair; x_coord(q):=cur_x; y_coord(q):=cur_y;
//! new_knot:=q;
//! end;
//!
//! @ The |known_pair| subroutine sets |cur_x| and |cur_y| to the components
//! of the current expression, assuming that the current expression is a
//! pair of known numerics. Unknown components are zeroed, and the
//! current expression is flushed.
//!
//! @<Declare the procedure called |known_pair|@>=
//! procedure known_pair;
//! var @!p:pointer; {the pair node}
//! begin if cur_type<>pair_type then
//!   begin exp_err("Undefined coordinates have been replaced by (0,0)");
//! @.Undefined coordinates...@>
//!   help5("I need x and y numbers for this part of the path.")@/
//!     ("The value I found (see above) was no good;")@/
//!     ("so I'll try to keep going by using zero instead.")@/
//!     ("(Chapter 27 of The METAFONTbook explains that")@/
//! @:METAFONTbook}{\sl The {\logos METAFONT\/}book@>
//!     ("you might want to type `I ???' now.)");
//!   put_get_flush_error(0); cur_x:=0; cur_y:=0;
//!   end
//! else  begin p:=value(cur_exp);
//!   @<Make sure that both |x| and |y| parts of |p| are known;
//!     copy them into |cur_x| and |cur_y|@>;
//!   flush_cur_exp(0);
//!   end;
//! end;
//!
//! @ @<Make sure that both |x| and |y| parts of |p| are known...@>=
//! if type(x_part_loc(p))=known then cur_x:=value(x_part_loc(p))
//! else  begin disp_err(x_part_loc(p),
//!     "Undefined x coordinate has been replaced by 0");
//! @.Undefined coordinates...@>
//!   help5("I need a `known' x value for this part of the path.")@/
//!     ("The value I found (see above) was no good;")@/
//!     ("so I'll try to keep going by using zero instead.")@/
//!     ("(Chapter 27 of The METAFONTbook explains that")@/
//! @:METAFONTbook}{\sl The {\logos METAFONT\/}book@>
//!     ("you might want to type `I ???' now.)");
//!   put_get_error; recycle_value(x_part_loc(p)); cur_x:=0;
//!   end;
//! if type(y_part_loc(p))=known then cur_y:=value(y_part_loc(p))
//! else  begin disp_err(y_part_loc(p),
//!     "Undefined y coordinate has been replaced by 0");
//!   help5("I need a `known' y value for this part of the path.")@/
//!     ("The value I found (see above) was no good;")@/
//!     ("so I'll try to keep going by using zero instead.")@/
//!     ("(Chapter 27 of The METAFONTbook explains that")@/
//!     ("you might want to type `I ???' now.)");
//!   put_get_error; recycle_value(y_part_loc(p)); cur_y:=0;
//!   end
//!
//! @ At this point |cur_cmd| is either |ampersand|, |left_brace|, or |path_join|.
//!
//! @<Determine the path join parameters...@>=
//! if cur_cmd=left_brace then
//!   @<Put the pre-join direction information into node |q|@>;
//! d:=cur_cmd;
//! if d=path_join then @<Determine the tension and/or control points@>
//! else if d<>ampersand then goto finish_path;
//! get_x_next;
//! if cur_cmd=left_brace then
//!   @<Put the post-join direction information into |x| and |t|@>
//! else if right_type(q)<>explicit then
//!   begin t:=open; x:=0;
//!   end
//!
//! @ The |scan_direction| subroutine looks at the directional information
//! that is enclosed in braces, and also scans ahead to the following character.
//! A type code is returned, either |open| (if the direction was $(0,0)$),
//! or |curl| (if the direction was a curl of known value |cur_exp|), or
//! |given| (if the direction is given by the |angle| value that now
//! appears in |cur_exp|).
//!
//! There's nothing difficult about this subroutine, but the program is rather
//! lengthy because a variety of potential errors need to be nipped in the bud.
//!
//! @p function scan_direction:small_number;
//! var @!t:given..open; {the type of information found}
//! @!x:scaled; {an |x| coordinate}
//! begin get_x_next;
//! if cur_cmd=curl_command then @<Scan a curl specification@>
//! else @<Scan a given direction@>;
//! if cur_cmd<>right_brace then
//!   begin missing_err("}");@/
//! @.Missing `\char`\}'@>
//!   help3("I've scanned a direction spec for part of a path,")@/
//!     ("so a right brace should have come next.")@/
//!     ("I shall pretend that one was there.");@/
//!   back_error;
//!   end;
//! get_x_next; scan_direction:=t;
//! end;
//!
//! @ @<Scan a curl specification@>=
//! begin get_x_next; scan_expression;
//! if (cur_type<>known)or(cur_exp<0) then
//!   begin exp_err("Improper curl has been replaced by 1");
//! @.Improper curl@>
//!   help1("A curl must be a known, nonnegative number.");
//!   put_get_flush_error(unity);
//!   end;
//! t:=curl;
//! end
//!
//! @ @<Scan a given direction@>=
//! begin scan_expression;
//! if cur_type>pair_type then @<Get given directions separated by commas@>
//! else known_pair;
//! if (cur_x=0)and(cur_y=0) then t:=open
//! else  begin t:=given; cur_exp:=n_arg(cur_x,cur_y);
//!   end;
//! end
//!
//! @ @<Get given directions separated by commas@>=
//! begin if cur_type<>known then
//!   begin exp_err("Undefined x coordinate has been replaced by 0");
//! @.Undefined coordinates...@>
//!   help5("I need a `known' x value for this part of the path.")@/
//!     ("The value I found (see above) was no good;")@/
//!     ("so I'll try to keep going by using zero instead.")@/
//!     ("(Chapter 27 of The METAFONTbook explains that")@/
//! @:METAFONTbook}{\sl The {\logos METAFONT\/}book@>
//!     ("you might want to type `I ???' now.)");
//!   put_get_flush_error(0);
//!   end;
//! x:=cur_exp;
//! if cur_cmd<>comma then
//!   begin missing_err(",");@/
//! @.Missing `,'@>
//!   help2("I've got the x coordinate of a path direction;")@/
//!     ("will look for the y coordinate next.");
//!   back_error;
//!   end;
//! get_x_next; scan_expression;
//! if cur_type<>known then
//!   begin exp_err("Undefined y coordinate has been replaced by 0");
//!   help5("I need a `known' y value for this part of the path.")@/
//!     ("The value I found (see above) was no good;")@/
//!     ("so I'll try to keep going by using zero instead.")@/
//!     ("(Chapter 27 of The METAFONTbook explains that")@/
//!     ("you might want to type `I ???' now.)");
//!   put_get_flush_error(0);
//!   end;
//! cur_y:=cur_exp; cur_x:=x;
//! end
//!
//! @ At this point |right_type(q)| is usually |open|, but it may have been
//! set to some other value by a previous operation. We must maintain
//! the value of |right_type(q)| in cases such as
//! `\.{..\{curl2\}z\{0,0\}..}'.
//!
//! @<Put the pre-join...@>=
//! begin t:=scan_direction;
//! if t<>open then
//!   begin right_type(q):=t; right_given(q):=cur_exp;
//!   if left_type(q)=open then
//!     begin left_type(q):=t; left_given(q):=cur_exp;
//!     end; {note that |left_given(q)=left_curl(q)|}
//!   end;
//! end
//!
//! @ Since |left_tension| and |left_y| share the same position in knot nodes,
//! and since |left_given| is similarly equivalent to |left_x|, we use
//! |x| and |y| to hold the given direction and tension information when
//! there are no explicit control points.
//!
//! @<Put the post-join...@>=
//! begin t:=scan_direction;
//! if right_type(q)<>explicit then x:=cur_exp
//! else t:=explicit; {the direction information is superfluous}
//! end
//!
//! @ @<Determine the tension and/or...@>=
//! begin get_x_next;
//! if cur_cmd=tension then @<Set explicit tensions@>
//! else if cur_cmd=controls then @<Set explicit control points@>
//! else  begin right_tension(q):=unity; y:=unity; back_input; {default tension}
//!   goto done;
//!   end;
//! if cur_cmd<>path_join then
//!   begin missing_err("..");@/
//! @.Missing `..'@>
//!   help1("A path join command should end with two dots.");
//!   back_error;
//!   end;
//! done:end
//!
//! @ @<Set explicit tensions@>=
//! begin get_x_next; y:=cur_cmd;
//! if cur_cmd=at_least then get_x_next;
//! scan_primary;
//! @<Make sure that the current expression is a valid tension setting@>;
//! if y=at_least then negate(cur_exp);
//! right_tension(q):=cur_exp;
//! if cur_cmd=and_command then
//!   begin get_x_next; y:=cur_cmd;
//!   if cur_cmd=at_least then get_x_next;
//!   scan_primary;
//!   @<Make sure that the current expression is a valid tension setting@>;
//!   if y=at_least then negate(cur_exp);
//!   end;
//! y:=cur_exp;
//! end
//!
//! @ @d min_tension==three_quarter_unit
//!
//! @<Make sure that the current expression is a valid tension setting@>=
//! if (cur_type<>known)or(cur_exp<min_tension) then
//!   begin exp_err("Improper tension has been set to 1");
//! @.Improper tension@>
//!   help1("The expression above should have been a number >=3/4.");
//!   put_get_flush_error(unity);
//!   end
//!
//! @ @<Set explicit control points@>=
//! begin right_type(q):=explicit; t:=explicit; get_x_next; scan_primary;@/
//! known_pair; right_x(q):=cur_x; right_y(q):=cur_y;
//! if cur_cmd<>and_command then
//!   begin x:=right_x(q); y:=right_y(q);
//!   end
//! else  begin get_x_next; scan_primary;@/
//!   known_pair; x:=cur_x; y:=cur_y;
//!   end;
//! end
//!
//! @ @<Convert the right operand, |cur_exp|, into a partial path...@>=
//! begin if cur_type<>path_type then pp:=new_knot
//! else pp:=cur_exp;
//! qq:=pp;
//! while link(qq)<>pp do qq:=link(qq);
//! if left_type(pp)<>endpoint then {open up a cycle}
//!   begin r:=copy_knot(pp); link(qq):=r; qq:=r;
//!   end;
//! left_type(pp):=open; right_type(qq):=open;
//! end
//!
//! @ If a person tries to define an entire path by saying `\.{(x,y)\&cycle}',
//! we silently change the specification to `\.{(x,y)..cycle}', since a cycle
//! shouldn't have length zero.
//!
//! @<Get ready to close a cycle@>=
//! begin cycle_hit:=true; get_x_next; pp:=p; qq:=p;
//! if d=ampersand then if p=q then
//!   begin d:=path_join; right_tension(q):=unity; y:=unity;
//!   end;
//! end
//!
//! @ @<Join the partial paths and reset |p| and |q|...@>=
//! begin if d=ampersand then
//!  if (x_coord(q)<>x_coord(pp))or(y_coord(q)<>y_coord(pp)) then
//!   begin print_err("Paths don't touch; `&' will be changed to `..'");
//! @.Paths don't touch@>
//!   help3("When you join paths `p&q', the ending point of p")@/
//!     ("must be exactly equal to the starting point of q.")@/
//!     ("So I'm going to pretend that you said `p..q' instead.");
//!   put_get_error; d:=path_join; right_tension(q):=unity; y:=unity;
//!   end;
//! @<Plug an opening in |right_type(pp)|, if possible@>;
//! if d=ampersand then @<Splice independent paths together@>
//! else  begin @<Plug an opening in |right_type(q)|, if possible@>;
//!   link(q):=pp; left_y(pp):=y;
//!   if t<>open then
//!     begin left_x(pp):=x; left_type(pp):=t;
//!     end;
//!   end;
//! q:=qq;
//! end
//!
//! @ @<Plug an opening in |right_type(q)|...@>=
//! if right_type(q)=open then
//!   if (left_type(q)=curl)or(left_type(q)=given) then
//!     begin right_type(q):=left_type(q); right_given(q):=left_given(q);
//!     end
//!
//! @ @<Plug an opening in |right_type(pp)|...@>=
//! if right_type(pp)=open then
//!   if (t=curl)or(t=given) then
//!     begin right_type(pp):=t; right_given(pp):=x;
//!     end
//!
//! @ @<Splice independent paths together@>=
//! begin if left_type(q)=open then if right_type(q)=open then
//!     begin left_type(q):=curl; left_curl(q):=unity;
//!     end;
//! if right_type(pp)=open then if t=open then
//!   begin right_type(pp):=curl; right_curl(pp):=unity;
//!   end;
//! right_type(q):=right_type(pp); link(q):=link(pp);@/
//! right_x(q):=right_x(pp); right_y(q):=right_y(pp);
//! free_node(pp,knot_node_size);
//! if qq=pp then qq:=q;
//! end
//!
//! @ @<Choose control points for the path...@>=
//! if cycle_hit then
//!   begin if d=ampersand then p:=q;
//!   end
//! else  begin left_type(p):=endpoint;
//!   if right_type(p)=open then
//!     begin right_type(p):=curl; right_curl(p):=unity;
//!     end;
//!   right_type(q):=endpoint;
//!   if left_type(q)=open then
//!     begin left_type(q):=curl; left_curl(q):=unity;
//!     end;
//!   link(q):=p;
//!   end;
//! make_choices(p);
//! cur_type:=path_type; cur_exp:=p
//!
//! @ Finally, we sometimes need to scan an expression whose value is
//! supposed to be either |true_code| or |false_code|.
//!
//! @<Declare the basic parsing subroutines@>=
//! procedure get_boolean;
//! begin get_x_next; scan_expression;
//! if cur_type<>boolean_type then
//!   begin exp_err("Undefined condition will be treated as `false'");
//! @.Undefined condition...@>
//!   help2("The expression shown above should have had a definite")@/
//!     ("true-or-false value. I'm changing it to `false'.");@/
//!   put_get_flush_error(false_code); cur_type:=boolean_type;
//!   end;
//! end;
//!
//! @* \[42] Doing the operations.
//! The purpose of parsing is primarily to permit people to avoid piles of
//! parentheses. But the real work is done after the structure of an expression
//! has been recognized; that's when new expressions are generated. We
//! turn now to the guts of \MF, which handles individual operators that
//! have come through the parsing mechanism.
//!
//! We'll start with the easy ones that take no operands, then work our way
//! up to operators with one and ultimately two arguments. In other words,
//! we will write the three procedures |do_nullary|, |do_unary|, and |do_binary|
//! that are invoked periodically by the expression scanners.
//!
//! First let's make sure that all of the primitive operators are in the
//! hash table. Although |scan_primary| and its relatives made use of the
//! \\{cmd} code for these operators, the \\{do} routines base everything
//! on the \\{mod} code. For example, |do_binary| doesn't care whether the
//! operation it performs is a |primary_binary| or |secondary_binary|, etc.
//!
//! @<Put each...@>=
//! primitive("true",nullary,true_code);@/
//! @!@:true_}{\&{true} primitive@>
//! primitive("false",nullary,false_code);@/
//! @!@:false_}{\&{false} primitive@>
//! primitive("nullpicture",nullary,null_picture_code);@/
//! @!@:null_picture_}{\&{nullpicture} primitive@>
//! primitive("nullpen",nullary,null_pen_code);@/
//! @!@:null_pen_}{\&{nullpen} primitive@>
//! primitive("jobname",nullary,job_name_op);@/
//! @!@:job_name_}{\&{jobname} primitive@>
//! primitive("readstring",nullary,read_string_op);@/
//! @!@:read_string_}{\&{readstring} primitive@>
//! primitive("pencircle",nullary,pen_circle);@/
//! @!@:pen_circle_}{\&{pencircle} primitive@>
//! primitive("normaldeviate",nullary,normal_deviate);@/
//! @!@:normal_deviate_}{\&{normaldeviate} primitive@>
//! primitive("odd",unary,odd_op);@/
//! @!@:odd_}{\&{odd} primitive@>
//! primitive("known",unary,known_op);@/
//! @!@:known_}{\&{known} primitive@>
//! primitive("unknown",unary,unknown_op);@/
//! @!@:unknown_}{\&{unknown} primitive@>
//! primitive("not",unary,not_op);@/
//! @!@:not_}{\&{not} primitive@>
//! primitive("decimal",unary,decimal);@/
//! @!@:decimal_}{\&{decimal} primitive@>
//! primitive("reverse",unary,reverse);@/
//! @!@:reverse_}{\&{reverse} primitive@>
//! primitive("makepath",unary,make_path_op);@/
//! @!@:make_path_}{\&{makepath} primitive@>
//! primitive("makepen",unary,make_pen_op);@/
//! @!@:make_pen_}{\&{makepen} primitive@>
//! primitive("totalweight",unary,total_weight_op);@/
//! @!@:total_weight_}{\&{totalweight} primitive@>
//! primitive("oct",unary,oct_op);@/
//! @!@:oct_}{\&{oct} primitive@>
//! primitive("hex",unary,hex_op);@/
//! @!@:hex_}{\&{hex} primitive@>
//! primitive("ASCII",unary,ASCII_op);@/
//! @!@:ASCII_}{\&{ASCII} primitive@>
//! primitive("char",unary,char_op);@/
//! @!@:char_}{\&{char} primitive@>
//! primitive("length",unary,length_op);@/
//! @!@:length_}{\&{length} primitive@>
//! primitive("turningnumber",unary,turning_op);@/
//! @!@:turning_number_}{\&{turningnumber} primitive@>
//! primitive("xpart",unary,x_part);@/
//! @!@:x_part_}{\&{xpart} primitive@>
//! primitive("ypart",unary,y_part);@/
//! @!@:y_part_}{\&{ypart} primitive@>
//! primitive("xxpart",unary,xx_part);@/
//! @!@:xx_part_}{\&{xxpart} primitive@>
//! primitive("xypart",unary,xy_part);@/
//! @!@:xy_part_}{\&{xypart} primitive@>
//! primitive("yxpart",unary,yx_part);@/
//! @!@:yx_part_}{\&{yxpart} primitive@>
//! primitive("yypart",unary,yy_part);@/
//! @!@:yy_part_}{\&{yypart} primitive@>
//! primitive("sqrt",unary,sqrt_op);@/
//! @!@:sqrt_}{\&{sqrt} primitive@>
//! primitive("mexp",unary,m_exp_op);@/
//! @!@:m_exp_}{\&{mexp} primitive@>
//! primitive("mlog",unary,m_log_op);@/
//! @!@:m_log_}{\&{mlog} primitive@>
//! primitive("sind",unary,sin_d_op);@/
//! @!@:sin_d_}{\&{sind} primitive@>
//! primitive("cosd",unary,cos_d_op);@/
//! @!@:cos_d_}{\&{cosd} primitive@>
//! primitive("floor",unary,floor_op);@/
//! @!@:floor_}{\&{floor} primitive@>
//! primitive("uniformdeviate",unary,uniform_deviate);@/
//! @!@:uniform_deviate_}{\&{uniformdeviate} primitive@>
//! primitive("charexists",unary,char_exists_op);@/
//! @!@:char_exists_}{\&{charexists} primitive@>
//! primitive("angle",unary,angle_op);@/
//! @!@:angle_}{\&{angle} primitive@>
//! primitive("cycle",cycle,cycle_op);@/
//! @!@:cycle_}{\&{cycle} primitive@>
//! primitive("+",plus_or_minus,plus);@/
//! @!@:+ }{\.{+} primitive@>
//! primitive("-",plus_or_minus,minus);@/
//! @!@:- }{\.{-} primitive@>
//! primitive("*",secondary_binary,times);@/
//! @!@:* }{\.{*} primitive@>
//! primitive("/",slash,over); eqtb[frozen_slash]:=eqtb[cur_sym];@/
//! @!@:/ }{\.{/} primitive@>
//! primitive("++",tertiary_binary,pythag_add);@/
//! @!@:++_}{\.{++} primitive@>
//! primitive("+-+",tertiary_binary,pythag_sub);@/
//! @!@:+-+_}{\.{+-+} primitive@>
//! primitive("and",and_command,and_op);@/
//! @!@:and_}{\&{and} primitive@>
//! primitive("or",tertiary_binary,or_op);@/
//! @!@:or_}{\&{or} primitive@>
//! primitive("<",expression_binary,less_than);@/
//! @!@:< }{\.{<} primitive@>
//! primitive("<=",expression_binary,less_or_equal);@/
//! @!@:<=_}{\.{<=} primitive@>
//! primitive(">",expression_binary,greater_than);@/
//! @!@:> }{\.{>} primitive@>
//! primitive(">=",expression_binary,greater_or_equal);@/
//! @!@:>=_}{\.{>=} primitive@>
//! primitive("=",equals,equal_to);@/
//! @!@:= }{\.{=} primitive@>
//! primitive("<>",expression_binary,unequal_to);@/
//! @!@:<>_}{\.{<>} primitive@>
//! primitive("substring",primary_binary,substring_of);@/
//! @!@:substring_}{\&{substring} primitive@>
//! primitive("subpath",primary_binary,subpath_of);@/
//! @!@:subpath_}{\&{subpath} primitive@>
//! primitive("directiontime",primary_binary,direction_time_of);@/
//! @!@:direction_time_}{\&{directiontime} primitive@>
//! primitive("point",primary_binary,point_of);@/
//! @!@:point_}{\&{point} primitive@>
//! primitive("precontrol",primary_binary,precontrol_of);@/
//! @!@:precontrol_}{\&{precontrol} primitive@>
//! primitive("postcontrol",primary_binary,postcontrol_of);@/
//! @!@:postcontrol_}{\&{postcontrol} primitive@>
//! primitive("penoffset",primary_binary,pen_offset_of);@/
//! @!@:pen_offset_}{\&{penoffset} primitive@>
//! primitive("&",ampersand,concatenate);@/
//! @!@:!!!}{\.{\&} primitive@>
//! primitive("rotated",secondary_binary,rotated_by);@/
//! @!@:rotated_}{\&{rotated} primitive@>
//! primitive("slanted",secondary_binary,slanted_by);@/
//! @!@:slanted_}{\&{slanted} primitive@>
//! primitive("scaled",secondary_binary,scaled_by);@/
//! @!@:scaled_}{\&{scaled} primitive@>
//! primitive("shifted",secondary_binary,shifted_by);@/
//! @!@:shifted_}{\&{shifted} primitive@>
//! primitive("transformed",secondary_binary,transformed_by);@/
//! @!@:transformed_}{\&{transformed} primitive@>
//! primitive("xscaled",secondary_binary,x_scaled);@/
//! @!@:x_scaled_}{\&{xscaled} primitive@>
//! primitive("yscaled",secondary_binary,y_scaled);@/
//! @!@:y_scaled_}{\&{yscaled} primitive@>
//! primitive("zscaled",secondary_binary,z_scaled);@/
//! @!@:z_scaled_}{\&{zscaled} primitive@>
//! primitive("intersectiontimes",tertiary_binary,intersect);@/
//! @!@:intersection_times_}{\&{intersectiontimes} primitive@>
//!
//! @ @<Cases of |print_cmd...@>=
//! nullary,unary,primary_binary,secondary_binary,tertiary_binary,
//!  expression_binary,cycle,plus_or_minus,slash,ampersand,equals,and_command:
//!   print_op(m);
//!
//! @ OK, let's look at the simplest \\{do} procedure first.
//!
//! @p procedure do_nullary(@!c:quarterword);
//! var @!k:integer; {all-purpose loop index}
//! begin check_arith;
//! if internal[tracing_commands]>two then
//!   show_cmd_mod(nullary,c);
//! case c of
//! true_code,false_code:begin cur_type:=boolean_type; cur_exp:=c;
//!   end;
//! null_picture_code:begin cur_type:=picture_type;
//!   cur_exp:=get_node(edge_header_size); init_edges(cur_exp);
//!   end;
//! null_pen_code:begin cur_type:=pen_type; cur_exp:=null_pen;
//!   end;
//! normal_deviate:begin cur_type:=known; cur_exp:=norm_rand;
//!   end;
//! pen_circle:@<Make a special knot node for \&{pencircle}@>;
//! job_name_op: begin if job_name=0 then open_log_file;
//!   cur_type:=string_type; cur_exp:=job_name;
//!   end;
//! read_string_op:@<Read a string from the terminal@>;
//! end; {there are no other cases}
//! check_arith;
//! end;
//!
//! @ @<Make a special knot node for \&{pencircle}@>=
//! begin cur_type:=future_pen; cur_exp:=get_node(knot_node_size);
//! left_type(cur_exp):=open; right_type(cur_exp):=open;
//! link(cur_exp):=cur_exp;@/
//! x_coord(cur_exp):=0; y_coord(cur_exp):=0;@/
//! left_x(cur_exp):=unity; left_y(cur_exp):=0;@/
//! right_x(cur_exp):=0; right_y(cur_exp):=unity;@/
//! end
//!
//! @ @<Read a string...@>=
//! begin if interaction<=nonstop_mode then
//!   fatal_error("*** (cannot readstring in nonstop modes)");
//! begin_file_reading; name:=1; prompt_input("");
//! str_room(last-start);
//! for k:=start to last-1 do append_char(buffer[k]);
//! end_file_reading; cur_type:=string_type; cur_exp:=make_string;
//! end
//!
//! @ Things get a bit more interesting when there's an operand. The
//! operand to |do_unary| appears in |cur_type| and |cur_exp|.
//!
//! @p @t\4@>@<Declare unary action procedures@>@;
//! procedure do_unary(@!c:quarterword);
//! var @!p,@!q:pointer; {for list manipulation}
//! @!x:integer; {a temporary register}
//! begin check_arith;
//! if internal[tracing_commands]>two then
//!   @<Trace the current unary operation@>;
//! case c of
//! plus:if cur_type<pair_type then
//!   if cur_type<>picture_type then bad_unary(plus);
//! minus:@<Negate the current expression@>;
//! @t\4@>@<Additional cases of unary operators@>@;
//! end; {there are no other cases}
//! check_arith;
//! end;
//!
//! @ The |nice_pair| function returns |true| if both components of a pair
//! are known.
//!
//! @<Declare unary action procedures@>=
//! function nice_pair(@!p:integer;@!t:quarterword):boolean;
//! label exit;
//! begin if t=pair_type then
//!   begin p:=value(p);
//!   if type(x_part_loc(p))=known then
//!    if type(y_part_loc(p))=known then
//!     begin nice_pair:=true; return;
//!     end;
//!   end;
//! nice_pair:=false;
//! exit:end;
//!
//! @ @<Declare unary action...@>=
//! procedure print_known_or_unknown_type(@!t:small_number;@!v:integer);
//! begin print_char("(");
//! if t<dependent then
//!   if t<>pair_type then print_type(t)
//!   else if nice_pair(v,pair_type) then print("pair")
//!   else print("unknown pair")
//! else print("unknown numeric");
//! print_char(")");
//! end;
//!
//! @ @<Declare unary action...@>=
//! procedure bad_unary(@!c:quarterword);
//! begin exp_err("Not implemented: "); print_op(c);
//! @.Not implemented...@>
//! print_known_or_unknown_type(cur_type,cur_exp);
//! help3("I'm afraid I don't know how to apply that operation to that")@/
//!   ("particular type. Continue, and I'll simply return the")@/
//!   ("argument (shown above) as the result of the operation.");
//! put_get_error;
//! end;
//!
//! @ @<Trace the current unary operation@>=
//! begin begin_diagnostic; print_nl("{"); print_op(c); print_char("(");@/
//! print_exp(null,0); {show the operand, but not verbosely}
//! print(")}"); end_diagnostic(false);
//! end
//!
//! @ Negation is easy except when the current expression
//! is of type |independent|, or when it is a pair with one or more
//! |independent| components.
//!
//! It is tempting to argue that the negative of an independent variable
//! is an independent variable, hence we don't have to do anything when
//! negating it. The fallacy is that other dependent variables pointing
//! to the current expression must change the sign of their
//! coefficients if we make no change to the current expression.
//!
//! Instead, we work around the problem by copying the current expression
//! and recycling it afterwards (cf.~the |stash_in| routine).
//!
//! @<Negate the current expression@>=
//! case cur_type of
//! pair_type,independent: begin q:=cur_exp; make_exp_copy(q);
//!   if cur_type=dependent then negate_dep_list(dep_list(cur_exp))
//!   else if cur_type=pair_type then
//!     begin p:=value(cur_exp);
//!     if type(x_part_loc(p))=known then negate(value(x_part_loc(p)))
//!     else negate_dep_list(dep_list(x_part_loc(p)));
//!     if type(y_part_loc(p))=known then negate(value(y_part_loc(p)))
//!     else negate_dep_list(dep_list(y_part_loc(p)));
//!     end; {if |cur_type=known| then |cur_exp=0|}
//!   recycle_value(q); free_node(q,value_node_size);
//!   end;
//! dependent,proto_dependent:negate_dep_list(dep_list(cur_exp));
//! known:negate(cur_exp);
//! picture_type:negate_edges(cur_exp);
//! othercases bad_unary(minus)
//! endcases
//!
//! @ @<Declare unary action...@>=
//! procedure negate_dep_list(@!p:pointer);
//! label exit;
//! begin loop@+begin negate(value(p));
//!   if info(p)=null then return;
//!   p:=link(p);
//!   end;
//! exit:end;
//!
//! @ @<Additional cases of unary operators@>=
//! not_op: if cur_type<>boolean_type then bad_unary(not_op)
//!   else cur_exp:=true_code+false_code-cur_exp;
//!
//! @ @d three_sixty_units==23592960 {that's |360*unity|}
//! @d boolean_reset(#)==if # then cur_exp:=true_code@+else cur_exp:=false_code
//!
//! @<Additional cases of unary operators@>=
//! sqrt_op,m_exp_op,m_log_op,sin_d_op,cos_d_op,floor_op,
//!  uniform_deviate,odd_op,char_exists_op:@t@>@;@/
//!   if cur_type<>known then bad_unary(c)
//!   else case c of
//!   sqrt_op:cur_exp:=square_rt(cur_exp);
//!   m_exp_op:cur_exp:=m_exp(cur_exp);
//!   m_log_op:cur_exp:=m_log(cur_exp);
//!   sin_d_op,cos_d_op:begin n_sin_cos((cur_exp mod three_sixty_units)*16);
//!     if c=sin_d_op then cur_exp:=round_fraction(n_sin)
//!     else cur_exp:=round_fraction(n_cos);
//!     end;
//!   floor_op:cur_exp:=floor_scaled(cur_exp);
//!   uniform_deviate:cur_exp:=unif_rand(cur_exp);
//!   odd_op: begin boolean_reset(odd(round_unscaled(cur_exp)));
//!     cur_type:=boolean_type;
//!     end;
//!   char_exists_op:@<Determine if a character has been shipped out@>;
//!   end; {there are no other cases}
//!
//! @ @<Additional cases of unary operators@>=
//! angle_op:if nice_pair(cur_exp,cur_type) then
//!     begin p:=value(cur_exp);
//!     x:=n_arg(value(x_part_loc(p)),value(y_part_loc(p)));
//!     if x>=0 then flush_cur_exp((x+8)div 16)
//!     else flush_cur_exp(-((-x+8)div 16));
//!     end
//!   else bad_unary(angle_op);
//!
//! @ If the current expression is a pair, but the context wants it to
//! be a path, we call |pair_to_path|.
//!
//! @<Declare unary action...@>=
//! procedure pair_to_path;
//! begin cur_exp:=new_knot; cur_type:=path_type;
//! end;
//!
//! @ @<Additional cases of unary operators@>=
//! x_part,y_part:if (cur_type<=pair_type)and(cur_type>=transform_type) then
//!     take_part(c)
//!   else bad_unary(c);
//! xx_part,xy_part,yx_part,yy_part: if cur_type=transform_type then take_part(c)
//!   else bad_unary(c);
//!
//! @ In the following procedure, |cur_exp| points to a capsule, which points to
//! a big node. We want to delete all but one part of the big node.
//!
//! @<Declare unary action...@>=
//! procedure take_part(@!c:quarterword);
//! var @!p:pointer; {the big node}
//! begin p:=value(cur_exp); value(temp_val):=p; type(temp_val):=cur_type;
//! link(p):=temp_val; free_node(cur_exp,value_node_size);
//! make_exp_copy(p+2*(c-x_part));
//! recycle_value(temp_val);
//! end;
//!
//! @ @<Initialize table entries...@>=
//! name_type(temp_val):=capsule;
//!
//! @ @<Additional cases of unary...@>=
//! char_op: if cur_type<>known then bad_unary(char_op)
//!   else  begin cur_exp:=round_unscaled(cur_exp) mod 256; cur_type:=string_type;
//!     if cur_exp<0 then cur_exp:=cur_exp+256;
//!     if length(cur_exp)<>1 then
//!       begin str_room(1); append_char(cur_exp); cur_exp:=make_string;
//!       end;
//!     end;
//! decimal: if cur_type<>known then bad_unary(decimal)
//!   else  begin old_setting:=selector; selector:=new_string;
//!     print_scaled(cur_exp); cur_exp:=make_string;
//!     selector:=old_setting; cur_type:=string_type;
//!     end;
//! oct_op,hex_op,ASCII_op: if cur_type<>string_type then bad_unary(c)
//!   else str_to_num(c);
//!
//! @ @<Declare unary action...@>=
//! procedure str_to_num(@!c:quarterword); {converts a string to a number}
//! var @!n:integer; {accumulator}
//! @!m:ASCII_code; {current character}
//! @!k:pool_pointer; {index into |str_pool|}
//! @!b:8..16; {radix of conversion}
//! @!bad_char:boolean; {did the string contain an invalid digit?}
//! begin if c=ASCII_op then
//!   if length(cur_exp)=0 then n:=-1
//!   else n:=so(str_pool[str_start[cur_exp]])
//! else  begin if c=oct_op then b:=8@+else b:=16;
//!   n:=0; bad_char:=false;
//!   for k:=str_start[cur_exp] to str_start[cur_exp+1]-1 do
//!     begin m:=so(str_pool[k]);
//!     if (m>="0")and(m<="9") then m:=m-"0"
//!     else if (m>="A")and(m<="F") then m:=m-"A"+10
//!     else if (m>="a")and(m<="f") then m:=m-"a"+10
//!     else  begin bad_char:=true; m:=0;
//!       end;
//!     if m>=b then
//!       begin bad_char:=true; m:=0;
//!       end;
//!     if n<32768 div b then n:=n*b+m@+else n:=32767;
//!     end;
//!   @<Give error messages if |bad_char| or |n>=4096|@>;
//!   end;
//! flush_cur_exp(n*unity);
//! end;
//!
//! @ @<Give error messages if |bad_char|...@>=
//! if bad_char then
//!   begin exp_err("String contains illegal digits");
//! @.String contains illegal digits@>
//!   if c=oct_op then
//!     help1("I zeroed out characters that weren't in the range 0..7.")
//!   else help1("I zeroed out characters that weren't hex digits.");
//!   put_get_error;
//!   end;
//! if n>4095 then
//!   begin print_err("Number too large ("); print_int(n); print_char(")");
//! @.Number too large@>
//!   help1("I have trouble with numbers greater than 4095; watch out.");
//!   put_get_error;
//!   end
//!
//! @ The length operation is somewhat unusual in that it applies to a variety
//! of different types of operands.
//!
//! @<Additional cases of unary...@>=
//! length_op: if cur_type=string_type then flush_cur_exp(length(cur_exp)*unity)
//!   else if cur_type=path_type then flush_cur_exp(path_length)
//!   else if cur_type=known then cur_exp:=abs(cur_exp)
//!   else if nice_pair(cur_exp,cur_type) then
//!     flush_cur_exp(pyth_add(value(x_part_loc(value(cur_exp))),@|
//!       value(y_part_loc(value(cur_exp)))))
//!   else bad_unary(c);
//!
//! @ @<Declare unary action...@>=
//! function path_length:scaled; {computes the length of the current path}
//! var @!n:scaled; {the path length so far}
//! @!p:pointer; {traverser}
//! begin p:=cur_exp;
//! if left_type(p)=endpoint then n:=-unity@+else n:=0;
//! repeat p:=link(p); n:=n+unity;
//! until p=cur_exp;
//! path_length:=n;
//! end;
//!
//! @ The turning number is computed only with respect to null pens. A different
//! pen might affect the turning number, in degenerate cases, because autorounding
//! will produce a slightly different path, or because excessively large coordinates
//! might be truncated.
//!
//! @<Additional cases of unary...@>=
//! turning_op:if cur_type=pair_type then flush_cur_exp(0)
//!   else if cur_type<>path_type then bad_unary(turning_op)
//!   else if left_type(cur_exp)=endpoint then
//!      flush_cur_exp(0) {not a cyclic path}
//!   else  begin cur_pen:=null_pen; cur_path_type:=contour_code;
//!     cur_exp:=make_spec(cur_exp,
//!       fraction_one-half_unit-1-el_gordo,0);
//!     flush_cur_exp(turning_number*unity); {convert to |scaled|}
//!     end;
//!
//! @ @d type_test_end== flush_cur_exp(true_code)
//!   else flush_cur_exp(false_code);
//!   cur_type:=boolean_type;
//!   end
//! @d type_range_end(#)==(cur_type<=#) then type_test_end
//! @d type_range(#)==begin if (cur_type>=#) and type_range_end
//! @d type_test(#)==begin if cur_type=# then type_test_end
//!
//! @<Additional cases of unary operators@>=
//! boolean_type: type_range(boolean_type)(unknown_boolean);
//! string_type: type_range(string_type)(unknown_string);
//! pen_type: type_range(pen_type)(future_pen);
//! path_type: type_range(path_type)(unknown_path);
//! picture_type: type_range(picture_type)(unknown_picture);
//! transform_type,pair_type: type_test(c);
//! numeric_type: type_range(known)(independent);
//! known_op,unknown_op: test_known(c);
//!
//! @ @<Declare unary action procedures@>=
//! procedure test_known(@!c:quarterword);
//! label done;
//! var @!b:true_code..false_code; {is the current expression known?}
//! @!p,@!q:pointer; {locations in a big node}
//! begin b:=false_code;
//! case cur_type of
//! vacuous,boolean_type,string_type,pen_type,future_pen,path_type,picture_type,
//!  known: b:=true_code;
//! transform_type,pair_type:begin p:=value(cur_exp); q:=p+big_node_size[cur_type];
//!   repeat q:=q-2;
//!   if type(q)<>known then goto done;
//!   until q=p;
//!   b:=true_code;
//! done:  end;
//! othercases do_nothing
//! endcases;
//! if c=known_op then flush_cur_exp(b)
//! else flush_cur_exp(true_code+false_code-b);
//! cur_type:=boolean_type;
//! end;
//!
//! @ @<Additional cases of unary operators@>=
//! cycle_op: begin if cur_type<>path_type then flush_cur_exp(false_code)
//!   else if left_type(cur_exp)<>endpoint then flush_cur_exp(true_code)
//!   else flush_cur_exp(false_code);
//!   cur_type:=boolean_type;
//!   end;
//!
//! @ @<Additional cases of unary operators@>=
//! make_pen_op: begin if cur_type=pair_type then pair_to_path;
//!   if cur_type=path_type then cur_type:=future_pen
//!   else bad_unary(make_pen_op);
//!   end;
//! make_path_op: begin if cur_type=future_pen then materialize_pen;
//!   if cur_type<>pen_type then bad_unary(make_path_op)
//!   else  begin flush_cur_exp(make_path(cur_exp)); cur_type:=path_type;
//!     end;
//!   end;
//! total_weight_op: if cur_type<>picture_type then bad_unary(total_weight_op)
//!   else flush_cur_exp(total_weight(cur_exp));
//! reverse: if cur_type=path_type then
//!     begin p:=htap_ypoc(cur_exp);
//!     if right_type(p)=endpoint then p:=link(p);
//!     toss_knot_list(cur_exp); cur_exp:=p;
//!     end
//!   else if cur_type=pair_type then pair_to_path
//!   else bad_unary(reverse);
//!
//! @ Finally, we have the operations that combine a capsule~|p|
//! with the current expression.
//!
//! @p @t\4@>@<Declare binary action procedures@>@;
//! procedure do_binary(@!p:pointer;@!c:quarterword);
//! label done,done1,exit;
//! var @!q,@!r,@!rr:pointer; {for list manipulation}
//! @!old_p,@!old_exp:pointer; {capsules to recycle}
//! @!v:integer; {for numeric manipulation}
//! begin check_arith;
//! if internal[tracing_commands]>two then
//!   @<Trace the current binary operation@>;
//! @<Sidestep |independent| cases in capsule |p|@>;
//! @<Sidestep |independent| cases in the current expression@>;
//! case c of
//! plus,minus:@<Add or subtract the current expression from |p|@>;
//! @t\4@>@<Additional cases of binary operators@>@;
//! end; {there are no other cases}
//! recycle_value(p); free_node(p,value_node_size); {|return| to avoid this}
//! exit:check_arith; @<Recycle any sidestepped |independent| capsules@>;
//! end;
//!
//! @ @<Declare binary action...@>=
//! procedure bad_binary(@!p:pointer;@!c:quarterword);
//! begin disp_err(p,"");
//! exp_err("Not implemented: ");
//! @.Not implemented...@>
//! if c>=min_of then print_op(c);
//! print_known_or_unknown_type(type(p),p);
//! if c>=min_of then print("of")@+else print_op(c);
//! print_known_or_unknown_type(cur_type,cur_exp);@/
//! help3("I'm afraid I don't know how to apply that operation to that")@/
//!   ("combination of types. Continue, and I'll return the second")@/
//!   ("argument (see above) as the result of the operation.");
//! put_get_error;
//! end;
//!
//! @ @<Trace the current binary operation@>=
//! begin begin_diagnostic; print_nl("{(");
//! print_exp(p,0); {show the operand, but not verbosely}
//! print_char(")"); print_op(c); print_char("(");@/
//! print_exp(null,0); print(")}"); end_diagnostic(false);
//! end
//!
//! @ Several of the binary operations are potentially complicated by the
//! fact that |independent| values can sneak into capsules. For example,
//! we've seen an instance of this difficulty in the unary operation
//! of negation. In order to reduce the number of cases that need to be
//! handled, we first change the two operands (if necessary)
//! to rid them of |independent| components. The original operands are
//! put into capsules called |old_p| and |old_exp|, which will be
//! recycled after the binary operation has been safely carried out.
//!
//! @<Recycle any sidestepped |independent| capsules@>=
//! if old_p<>null then
//!   begin recycle_value(old_p); free_node(old_p,value_node_size);
//!   end;
//! if old_exp<>null then
//!   begin recycle_value(old_exp); free_node(old_exp,value_node_size);
//!   end
//!
//! @ A big node is considered to be ``tarnished'' if it contains at least one
//! independent component. We will define a simple function called `|tarnished|'
//! that returns |null| if and only if its argument is not tarnished.
//!
//! @<Sidestep |independent| cases in capsule |p|@>=
//! case type(p) of
//! transform_type,pair_type: old_p:=tarnished(p);
//! independent: old_p:=void;
//! othercases old_p:=null
//! endcases;
//! if old_p<>null then
//!   begin q:=stash_cur_exp; old_p:=p; make_exp_copy(old_p);
//!   p:=stash_cur_exp; unstash_cur_exp(q);
//!   end;
//!
//! @ @<Sidestep |independent| cases in the current expression@>=
//! case cur_type of
//! transform_type,pair_type:old_exp:=tarnished(cur_exp);
//! independent:old_exp:=void;
//! othercases old_exp:=null
//! endcases;
//! if old_exp<>null then
//!   begin old_exp:=cur_exp; make_exp_copy(old_exp);
//!   end
//!
//! @ @<Declare binary action...@>=
//! function tarnished(@!p:pointer):pointer;
//! label exit;
//! var @!q:pointer; {beginning of the big node}
//! @!r:pointer; {current position in the big node}
//! begin q:=value(p); r:=q+big_node_size[type(p)];
//! repeat r:=r-2;
//! if type(r)=independent then
//!   begin tarnished:=void; return;
//!   end;
//! until r=q;
//! tarnished:=null;
//! exit:end;
//!
//! @ @<Add or subtract the current expression from |p|@>=
//! if (cur_type<pair_type)or(type(p)<pair_type) then
//!   if (cur_type=picture_type)and(type(p)=picture_type) then
//!     begin if c=minus then negate_edges(cur_exp);
//!     cur_edges:=cur_exp; merge_edges(value(p));
//!     end
//!   else bad_binary(p,c)
//! else  if cur_type=pair_type then
//!     if type(p)<>pair_type then bad_binary(p,c)
//!     else  begin q:=value(p); r:=value(cur_exp);
//!       add_or_subtract(x_part_loc(q),x_part_loc(r),c);
//!       add_or_subtract(y_part_loc(q),y_part_loc(r),c);
//!       end
//!   else  if type(p)=pair_type then bad_binary(p,c)
//!     else add_or_subtract(p,null,c)
//!
//! @ The first argument to |add_or_subtract| is the location of a value node
//! in a capsule or pair node that will soon be recycled. The second argument
//! is either a location within a pair or transform node of |cur_exp|,
//! or it is null (which means that |cur_exp| itself should be the second
//! argument).  The third argument is either |plus| or |minus|.
//!
//! The sum or difference of the numeric quantities will replace the second
//! operand.  Arithmetic overflow may go undetected; users aren't supposed to
//! be monkeying around with really big values.
//! @^overflow in arithmetic@>
//!
//! @<Declare binary action...@>=
//! @t\4@>@<Declare the procedure called |dep_finish|@>@;
//! procedure add_or_subtract(@!p,@!q:pointer;@!c:quarterword);
//! label done,exit;
//! var @!s,@!t:small_number; {operand types}
//! @!r:pointer; {list traverser}
//! @!v:integer; {second operand value}
//! begin if q=null then
//!   begin t:=cur_type;
//!   if t<dependent then v:=cur_exp@+else v:=dep_list(cur_exp);
//!   end
//! else  begin t:=type(q);
//!   if t<dependent then v:=value(q)@+else v:=dep_list(q);
//!   end;
//! if t=known then
//!   begin if c=minus then negate(v);
//!   if type(p)=known then
//!     begin v:=slow_add(value(p),v);
//!     if q=null then cur_exp:=v@+else value(q):=v;
//!     return;
//!     end;
//!   @<Add a known value to the constant term of |dep_list(p)|@>;
//!   end
//! else  begin if c=minus then negate_dep_list(v);
//!   @<Add operand |p| to the dependency list |v|@>;
//!   end;
//! exit:end;
//!
//! @ @<Add a known value to the constant term of |dep_list(p)|@>=
//! r:=dep_list(p);
//! while info(r)<>null do r:=link(r);
//! value(r):=slow_add(value(r),v);
//! if q=null then
//!   begin q:=get_node(value_node_size); cur_exp:=q; cur_type:=type(p);
//!   name_type(q):=capsule;
//!   end;
//! dep_list(q):=dep_list(p); type(q):=type(p);
//! prev_dep(q):=prev_dep(p); link(prev_dep(p)):=q;
//! type(p):=known; {this will keep the recycler from collecting non-garbage}
//!
//! @ We prefer |dependent| lists to |proto_dependent| ones, because it is
//! nice to retain the extra accuracy of |fraction| coefficients.
//! But we have to handle both kinds, and mixtures too.
//!
//! @<Add operand |p| to the dependency list |v|@>=
//! if type(p)=known then
//!   @<Add the known |value(p)| to the constant term of |v|@>
//! else  begin s:=type(p); r:=dep_list(p);
//!   if t=dependent then
//!     begin if s=dependent then
//!      if max_coef(r)+max_coef(v)<coef_bound then
//!       begin v:=p_plus_q(v,r,dependent); goto done;
//!       end; {|fix_needed| will necessarily be false}
//!     t:=proto_dependent; v:=p_over_v(v,unity,dependent,proto_dependent);
//!     end;
//!   if s=proto_dependent then v:=p_plus_q(v,r,proto_dependent)
//!   else v:=p_plus_fq(v,unity,r,proto_dependent,dependent);
//!  done:  @<Output the answer, |v| (which might have become |known|)@>;
//!   end
//!
//! @ @<Add the known |value(p)| to the constant term of |v|@>=
//! begin while info(v)<>null do v:=link(v);
//! value(v):=slow_add(value(p),value(v));
//! end
//!
//! @ @<Output the answer, |v| (which might have become |known|)@>=
//! if q<>null then dep_finish(v,q,t)
//! else  begin cur_type:=t; dep_finish(v,null,t);
//!   end
//!
//! @ Here's the current situation: The dependency list |v| of type |t|
//! should either be put into the current expression (if |q=null|) or
//! into location |q| within a pair node (otherwise). The destination (|cur_exp|
//! or |q|) formerly held a dependency list with the same
//! final pointer as the list |v|.
//!
//! @<Declare the procedure called |dep_finish|@>=
//! procedure dep_finish(@!v,@!q:pointer;@!t:small_number);
//! var @!p:pointer; {the destination}
//! @!vv:scaled; {the value, if it is |known|}
//! begin if q=null then p:=cur_exp@+else p:=q;
//! dep_list(p):=v; type(p):=t;
//! if info(v)=null then
//!   begin vv:=value(v);
//!   if q=null then flush_cur_exp(vv)
//!   else  begin recycle_value(p); type(q):=known; value(q):=vv;
//!     end;
//!   end
//! else if q=null then cur_type:=t;
//! if fix_needed then fix_dependencies;
//! end;
//!
//! @ Let's turn now to the six basic relations of comparison.
//!
//! @<Additional cases of binary operators@>=
//! less_than,less_or_equal,greater_than,greater_or_equal,equal_to,unequal_to:
//!   begin@t@>@;
//!   if (cur_type>pair_type)and(type(p)>pair_type) then
//!     add_or_subtract(p,null,minus) {|cur_exp:=(p)-cur_exp|}
//!   else if cur_type<>type(p) then
//!     begin bad_binary(p,c); goto done;
//!     end
//!   else if cur_type=string_type then
//!     flush_cur_exp(str_vs_str(value(p),cur_exp))
//!   else if (cur_type=unknown_string)or(cur_type=unknown_boolean) then
//!     @<Check if unknowns have been equated@>
//!   else if (cur_type=pair_type)or(cur_type=transform_type) then
//!     @<Reduce comparison of big nodes to comparison of scalars@>
//!   else if cur_type=boolean_type then flush_cur_exp(cur_exp-value(p))
//!   else  begin bad_binary(p,c); goto done;
//!     end;
//!   @<Compare the current expression with zero@>;
//! done:  end;
//!
//! @ @<Compare the current expression with zero@>=
//! if cur_type<>known then
//!   begin if cur_type<known then
//!     begin disp_err(p,"");
//!     help1("The quantities shown above have not been equated.")@/
//!     end
//!   else  help2("Oh dear. I can't decide if the expression above is positive,")@/
//!     ("negative, or zero. So this comparison test won't be `true'.");
//!   exp_err("Unknown relation will be considered false");
//! @.Unknown relation...@>
//!   put_get_flush_error(false_code);
//!   end
//! else case c of
//!   less_than: boolean_reset(cur_exp<0);
//!   less_or_equal: boolean_reset(cur_exp<=0);
//!   greater_than: boolean_reset(cur_exp>0);
//!   greater_or_equal: boolean_reset(cur_exp>=0);
//!   equal_to: boolean_reset(cur_exp=0);
//!   unequal_to: boolean_reset(cur_exp<>0);
//!   end; {there are no other cases}
//!  cur_type:=boolean_type
//!
//! @ When two unknown strings are in the same ring, we know that they are
//! equal. Otherwise, we don't know whether they are equal or not, so we
//! make no change.
//!
//! @<Check if unknowns have been equated@>=
//! begin q:=value(cur_exp);
//! while (q<>cur_exp)and(q<>p) do q:=value(q);
//! if q=p then flush_cur_exp(0);
//! end
//!
//! @ @<Reduce comparison of big nodes to comparison of scalars@>=
//! begin q:=value(p); r:=value(cur_exp);
//! rr:=r+big_node_size[cur_type]-2;
//! loop@+  begin add_or_subtract(q,r,minus);
//!   if type(r)<>known then goto done1;
//!   if value(r)<>0 then goto done1;
//!   if r=rr then goto done1;
//!   q:=q+2; r:=r+2;
//!   end;
//! done1:take_part(x_part+half(r-value(cur_exp)));
//! end
//!
//! @ Here we use the sneaky fact that |and_op-false_code=or_op-true_code|.
//!
//! @<Additional cases of binary operators@>=
//! and_op,or_op: if (type(p)<>boolean_type)or(cur_type<>boolean_type) then
//!     bad_binary(p,c)
//!   else if value(p)=c+false_code-and_op then cur_exp:=value(p);
//!
//! @ @<Additional cases of binary operators@>=
//! times: if (cur_type<pair_type)or(type(p)<pair_type) then bad_binary(p,times)
//!   else if (cur_type=known)or(type(p)=known) then
//!     @<Multiply when at least one operand is known@>
//!   else if (nice_pair(p,type(p))and(cur_type>pair_type))
//!       or(nice_pair(cur_exp,cur_type)and(type(p)>pair_type)) then
//!     begin hard_times(p); return;
//!     end
//!   else bad_binary(p,times);
//!
//! @ @<Multiply when at least one operand is known@>=
//! begin if type(p)=known then
//!   begin v:=value(p); free_node(p,value_node_size);
//!   end
//! else  begin v:=cur_exp; unstash_cur_exp(p);
//!   end;
//! if cur_type=known then cur_exp:=take_scaled(cur_exp,v)
//! else if cur_type=pair_type then
//!   begin p:=value(cur_exp);
//!   dep_mult(x_part_loc(p),v,true);
//!   dep_mult(y_part_loc(p),v,true);
//!   end
//! else dep_mult(null,v,true);
//! return;
//! end
//!
//! @ @<Declare binary action...@>=
//! procedure dep_mult(@!p:pointer;@!v:integer;@!v_is_scaled:boolean);
//! label exit;
//! var @!q:pointer; {the dependency list being multiplied by |v|}
//! @!s,@!t:small_number; {its type, before and after}
//! begin if p=null then q:=cur_exp
//! else if type(p)<>known then q:=p
//! else  begin if v_is_scaled then value(p):=take_scaled(value(p),v)
//!   else value(p):=take_fraction(value(p),v);
//!   return;
//!   end;
//! t:=type(q); q:=dep_list(q); s:=t;
//! if t=dependent then if v_is_scaled then
//!   if ab_vs_cd(max_coef(q),abs(v),coef_bound-1,unity)>=0 then t:=proto_dependent;
//! q:=p_times_v(q,v,s,t,v_is_scaled); dep_finish(q,p,t);
//! exit:end;
//!
//! @ Here is a routine that is similar to |times|; but it is invoked only
//! internally, when |v| is a |fraction| whose magnitude is at most~1,
//! and when |cur_type>=pair_type|.
//!
//! @p procedure frac_mult(@!n,@!d:scaled); {multiplies |cur_exp| by |n/d|}
//! var @!p:pointer; {a pair node}
//! @!old_exp:pointer; {a capsule to recycle}
//! @!v:fraction; {|n/d|}
//! begin if internal[tracing_commands]>two then
//!   @<Trace the fraction multiplication@>;
//! case cur_type of
//! transform_type,pair_type:old_exp:=tarnished(cur_exp);
//! independent:old_exp:=void;
//! othercases old_exp:=null
//! endcases;
//! if old_exp<>null then
//!   begin old_exp:=cur_exp; make_exp_copy(old_exp);
//!   end;
//! v:=make_fraction(n,d);
//! if cur_type=known then cur_exp:=take_fraction(cur_exp,v)
//! else if cur_type=pair_type then
//!   begin p:=value(cur_exp);
//!   dep_mult(x_part_loc(p),v,false);
//!   dep_mult(y_part_loc(p),v,false);
//!   end
//! else dep_mult(null,v,false);
//! if old_exp<>null then
//!   begin recycle_value(old_exp); free_node(old_exp,value_node_size);
//!   end
//! end;
//!
//! @ @<Trace the fraction multiplication@>=
//! begin begin_diagnostic; print_nl("{("); print_scaled(n); print_char("/");
//! print_scaled(d); print(")*("); print_exp(null,0); print(")}");
//! end_diagnostic(false);
//! end
//!
//! @ The |hard_times| routine multiplies a nice pair by a dependency list.
//!
//! @<Declare binary action procedures@>=
//! procedure hard_times(@!p:pointer);
//! var @!q:pointer; {a copy of the dependent variable |p|}
//! @!r:pointer; {the big node for the nice pair}
//! @!u,@!v:scaled; {the known values of the nice pair}
//! begin if type(p)=pair_type then
//!   begin q:=stash_cur_exp; unstash_cur_exp(p); p:=q;
//!   end; {now |cur_type=pair_type|}
//! r:=value(cur_exp); u:=value(x_part_loc(r)); v:=value(y_part_loc(r));
//! @<Move the dependent variable |p| into both parts of the pair node |r|@>;
//! dep_mult(x_part_loc(r),u,true); dep_mult(y_part_loc(r),v,true);
//! end;
//!
//! @ @<Move the dependent variable |p|...@>=
//! type(y_part_loc(r)):=type(p);
//! new_dep(y_part_loc(r),copy_dep_list(dep_list(p)));@/
//! type(x_part_loc(r)):=type(p);
//! mem[value_loc(x_part_loc(r))]:=mem[value_loc(p)];
//! link(prev_dep(p)):=x_part_loc(r);
//! free_node(p,value_node_size)
//!
//! @ @<Additional cases of binary operators@>=
//! over: if (cur_type<>known)or(type(p)<pair_type) then bad_binary(p,over)
//!   else  begin v:=cur_exp; unstash_cur_exp(p);
//!     if v=0 then @<Squeal about division by zero@>
//!     else  begin if cur_type=known then cur_exp:=make_scaled(cur_exp,v)
//!       else if cur_type=pair_type then
//!         begin p:=value(cur_exp);
//!         dep_div(x_part_loc(p),v);
//!         dep_div(y_part_loc(p),v);
//!         end
//!       else dep_div(null,v);
//!       end;
//!     return;
//!     end;
//!
//! @ @<Declare binary action...@>=
//! procedure dep_div(@!p:pointer;@!v:scaled);
//! label exit;
//! var @!q:pointer; {the dependency list being divided by |v|}
//! @!s,@!t:small_number; {its type, before and after}
//! begin if p=null then q:=cur_exp
//! else if type(p)<>known then q:=p
//! else  begin value(p):=make_scaled(value(p),v); return;
//!   end;
//! t:=type(q); q:=dep_list(q); s:=t;
//! if t=dependent then
//!   if ab_vs_cd(max_coef(q),unity,coef_bound-1,abs(v))>=0 then t:=proto_dependent;
//! q:=p_over_v(q,v,s,t); dep_finish(q,p,t);
//! exit:end;
//!
//! @ @<Squeal about division by zero@>=
//! begin exp_err("Division by zero");
//! @.Division by zero@>
//! help2("You're trying to divide the quantity shown above the error")@/
//!   ("message by zero. I'm going to divide it by one instead.");
//! put_get_error;
//! end
//!
//! @ @<Additional cases of binary operators@>=
//! pythag_add,pythag_sub: if (cur_type=known)and(type(p)=known) then
//!     if c=pythag_add then cur_exp:=pyth_add(value(p),cur_exp)
//!     else cur_exp:=pyth_sub(value(p),cur_exp)
//!   else bad_binary(p,c);
//!
//! @ The next few sections of the program deal with affine transformations
//! of coordinate data.
//!
//! @<Additional cases of binary operators@>=
//! rotated_by,slanted_by,scaled_by,shifted_by,transformed_by,
//!  x_scaled,y_scaled,z_scaled: @t@>@;@/
//!   if (type(p)=path_type)or(type(p)=future_pen)or(type(p)=pen_type) then
//!     begin path_trans(p,c); return;
//!     end
//!   else if (type(p)=pair_type)or(type(p)=transform_type) then big_trans(p,c)
//!   else if type(p)=picture_type then
//!     begin edges_trans(p,c); return;
//!     end
//!   else bad_binary(p,c);
//!
//! @ Let |c| be one of the eight transform operators. The procedure call
//! |set_up_trans(c)| first changes |cur_exp| to a transform that corresponds to
//! |c| and the original value of |cur_exp|. (In particular, |cur_exp| doesn't
//! change at all if |c=transformed_by|.)
//!
//! Then, if all components of the resulting transform are |known|, they are
//! moved to the global variables |txx|, |txy|, |tyx|, |tyy|, |tx|, |ty|;
//! and |cur_exp| is changed to the known value zero.
//!
//! @<Declare binary action...@>=
//! procedure set_up_trans(@!c:quarterword);
//! label done,exit;
//! var @!p,@!q,@!r:pointer; {list manipulation registers}
//! begin if (c<>transformed_by)or(cur_type<>transform_type) then
//!   @<Put the current transform into |cur_exp|@>;
//! @<If the current transform is entirely known, stash it in global variables;
//!   otherwise |return|@>;
//! exit:end;
//!
//! @ @<Glob...@>=
//! @!txx,@!txy,@!tyx,@!tyy,@!tx,@!ty:scaled; {current transform coefficients}
//!
//! @ @<Put the current transform...@>=
//! begin p:=stash_cur_exp; cur_exp:=id_transform; cur_type:=transform_type;
//! q:=value(cur_exp);
//! case c of
//! @<For each of the eight cases, change the relevant fields of |cur_exp|
//!   and |goto done|;
//!   but do nothing if capsule |p| doesn't have the appropriate type@>@;
//! end; {there are no other cases}
//! disp_err(p,"Improper transformation argument");
//! @.Improper transformation argument@>
//! help3("The expression shown above has the wrong type,")@/
//!   ("so I can't transform anything using it.")@/
//!   ("Proceed, and I'll omit the transformation.");
//! put_get_error;
//! done: recycle_value(p); free_node(p,value_node_size);
//! end
//!
//! @ @<If the current transform is entirely known, ...@>=
//! q:=value(cur_exp); r:=q+transform_node_size;
//! repeat r:=r-2;
//! if type(r)<>known then return;
//! until r=q;
//! txx:=value(xx_part_loc(q));
//! txy:=value(xy_part_loc(q));
//! tyx:=value(yx_part_loc(q));
//! tyy:=value(yy_part_loc(q));
//! tx:=value(x_part_loc(q));
//! ty:=value(y_part_loc(q));
//! flush_cur_exp(0)
//!
//! @ @<For each of the eight cases...@>=
//! rotated_by:if type(p)=known then
//!   @<Install sines and cosines, then |goto done|@>;
//! slanted_by:if type(p)>pair_type then
//!   begin install(xy_part_loc(q),p); goto done;
//!   end;
//! scaled_by:if type(p)>pair_type then
//!   begin install(xx_part_loc(q),p); install(yy_part_loc(q),p); goto done;
//!   end;
//! shifted_by:if type(p)=pair_type then
//!   begin r:=value(p); install(x_part_loc(q),x_part_loc(r));
//!   install(y_part_loc(q),y_part_loc(r)); goto done;
//!   end;
//! x_scaled:if type(p)>pair_type then
//!   begin install(xx_part_loc(q),p); goto done;
//!   end;
//! y_scaled:if type(p)>pair_type then
//!   begin install(yy_part_loc(q),p); goto done;
//!   end;
//! z_scaled:if type(p)=pair_type then
//!   @<Install a complex multiplier, then |goto done|@>;
//! transformed_by:do_nothing;
//!
//! @ @<Install sines and cosines, then |goto done|@>=
//! begin n_sin_cos((value(p) mod three_sixty_units)*16);
//! value(xx_part_loc(q)):=round_fraction(n_cos);
//! value(yx_part_loc(q)):=round_fraction(n_sin);
//! value(xy_part_loc(q)):=-value(yx_part_loc(q));
//! value(yy_part_loc(q)):=value(xx_part_loc(q));
//! goto done;
//! end
//!
//! @ @<Install a complex multiplier, then |goto done|@>=
//! begin r:=value(p);
//! install(xx_part_loc(q),x_part_loc(r));
//! install(yy_part_loc(q),x_part_loc(r));
//! install(yx_part_loc(q),y_part_loc(r));
//! if type(y_part_loc(r))=known then negate(value(y_part_loc(r)))
//! else negate_dep_list(dep_list(y_part_loc(r)));
//! install(xy_part_loc(q),y_part_loc(r));
//! goto done;
//! end
//!
//! @ Procedure |set_up_known_trans| is like |set_up_trans|, but it
//! insists that the transformation be entirely known.
//!
//! @<Declare binary action...@>=
//! procedure set_up_known_trans(@!c:quarterword);
//! begin set_up_trans(c);
//! if cur_type<>known then
//!   begin exp_err("Transform components aren't all known");
//! @.Transform components...@>
//!   help3("I'm unable to apply a partially specified transformation")@/
//!     ("except to a fully known pair or transform.")@/
//!     ("Proceed, and I'll omit the transformation.");
//!   put_get_flush_error(0);
//!   txx:=unity; txy:=0; tyx:=0; tyy:=unity; tx:=0; ty:=0;
//!   end;
//! end;
//!
//! @ Here's a procedure that applies the transform |txx..ty| to a pair of
//! coordinates in locations |p| and~|q|.
//!
//! @<Declare binary action...@>=
//! procedure trans(@!p,@!q:pointer);
//! var @!v:scaled; {the new |x| value}
//! begin v:=take_scaled(mem[p].sc,txx)+take_scaled(mem[q].sc,txy)+tx;
//! mem[q].sc:=take_scaled(mem[p].sc,tyx)+take_scaled(mem[q].sc,tyy)+ty;
//! mem[p].sc:=v;
//! end;
//!
//! @ The simplest transformation procedure applies a transform to all
//! coordinates of a path. The |null_pen| remains unchanged if it isn't
//! being shifted.
//!
//! @<Declare binary action...@>=
//! procedure path_trans(@!p:pointer;@!c:quarterword);
//! label exit;
//! var @!q:pointer; {list traverser}
//! begin set_up_known_trans(c); unstash_cur_exp(p);
//! if cur_type=pen_type then
//!   begin if max_offset(cur_exp)=0 then if tx=0 then if ty=0 then return;
//!   flush_cur_exp(make_path(cur_exp)); cur_type:=future_pen;
//!   end;
//! q:=cur_exp;
//! repeat if left_type(q)<>endpoint then
//!   trans(q+3,q+4); {that's |left_x| and |left_y|}
//! trans(q+1,q+2); {that's |x_coord| and |y_coord|}
//! if right_type(q)<>endpoint then
//!   trans(q+5,q+6); {that's |right_x| and |right_y|}
//! q:=link(q);
//! until q=cur_exp;
//! exit:end;
//!
//! @ The next simplest transformation procedure applies to edges.
//! It is simple primarily because \MF\ doesn't allow very general
//! transformations to be made, and because the tricky subroutines
//! for edge transformation have already been written.
//!
//! @<Declare binary action...@>=
//! procedure edges_trans(@!p:pointer;@!c:quarterword);
//! label exit;
//! begin set_up_known_trans(c); unstash_cur_exp(p); cur_edges:=cur_exp;
//! if empty_edges(cur_edges) then return; {the empty set is easy to transform}
//! if txx=0 then if tyy=0 then
//!  if txy mod unity=0 then if tyx mod unity=0 then
//!   begin xy_swap_edges; txx:=txy; tyy:=tyx; txy:=0; tyx:=0;
//!   if empty_edges(cur_edges) then return;
//!   end;
//! if txy=0 then if tyx=0 then
//!  if txx mod unity=0 then if tyy mod unity=0 then
//!   @<Scale the edges, shift them, and |return|@>;
//! print_err("That transformation is too hard");
//! @.That transformation...@>
//! help3("I can apply complicated transformations to paths,")@/
//!   ("but I can only do integer operations on pictures.")@/
//!   ("Proceed, and I'll omit the transformation.");
//! put_get_error;
//! exit:end;
//!
//! @ @<Scale the edges, shift them, and |return|@>=
//! begin if (txx=0)or(tyy=0) then
//!   begin toss_edges(cur_edges);
//!   cur_exp:=get_node(edge_header_size); init_edges(cur_exp);
//!   end
//! else  begin if txx<0 then
//!     begin x_reflect_edges; txx:=-txx;
//!     end;
//!   if tyy<0 then
//!     begin y_reflect_edges; tyy:=-tyy;
//!     end;
//!   if txx<>unity then x_scale_edges(txx div unity);
//!   if tyy<>unity then y_scale_edges(tyy div unity);
//!   @<Shift the edges by |(tx,ty)|, rounded@>;
//!   end;
//! return;
//! end
//!
//! @ @<Shift the edges...@>=
//! tx:=round_unscaled(tx); ty:=round_unscaled(ty);
//! if (m_min(cur_edges)+tx<=0)or(m_max(cur_edges)+tx>=8192)or@|
//!  (n_min(cur_edges)+ty<=0)or(n_max(cur_edges)+ty>=8191)or@|
//!  (abs(tx)>=4096)or(abs(ty)>=4096) then
//!   begin print_err("Too far to shift");
//! @.Too far to shift@>
//!   help3("I can't shift the picture as requested---it would")@/
//!     ("make some coordinates too large or too small.")@/
//!     ("Proceed, and I'll omit the transformation.");
//!   put_get_error;
//!   end
//! else  begin if tx<>0 then
//!     begin if not valid_range(m_offset(cur_edges)-tx) then fix_offset;
//!     m_min(cur_edges):=m_min(cur_edges)+tx;
//!     m_max(cur_edges):=m_max(cur_edges)+tx;
//!     m_offset(cur_edges):=m_offset(cur_edges)-tx;
//!     last_window_time(cur_edges):=0;
//!     end;
//!   if ty<>0 then
//!     begin n_min(cur_edges):=n_min(cur_edges)+ty;
//!     n_max(cur_edges):=n_max(cur_edges)+ty;
//!     n_pos(cur_edges):=n_pos(cur_edges)+ty;
//!     last_window_time(cur_edges):=0;
//!     end;
//!   end
//!
//! @ The hard cases of transformation occur when big nodes are involved,
//! and when some of their components are unknown.
//!
//! @<Declare binary action...@>=
//! @t\4@>@<Declare subroutines needed by |big_trans|@>@;
//! procedure big_trans(@!p:pointer;@!c:quarterword);
//! label exit;
//! var @!q,@!r,@!pp,@!qq:pointer; {list manipulation registers}
//! @!s:small_number; {size of a big node}
//! begin s:=big_node_size[type(p)]; q:=value(p); r:=q+s;
//! repeat r:=r-2;
//! if type(r)<>known then @<Transform an unknown big node and |return|@>;
//! until r=q;
//! @<Transform a known big node@>;
//! exit:end; {node |p| will now be recycled by |do_binary|}
//!
//! @ @<Transform an unknown big node and |return|@>=
//! begin set_up_known_trans(c); make_exp_copy(p); r:=value(cur_exp);
//! if cur_type=transform_type then
//!   begin bilin1(yy_part_loc(r),tyy,xy_part_loc(q),tyx,0);
//!   bilin1(yx_part_loc(r),tyy,xx_part_loc(q),tyx,0);
//!   bilin1(xy_part_loc(r),txx,yy_part_loc(q),txy,0);
//!   bilin1(xx_part_loc(r),txx,yx_part_loc(q),txy,0);
//!   end;
//! bilin1(y_part_loc(r),tyy,x_part_loc(q),tyx,ty);
//! bilin1(x_part_loc(r),txx,y_part_loc(q),txy,tx);
//! return;
//! end
//!
//! @ Let |p| point to a two-word value field inside a big node of |cur_exp|,
//! and let |q| point to a another value field. The |bilin1| procedure
//! replaces |p| by $p\cdot t+q\cdot u+\delta$.
//!
//! @<Declare subroutines needed by |big_trans|@>=
//! procedure bilin1(@!p:pointer;@!t:scaled;@!q:pointer;@!u,@!delta:scaled);
//! var @!r:pointer; {list traverser}
//! begin if t<>unity then dep_mult(p,t,true);
//! if u<>0 then
//!   if type(q)=known then delta:=delta+take_scaled(value(q),u)
//!   else  begin @<Ensure that |type(p)=proto_dependent|@>;
//!     dep_list(p):=p_plus_fq(dep_list(p),u,dep_list(q),proto_dependent,type(q));
//!     end;
//! if type(p)=known then value(p):=value(p)+delta
//! else  begin r:=dep_list(p);
//!   while info(r)<>null do r:=link(r);
//!   delta:=value(r)+delta;
//!   if r<>dep_list(p) then value(r):=delta
//!   else  begin recycle_value(p); type(p):=known; value(p):=delta;
//!     end;
//!   end;
//! if fix_needed then fix_dependencies;
//! end;
//!
//! @ @<Ensure that |type(p)=proto_dependent|@>=
//! if type(p)<>proto_dependent then
//!   begin if type(p)=known then new_dep(p,const_dependency(value(p)))
//!   else dep_list(p):=p_times_v(dep_list(p),unity,dependent,proto_dependent,true);
//!   type(p):=proto_dependent;
//!   end
//!
//! @ @<Transform a known big node@>=
//! set_up_trans(c);
//! if cur_type=known then @<Transform known by known@>
//! else  begin pp:=stash_cur_exp; qq:=value(pp);
//!   make_exp_copy(p); r:=value(cur_exp);
//!   if cur_type=transform_type then
//!     begin bilin2(yy_part_loc(r),yy_part_loc(qq),
//!       value(xy_part_loc(q)),yx_part_loc(qq),null);
//!     bilin2(yx_part_loc(r),yy_part_loc(qq),
//!       value(xx_part_loc(q)),yx_part_loc(qq),null);
//!     bilin2(xy_part_loc(r),xx_part_loc(qq),
//!       value(yy_part_loc(q)),xy_part_loc(qq),null);
//!     bilin2(xx_part_loc(r),xx_part_loc(qq),
//!       value(yx_part_loc(q)),xy_part_loc(qq),null);
//!     end;
//!   bilin2(y_part_loc(r),yy_part_loc(qq),
//!     value(x_part_loc(q)),yx_part_loc(qq),y_part_loc(qq));
//!   bilin2(x_part_loc(r),xx_part_loc(qq),
//!     value(y_part_loc(q)),xy_part_loc(qq),x_part_loc(qq));
//!   recycle_value(pp); free_node(pp,value_node_size);
//!   end;
//!
//! @ Let |p| be a |proto_dependent| value whose dependency list ends
//! at |dep_final|. The following procedure adds |v| times another
//! numeric quantity to~|p|.
//!
//! @<Declare subroutines needed by |big_trans|@>=
//! procedure add_mult_dep(@!p:pointer;@!v:scaled;@!r:pointer);
//! begin if type(r)=known then
//!   value(dep_final):=value(dep_final)+take_scaled(value(r),v)
//! else  begin dep_list(p):=
//!    p_plus_fq(dep_list(p),v,dep_list(r),proto_dependent,type(r));
//!   if fix_needed then fix_dependencies;
//!   end;
//! end;
//!
//! @ The |bilin2| procedure is something like |bilin1|, but with known
//! and unknown quantities reversed. Parameter |p| points to a value field
//! within the big node for |cur_exp|; and |type(p)=known|. Parameters
//! |t| and~|u| point to value fields elsewhere; so does parameter~|q|,
//! unless it is |null| (which stands for zero). Location~|p| will be
//! replaced by $p\cdot t+v\cdot u+q$.
//!
//! @<Declare subroutines needed by |big_trans|@>=
//! procedure bilin2(@!p,@!t:pointer;@!v:scaled;@!u,@!q:pointer);
//! var @!vv:scaled; {temporary storage for |value(p)|}
//! begin vv:=value(p); type(p):=proto_dependent;
//! new_dep(p,const_dependency(0)); {this sets |dep_final|}
//! if vv<>0 then add_mult_dep(p,vv,t); {|dep_final| doesn't change}
//! if v<>0 then add_mult_dep(p,v,u);
//! if q<>null then add_mult_dep(p,unity,q);
//! if dep_list(p)=dep_final then
//!   begin vv:=value(dep_final); recycle_value(p);
//!   type(p):=known; value(p):=vv;
//!   end;
//! end;
//!
//! @ @<Transform known by known@>=
//! begin make_exp_copy(p); r:=value(cur_exp);
//! if cur_type=transform_type then
//!   begin bilin3(yy_part_loc(r),tyy,value(xy_part_loc(q)),tyx,0);
//!   bilin3(yx_part_loc(r),tyy,value(xx_part_loc(q)),tyx,0);
//!   bilin3(xy_part_loc(r),txx,value(yy_part_loc(q)),txy,0);
//!   bilin3(xx_part_loc(r),txx,value(yx_part_loc(q)),txy,0);
//!   end;
//! bilin3(y_part_loc(r),tyy,value(x_part_loc(q)),tyx,ty);
//! bilin3(x_part_loc(r),txx,value(y_part_loc(q)),txy,tx);
//! end
//!
//! @ Finally, in |bilin3| everything is |known|.
//!
//! @<Declare subroutines needed by |big_trans|@>=
//! procedure bilin3(@!p:pointer;@!t,@!v,@!u,@!delta:scaled);
//! begin if t<>unity then delta:=delta+take_scaled(value(p),t)
//! else delta:=delta+value(p);
//! if u<>0 then value(p):=delta+take_scaled(v,u)
//! else value(p):=delta;
//! end;
//!
//! @ @<Additional cases of binary operators@>=
//! concatenate: if (cur_type=string_type)and(type(p)=string_type) then cat(p)
//!   else bad_binary(p,concatenate);
//! substring_of: if nice_pair(p,type(p))and(cur_type=string_type) then
//!     chop_string(value(p))
//!   else bad_binary(p,substring_of);
//! subpath_of: begin if cur_type=pair_type then pair_to_path;
//!   if nice_pair(p,type(p))and(cur_type=path_type) then
//!     chop_path(value(p))
//!   else bad_binary(p,subpath_of);
//!   end;
//!
//! @ @<Declare binary action...@>=
//! procedure cat(@!p:pointer);
//! var @!a,@!b:str_number; {the strings being concatenated}
//! @!k:pool_pointer; {index into |str_pool|}
//! begin a:=value(p); b:=cur_exp; str_room(length(a)+length(b));
//! for k:=str_start[a] to str_start[a+1]-1 do append_char(so(str_pool[k]));
//! for k:=str_start[b] to str_start[b+1]-1 do append_char(so(str_pool[k]));
//! cur_exp:=make_string; delete_str_ref(b);
//! end;
//!
//! @ @<Declare binary action...@>=
//! procedure chop_string(@!p:pointer);
//! var @!a,@!b:integer; {start and stop points}
//! @!l:integer; {length of the original string}
//! @!k:integer; {runs from |a| to |b|}
//! @!s:str_number; {the original string}
//! @!reversed:boolean; {was |a>b|?}
//! begin a:=round_unscaled(value(x_part_loc(p)));
//! b:=round_unscaled(value(y_part_loc(p)));
//! if a<=b then reversed:=false
//! else  begin reversed:=true; k:=a; a:=b; b:=k;
//!   end;
//! s:=cur_exp; l:=length(s);
//! if a<0 then
//!   begin a:=0;
//!   if b<0 then b:=0;
//!   end;
//! if b>l then
//!   begin b:=l;
//!   if a>l then a:=l;
//!   end;
//! str_room(b-a);
//! if reversed then
//!   for k:=str_start[s]+b-1 downto str_start[s]+a do append_char(so(str_pool[k]))
//! else for k:=str_start[s]+a to str_start[s]+b-1 do append_char(so(str_pool[k]));
//! cur_exp:=make_string; delete_str_ref(s);
//! end;
//!
//! @ @<Declare binary action...@>=
//! procedure chop_path(@!p:pointer);
//! var @!q:pointer; {a knot in the original path}
//! @!pp,@!qq,@!rr,@!ss:pointer; {link variables for copies of path nodes}
//! @!a,@!b,@!k,@!l:scaled; {indices for chopping}
//! @!reversed:boolean; {was |a>b|?}
//! begin l:=path_length; a:=value(x_part_loc(p)); b:=value(y_part_loc(p));
//! if a<=b then reversed:=false
//! else  begin reversed:=true; k:=a; a:=b; b:=k;
//!   end;
//! @<Dispense with the cases |a<0| and/or |b>l|@>;
//! q:=cur_exp;
//! while a>=unity do
//!   begin q:=link(q); a:=a-unity; b:=b-unity;
//!   end;
//! if b=a then @<Construct a path from |pp| to |qq| of length zero@>
//! else @<Construct a path from |pp| to |qq| of length $\lceil b\rceil$@>;
//! left_type(pp):=endpoint; right_type(qq):=endpoint; link(qq):=pp;
//! toss_knot_list(cur_exp);
//! if reversed then
//!   begin cur_exp:=link(htap_ypoc(pp)); toss_knot_list(pp);
//!   end
//! else cur_exp:=pp;
//! end;
//!
//! @ @<Dispense with the cases |a<0| and/or |b>l|@>=
//! if a<0 then
//!   if left_type(cur_exp)=endpoint then
//!     begin a:=0; if b<0 then b:=0;
//!     end
//!   else  repeat a:=a+l; b:=b+l;
//!     until a>=0; {a cycle always has length |l>0|}
//! if b>l then if left_type(cur_exp)=endpoint then
//!     begin b:=l; if a>l then a:=l;
//!     end
//!   else while a>=l do
//!     begin a:=a-l; b:=b-l;
//!     end
//!
//! @ @<Construct a path from |pp| to |qq| of length $\lceil b\rceil$@>=
//! begin pp:=copy_knot(q); qq:=pp;
//! repeat q:=link(q); rr:=qq; qq:=copy_knot(q); link(rr):=qq; b:=b-unity;
//! until b<=0;
//! if a>0 then
//!   begin ss:=pp; pp:=link(pp);
//!   split_cubic(ss,a*@'10000,x_coord(pp),y_coord(pp)); pp:=link(ss);
//!   free_node(ss,knot_node_size);
//!   if rr=ss then
//!     begin b:=make_scaled(b,unity-a); rr:=pp;
//!     end;
//!   end;
//! if b<0 then
//!   begin split_cubic(rr,(b+unity)*@'10000,x_coord(qq),y_coord(qq));
//!   free_node(qq,knot_node_size);
//!   qq:=link(rr);
//!   end;
//! end
//!
//! @ @<Construct a path from |pp| to |qq| of length zero@>=
//! begin if a>0 then
//!   begin qq:=link(q);
//!   split_cubic(q,a*@'10000,x_coord(qq),y_coord(qq)); q:=link(q);
//!   end;
//! pp:=copy_knot(q); qq:=pp;
//! end
//!
//! @ The |pair_value| routine changes the current expression to a
//! given ordered pair of values.
//!
//! @<Declare binary action...@>=
//! procedure pair_value(@!x,@!y:scaled);
//! var @!p:pointer; {a pair node}
//! begin p:=get_node(value_node_size); flush_cur_exp(p); cur_type:=pair_type;
//! type(p):=pair_type; name_type(p):=capsule; init_big_node(p);
//! p:=value(p);@/
//! type(x_part_loc(p)):=known; value(x_part_loc(p)):=x;@/
//! type(y_part_loc(p)):=known; value(y_part_loc(p)):=y;@/
//! end;
//!
//! @ @<Additional cases of binary operators@>=
//! point_of,precontrol_of,postcontrol_of: begin if cur_type=pair_type then
//!      pair_to_path;
//!   if (cur_type=path_type)and(type(p)=known) then
//!     find_point(value(p),c)
//!   else bad_binary(p,c);
//!   end;
//! pen_offset_of: begin if cur_type=future_pen then materialize_pen;
//!   if (cur_type=pen_type)and nice_pair(p,type(p)) then
//!     set_up_offset(value(p))
//!   else bad_binary(p,pen_offset_of);
//!   end;
//! direction_time_of: begin if cur_type=pair_type then pair_to_path;
//!   if (cur_type=path_type)and nice_pair(p,type(p)) then
//!     set_up_direction_time(value(p))
//!   else bad_binary(p,direction_time_of);
//!   end;
//!
//! @ @<Declare binary action...@>=
//! procedure set_up_offset(@!p:pointer);
//! begin find_offset(value(x_part_loc(p)),value(y_part_loc(p)),cur_exp);
//! pair_value(cur_x,cur_y);
//! end;
//! @#
//! procedure set_up_direction_time(@!p:pointer);
//! begin flush_cur_exp(find_direction_time(value(x_part_loc(p)),
//!   value(y_part_loc(p)),cur_exp));
//! end;
//!
//! @ @<Declare binary action...@>=
//! procedure find_point(@!v:scaled;@!c:quarterword);
//! var @!p:pointer; {the path}
//! @!n:scaled; {its length}
//! @!q:pointer; {successor of |p|}
//! begin p:=cur_exp;@/
//! if left_type(p)=endpoint then n:=-unity@+else n:=0;
//! repeat p:=link(p); n:=n+unity;
//! until p=cur_exp;
//! if n=0 then v:=0
//! else if v<0 then
//!   if left_type(p)=endpoint then v:=0
//!   else v:=n-1-((-v-1) mod n)
//! else if v>n then
//!   if left_type(p)=endpoint then v:=n
//!   else v:=v mod n;
//! p:=cur_exp;
//! while v>=unity do
//!   begin p:=link(p); v:=v-unity;
//!   end;
//! if v<>0 then @<Insert a fractional node by splitting the cubic@>;
//! @<Set the current expression to the desired path coordinates@>;
//! end;
//!
//! @ @<Insert a fractional node...@>=
//! begin q:=link(p); split_cubic(p,v*@'10000,x_coord(q),y_coord(q)); p:=link(p);
//! end
//!
//! @ @<Set the current expression to the desired path coordinates...@>=
//! case c of
//! point_of: pair_value(x_coord(p),y_coord(p));
//! precontrol_of: if left_type(p)=endpoint then pair_value(x_coord(p),y_coord(p))
//!   else pair_value(left_x(p),left_y(p));
//! postcontrol_of: if right_type(p)=endpoint then pair_value(x_coord(p),y_coord(p))
//!   else pair_value(right_x(p),right_y(p));
//! end {there are no other cases}
//!
//! @ @<Additional cases of bin...@>=
//! intersect: begin if type(p)=pair_type then
//!     begin q:=stash_cur_exp; unstash_cur_exp(p);
//!     pair_to_path; p:=stash_cur_exp; unstash_cur_exp(q);
//!     end;
//!   if cur_type=pair_type then pair_to_path;
//!   if (cur_type=path_type)and(type(p)=path_type) then
//!     begin path_intersection(value(p),cur_exp);
//!     pair_value(cur_t,cur_tt);
//!     end
//!   else bad_binary(p,intersect);
//!   end;
//!
//! @* \[43] Statements and commands.
//! The chief executive of \MF\ is the |do_statement| routine, which
//! contains the master switch that causes all the various pieces of \MF\
//! to do their things, in the right order.
//!
//! In a sense, this is the grand climax of the program: It applies all the
//! tools that we have worked so hard to construct. In another sense, this is
//! the messiest part of the program: It necessarily refers to other pieces
//! of code all over the place, so that a person can't fully understand what is
//! going on without paging back and forth to be reminded of conventions that
//! are defined elsewhere. We are now at the hub of the web.
//!
//! The structure of |do_statement| itself is quite simple.  The first token
//! of the statement is fetched using |get_x_next|.  If it can be the first
//! token of an expression, we look for an equation, an assignment, or a
//! title. Otherwise we use a \&{case} construction to branch at high speed to
//! the appropriate routine for various and sundry other types of commands,
//! each of which has an ``action procedure'' that does the necessary work.
//!
//! The program uses the fact that
//! $$\hbox{|min_primary_command=max_statement_command=type_name|}$$
//! to interpret a statement that starts with, e.g., `\&{string}',
//! as a type declaration rather than a boolean expression.
//!
//! @p @t\4@>@<Declare generic font output procedures@>@;
//! @t\4@>@<Declare action procedures for use by |do_statement|@>@;
//! procedure do_statement; {governs \MF's activities}
//! begin cur_type:=vacuous; get_x_next;
//! if cur_cmd>max_primary_command then @<Worry about bad statement@>
//! else if cur_cmd>max_statement_command then
//!   @<Do an equation, assignment, title, or
//!    `$\langle\,$expression$\,\rangle\,$\&{endgroup}'@>
//! else @<Do a statement that doesn't begin with an expression@>;
//! if cur_cmd<semicolon then
//!   @<Flush unparsable junk that was found after the statement@>;
//! error_count:=0;
//! end;
//!
//! @ The only command codes |>max_primary_command| that can be present
//! at the beginning of a statement are |semicolon| and higher; these
//! occur when the statement is null.
//!
//! @<Worry about bad statement@>=
//! begin if cur_cmd<semicolon then
//!   begin print_err("A statement can't begin with `");
//! @.A statement can't begin with x@>
//!   print_cmd_mod(cur_cmd,cur_mod); print_char("'");
//!   help5("I was looking for the beginning of a new statement.")@/
//!     ("If you just proceed without changing anything, I'll ignore")@/
//!     ("everything up to the next `;'. Please insert a semicolon")@/
//!     ("now in front of anything that you don't want me to delete.")@/
//!     ("(See Chapter 27 of The METAFONTbook for an example.)");@/
//! @:METAFONTbook}{\sl The {\logos METAFONT\/}book@>
//!   back_error; get_x_next;
//!   end;
//! end
//!
//! @ The help message printed here says that everything is flushed up to
//! a semicolon, but actually the commands |end_group| and |stop| will
//! also terminate a statement.
//!
//! @<Flush unparsable junk that was found after the statement@>=
//! begin print_err("Extra tokens will be flushed");
//! @.Extra tokens will be flushed@>
//! help6("I've just read as much of that statement as I could fathom,")@/
//! ("so a semicolon should have been next. It's very puzzling...")@/
//! ("but I'll try to get myself back together, by ignoring")@/
//! ("everything up to the next `;'. Please insert a semicolon")@/
//! ("now in front of anything that you don't want me to delete.")@/
//! ("(See Chapter 27 of The METAFONTbook for an example.)");@/
//! @:METAFONTbook}{\sl The {\logos METAFONT\/}book@>
//! back_error; scanner_status:=flushing;
//! repeat get_next;
//! @<Decrease the string reference count...@>;
//! until end_of_statement; {|cur_cmd=semicolon|, |end_group|, or |stop|}
//! scanner_status:=normal;
//! end
//!
//! @ If |do_statement| ends with |cur_cmd=end_group|, we should have
//! |cur_type=vacuous| unless the statement was simply an expression;
//! in the latter case, |cur_type| and |cur_exp| should represent that
//! expression.
//!
//! @<Do a statement that doesn't...@>=
//! begin if internal[tracing_commands]>0 then show_cur_cmd_mod;
//! case cur_cmd of
//! type_name:do_type_declaration;
//! macro_def:if cur_mod>var_def then make_op_def
//!   else if cur_mod>end_def then scan_def;
//! @t\4@>@<Cases of |do_statement| that invoke particular commands@>@;
//! end; {there are no other cases}
//! cur_type:=vacuous;
//! end
//!
//! @ The most important statements begin with expressions.
//!
//! @<Do an equation, assignment, title, or...@>=
//! begin var_flag:=assignment; scan_expression;
//! if cur_cmd<end_group then
//!   begin if cur_cmd=equals then do_equation
//!   else if cur_cmd=assignment then do_assignment
//!   else if cur_type=string_type then @<Do a title@>
//!   else if cur_type<>vacuous then
//!     begin exp_err("Isolated expression");
//! @.Isolated expression@>
//!     help3("I couldn't find an `=' or `:=' after the")@/
//!       ("expression that is shown above this error message,")@/
//!       ("so I guess I'll just ignore it and carry on.");
//!     put_get_error;
//!     end;
//!   flush_cur_exp(0); cur_type:=vacuous;
//!   end;
//! end
//!
//! @ @<Do a title@>=
//! begin if internal[tracing_titles]>0 then
//!   begin print_nl(""); slow_print(cur_exp); update_terminal;
//!   end;
//! if internal[proofing]>0 then
//!   @<Send the current expression as a title to the output file@>;
//! end
//!
//! @ Equations and assignments are performed by the pair of mutually recursive
//! @^recursion@>
//! routines |do_equation| and |do_assignment|. These routines are called when
//! |cur_cmd=equals| and when |cur_cmd=assignment|, respectively; the left-hand
//! side is in |cur_type| and |cur_exp|, while the right-hand side is yet
//! to be scanned. After the routines are finished, |cur_type| and |cur_exp|
//! will be equal to the right-hand side (which will normally be equal
//! to the left-hand side).
//!
//! @<Declare action procedures for use by |do_statement|@>=
//! @t\4@>@<Declare the procedure called |try_eq|@>@;
//! @t\4@>@<Declare the procedure called |make_eq|@>@;
//! procedure@?do_assignment; forward;@t\2@>@/
//! procedure do_equation;
//! var @!lhs:pointer; {capsule for the left-hand side}
//! @!p:pointer; {temporary register}
//! begin lhs:=stash_cur_exp; get_x_next; var_flag:=assignment; scan_expression;
//! if cur_cmd=equals then do_equation
//! else if cur_cmd=assignment then do_assignment;
//! if internal[tracing_commands]>two then @<Trace the current equation@>;
//! if cur_type=unknown_path then if type(lhs)=pair_type then
//!   begin p:=stash_cur_exp; unstash_cur_exp(lhs); lhs:=p;
//!   end; {in this case |make_eq| will change the pair to a path}
//! make_eq(lhs); {equate |lhs| to |(cur_type,cur_exp)|}
//! end;
//!
//! @ And |do_assignment| is similar to |do_equation|:
//!
//! @<Declare action procedures for use by |do_statement|@>=
//! procedure do_assignment;
//! var @!lhs:pointer; {token list for the left-hand side}
//! @!p:pointer; {where the left-hand value is stored}
//! @!q:pointer; {temporary capsule for the right-hand value}
//! begin if cur_type<>token_list then
//!   begin exp_err("Improper `:=' will be changed to `='");
//! @.Improper `:='@>
//!   help2("I didn't find a variable name at the left of the `:=',")@/
//!     ("so I'm going to pretend that you said `=' instead.");@/
//!   error; do_equation;
//!   end
//! else  begin lhs:=cur_exp; cur_type:=vacuous;@/
//!   get_x_next; var_flag:=assignment; scan_expression;
//!   if cur_cmd=equals then do_equation
//!   else if cur_cmd=assignment then do_assignment;
//!   if internal[tracing_commands]>two then @<Trace the current assignment@>;
//!   if info(lhs)>hash_end then
//!     @<Assign the current expression to an internal variable@>
//!   else @<Assign the current expression to the variable |lhs|@>;
//!   flush_node_list(lhs);
//!   end;
//! end;
//!
//! @ @<Trace the current equation@>=
//! begin begin_diagnostic; print_nl("{("); print_exp(lhs,0);
//! print(")=("); print_exp(null,0); print(")}"); end_diagnostic(false);
//! end
//!
//! @ @<Trace the current assignment@>=
//! begin begin_diagnostic; print_nl("{");
//! if info(lhs)>hash_end then slow_print(int_name[info(lhs)-(hash_end)])
//! else show_token_list(lhs,null,1000,0);
//! print(":="); print_exp(null,0); print_char("}"); end_diagnostic(false);
//! end
//!
//! @ @<Assign the current expression to an internal variable@>=
//! if cur_type=known then internal[info(lhs)-(hash_end)]:=cur_exp
//! else  begin exp_err("Internal quantity `");
//! @.Internal quantity...@>
//!   slow_print(int_name[info(lhs)-(hash_end)]);
//!   print("' must receive a known value");
//!   help2("I can't set an internal quantity to anything but a known")@/
//!     ("numeric value, so I'll have to ignore this assignment.");
//!   put_get_error;
//!   end
//!
//! @ @<Assign the current expression to the variable |lhs|@>=
//! begin p:=find_variable(lhs);
//! if p<>null then
//!   begin q:=stash_cur_exp; cur_type:=und_type(p); recycle_value(p);
//!   type(p):=cur_type; value(p):=null; make_exp_copy(p);
//!   p:=stash_cur_exp; unstash_cur_exp(q); make_eq(p);
//!   end
//! else  begin obliterated(lhs); put_get_error;
//!   end;
//! end
//!
//!
//! @ And now we get to the nitty-gritty. The |make_eq| procedure is given
//! a pointer to a capsule that is to be equated to the current expression.
//!
//! @<Declare the procedure called |make_eq|@>=
//! procedure make_eq(@!lhs:pointer);
//! label restart,done, not_found;
//! var @!t:small_number; {type of the left-hand side}
//! @!v:integer; {value of the left-hand side}
//! @!p,@!q:pointer; {pointers inside of big nodes}
//! begin restart: t:=type(lhs);
//! if t<=pair_type then v:=value(lhs);
//! case t of
//! @t\4@>@<For each type |t|, make an equation and |goto done| unless |cur_type|
//!   is incompatible with~|t|@>@;
//! end; {all cases have been listed}
//! @<Announce that the equation cannot be performed@>;
//! done:check_arith; recycle_value(lhs); free_node(lhs,value_node_size);
//! end;
//!
//! @ @<Announce that the equation cannot be performed@>=
//! disp_err(lhs,""); exp_err("Equation cannot be performed (");
//! @.Equation cannot be performed@>
//! if type(lhs)<=pair_type then print_type(type(lhs))@+else print("numeric");
//! print_char("=");
//! if cur_type<=pair_type then print_type(cur_type)@+else print("numeric");
//! print_char(")");@/
//! help2("I'm sorry, but I don't know how to make such things equal.")@/
//!   ("(See the two expressions just above the error message.)");
//! put_get_error
//!
//! @ @<For each type |t|, make an equation and |goto done| unless...@>=
//! boolean_type,string_type,pen_type,path_type,picture_type:
//!   if cur_type=t+unknown_tag then
//!     begin nonlinear_eq(v,cur_exp,false); unstash_cur_exp(cur_exp); goto done;
//!     end
//!   else if cur_type=t then
//!     @<Report redundant or inconsistent equation and |goto done|@>;
//! unknown_types:if cur_type=t-unknown_tag then
//!     begin nonlinear_eq(cur_exp,lhs,true); goto done;
//!     end
//!   else if cur_type=t then
//!     begin ring_merge(lhs,cur_exp); goto done;
//!     end
//!   else if cur_type=pair_type then if t=unknown_path then
//!     begin pair_to_path; goto restart;
//!     end;
//! transform_type,pair_type:if cur_type=t then
//!     @<Do multiple equations and |goto done|@>;
//! known,dependent,proto_dependent,independent:if cur_type>=known then
//!     begin try_eq(lhs,null); goto done;
//!     end;
//! vacuous:do_nothing;
//!
//! @ @<Report redundant or inconsistent equation and |goto done|@>=
//! begin if cur_type<=string_type then
//!   begin if cur_type=string_type then
//!     begin if str_vs_str(v,cur_exp)<>0 then goto not_found;
//!     end
//!   else if v<>cur_exp then goto not_found;
//!   @<Exclaim about a redundant equation@>; goto done;
//!   end;
//! print_err("Redundant or inconsistent equation");
//! @.Redundant or inconsistent equation@>
//! help2("An equation between already-known quantities can't help.")@/
//!   ("But don't worry; continue and I'll just ignore it.");
//! put_get_error; goto done;
//! not_found: print_err("Inconsistent equation");
//! @.Inconsistent equation@>
//! help2("The equation I just read contradicts what was said before.")@/
//!   ("But don't worry; continue and I'll just ignore it.");
//! put_get_error; goto done;
//! end
//!
//! @ @<Do multiple equations and |goto done|@>=
//! begin p:=v+big_node_size[t]; q:=value(cur_exp)+big_node_size[t];
//! repeat p:=p-2; q:=q-2; try_eq(p,q);
//! until p=v;
//! goto done;
//! end
//!
//! @ The first argument to |try_eq| is the location of a value node
//! in a capsule that will soon be recycled. The second argument is
//! either a location within a pair or transform node pointed to by
//! |cur_exp|, or it is |null| (which means that |cur_exp| itself
//! serves as the second argument). The idea is to leave |cur_exp| unchanged,
//! but to equate the two operands.
//!
//! @<Declare the procedure called |try_eq|@>=
//! procedure try_eq(@!l,@!r:pointer);
//! label done,done1;
//! var @!p:pointer; {dependency list for right operand minus left operand}
//! @!t:known..independent; {the type of list |p|}
//! @!q:pointer; {the constant term of |p| is here}
//! @!pp:pointer; {dependency list for right operand}
//! @!tt:dependent..independent; {the type of list |pp|}
//! @!copied:boolean; {have we copied a list that ought to be recycled?}
//! begin @<Remove the left operand from its container, negate it, and
//!   put it into dependency list~|p| with constant term~|q|@>;
//! @<Add the right operand to list |p|@>;
//! if info(p)=null then @<Deal with redundant or inconsistent equation@>
//! else  begin linear_eq(p,t);
//!   if r=null then if cur_type<>known then if type(cur_exp)=known then
//!     begin pp:=cur_exp; cur_exp:=value(cur_exp); cur_type:=known;
//!     free_node(pp,value_node_size);
//!     end;
//!   end;
//! end;
//!
//! @ @<Remove the left operand from its container, negate it, and...@>=
//! t:=type(l);
//! if t=known then
//!   begin t:=dependent; p:=const_dependency(-value(l)); q:=p;
//!   end
//! else if t=independent then
//!   begin t:=dependent; p:=single_dependency(l); negate(value(p));
//!   q:=dep_final;
//!   end
//! else  begin p:=dep_list(l); q:=p;
//!   loop@+  begin negate(value(q));
//!     if info(q)=null then goto done;
//!     q:=link(q);
//!     end;
//!  done:  link(prev_dep(l)):=link(q); prev_dep(link(q)):=prev_dep(l);
//!   type(l):=known;
//!   end
//!
//! @ @<Deal with redundant or inconsistent equation@>=
//! begin if abs(value(p))>64 then {off by .001 or more}
//!   begin print_err("Inconsistent equation");@/
//! @.Inconsistent equation@>
//!   print(" (off by "); print_scaled(value(p)); print_char(")");
//!   help2("The equation I just read contradicts what was said before.")@/
//!     ("But don't worry; continue and I'll just ignore it.");
//!   put_get_error;
//!   end
//! else if r=null then @<Exclaim about a redundant equation@>;
//! free_node(p,dep_node_size);
//! end
//!
//! @ @<Add the right operand to list |p|@>=
//! if r=null then
//!   if cur_type=known then
//!     begin value(q):=value(q)+cur_exp; goto done1;
//!     end
//!   else  begin tt:=cur_type;
//!     if tt=independent then pp:=single_dependency(cur_exp)
//!     else pp:=dep_list(cur_exp);
//!     end
//! else  if type(r)=known then
//!     begin value(q):=value(q)+value(r); goto done1;
//!     end
//!   else  begin tt:=type(r);
//!     if tt=independent then pp:=single_dependency(r)
//!     else pp:=dep_list(r);
//!     end;
//! if tt<>independent then copied:=false
//! else  begin copied:=true; tt:=dependent;
//!   end;
//! @<Add dependency list |pp| of type |tt| to dependency list~|p| of type~|t|@>;
//! if copied then flush_node_list(pp);
//! done1:
//!
//! @ @<Add dependency list |pp| of type |tt| to dependency list~|p| of type~|t|@>=
//! watch_coefs:=false;
//! if t=tt then p:=p_plus_q(p,pp,t)
//! else if t=proto_dependent then
//!   p:=p_plus_fq(p,unity,pp,proto_dependent,dependent)
//! else  begin q:=p;
//!   while info(q)<>null do
//!     begin value(q):=round_fraction(value(q)); q:=link(q);
//!     end;
//!   t:=proto_dependent; p:=p_plus_q(p,pp,t);
//!   end;
//! watch_coefs:=true;
//!
//! @ Our next goal is to process type declarations. For this purpose it's
//! convenient to have a procedure that scans a $\langle\,$declared
//! variable$\,\rangle$ and returns the corresponding token list. After the
//! following procedure has acted, the token after the declared variable
//! will have been scanned, so it will appear in |cur_cmd|, |cur_mod|,
//! and~|cur_sym|.
//!
//! @<Declare the function called |scan_declared_variable|@>=
//! function scan_declared_variable:pointer;
//! label done;
//! var @!x:pointer; {hash address of the variable's root}
//! @!h,@!t:pointer; {head and tail of the token list to be returned}
//! @!l:pointer; {hash address of left bracket}
//! begin get_symbol; x:=cur_sym;
//! if cur_cmd<>tag_token then clear_symbol(x,false);
//! h:=get_avail; info(h):=x; t:=h;@/
//! loop@+  begin get_x_next;
//!   if cur_sym=0 then goto done;
//!   if cur_cmd<>tag_token then if cur_cmd<>internal_quantity then
//!     if cur_cmd=left_bracket then @<Descend past a collective subscript@>
//!     else goto done;
//!   link(t):=get_avail; t:=link(t); info(t):=cur_sym;
//!   end;
//! done: if eq_type(x) mod outer_tag<>tag_token then clear_symbol(x,false);
//! if equiv(x)=null then new_root(x);
//! scan_declared_variable:=h;
//! end;
//!
//! @ If the subscript isn't collective, we don't accept it as part of the
//! declared variable.
//!
//! @<Descend past a collective subscript@>=
//! begin l:=cur_sym; get_x_next;
//! if cur_cmd<>right_bracket then
//!   begin back_input; cur_sym:=l; cur_cmd:=left_bracket; goto done;
//!   end
//! else cur_sym:=collective_subscript;
//! end
//!
//! @ Type declarations are introduced by the following primitive operations.
//!
//! @<Put each...@>=
//! primitive("numeric",type_name,numeric_type);@/
//! @!@:numeric_}{\&{numeric} primitive@>
//! primitive("string",type_name,string_type);@/
//! @!@:string_}{\&{string} primitive@>
//! primitive("boolean",type_name,boolean_type);@/
//! @!@:boolean_}{\&{boolean} primitive@>
//! primitive("path",type_name,path_type);@/
//! @!@:path_}{\&{path} primitive@>
//! primitive("pen",type_name,pen_type);@/
//! @!@:pen_}{\&{pen} primitive@>
//! primitive("picture",type_name,picture_type);@/
//! @!@:picture_}{\&{picture} primitive@>
//! primitive("transform",type_name,transform_type);@/
//! @!@:transform_}{\&{transform} primitive@>
//! primitive("pair",type_name,pair_type);@/
//! @!@:pair_}{\&{pair} primitive@>
//!
//! @ @<Cases of |print_cmd...@>=
//! type_name: print_type(m);
//!
//! @ Now we are ready to handle type declarations, assuming that a
//! |type_name| has just been scanned.
//!
//! @<Declare action procedures for use by |do_statement|@>=
//! procedure do_type_declaration;
//! var @!t:small_number; {the type being declared}
//! @!p:pointer; {token list for a declared variable}
//! @!q:pointer; {value node for the variable}
//! begin if cur_mod>=transform_type then t:=cur_mod@+else t:=cur_mod+unknown_tag;
//! repeat p:=scan_declared_variable;
//! flush_variable(equiv(info(p)),link(p),false);@/
//! q:=find_variable(p);
//! if q<>null then
//!   begin type(q):=t; value(q):=null;
//!   end
//! else  begin print_err("Declared variable conflicts with previous vardef");
//! @.Declared variable conflicts...@>
//!   help2("You can't use, e.g., `numeric foo[]' after `vardef foo'.")@/
//!     ("Proceed, and I'll ignore the illegal redeclaration.");
//!   put_get_error;
//!   end;
//! flush_list(p);
//! if cur_cmd<comma then @<Flush spurious symbols after the declared variable@>;
//! until end_of_statement;
//! end;
//!
//! @ @<Flush spurious symbols after the declared variable@>=
//! begin print_err("Illegal suffix of declared variable will be flushed");
//! @.Illegal suffix...flushed@>
//! help5("Variables in declarations must consist entirely of")@/
//!   ("names and collective subscripts, e.g., `x[]a'.")@/
//!   ("Are you trying to use a reserved word in a variable name?")@/
//!   ("I'm going to discard the junk I found here,")@/
//!   ("up to the next comma or the end of the declaration.");
//! if cur_cmd=numeric_token then
//!   help_line[2]:="Explicit subscripts like `x15a' aren't permitted.";
//! put_get_error; scanner_status:=flushing;
//! repeat get_next;
//! @<Decrease the string reference count...@>;
//! until cur_cmd>=comma; {either |end_of_statement| or |cur_cmd=comma|}
//! scanner_status:=normal;
//! end
//!
