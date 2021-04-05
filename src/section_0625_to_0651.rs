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
//! @* \[31] Input stacks and states.
//! The state of \MF's input mechanism appears in the input stack, whose
//! entries are records with five fields, called |index|, |start|, |loc|,
//! |limit|, and |name|. The top element of this stack is maintained in a
//! global variable for which no subscripting needs to be done; the other
//! elements of the stack appear in an array. Hence the stack is declared thus:
//!
//! @<Types...@>=
//! @!in_state_record = record
//!   @!index_field: quarterword;
//!   @!start_field,@!loc_field, @!limit_field, @!name_field: halfword;
//!   end;
//!
//! @ @<Glob...@>=
//! @!input_stack : array[0..stack_size] of in_state_record;
//! @!input_ptr : 0..stack_size; {first unused location of |input_stack|}
//! @!max_in_stack: 0..stack_size; {largest value of |input_ptr| when pushing}
//! @!cur_input : in_state_record; {the ``top'' input state}
//!
//! @ We've already defined the special variable |@!loc==cur_input.loc_field|
//! in our discussion of basic input-output routines. The other components of
//! |cur_input| are defined in the same way:
//!
//! @d index==cur_input.index_field {reference for buffer information}
//! @d start==cur_input.start_field {starting position in |buffer|}
//! @d limit==cur_input.limit_field {end of current line in |buffer|}
//! @d name==cur_input.name_field {name of the current file}
//!
//! @ Let's look more closely now at the five control variables
//! (|index|,~|start|,~|loc|,~|limit|,~|name|),
//! assuming that \MF\ is reading a line of characters that have been input
//! from some file or from the user's terminal. There is an array called
//! |buffer| that acts as a stack of all lines of characters that are
//! currently being read from files, including all lines on subsidiary
//! levels of the input stack that are not yet completed. \MF\ will return to
//! the other lines when it is finished with the present input file.
//!
//! (Incidentally, on a machine with byte-oriented addressing, it would be
//! appropriate to combine |buffer| with the |str_pool| array,
//! letting the buffer entries grow downward from the top of the string pool
//! and checking that these two tables don't bump into each other.)
//!
//! The line we are currently working on begins in position |start| of the
//! buffer; the next character we are about to read is |buffer[loc]|; and
//! |limit| is the location of the last character present. We always have
//! |loc<=limit|. For convenience, |buffer[limit]| has been set to |"%"|, so
//! that the end of a line is easily sensed.
//!
//! The |name| variable is a string number that designates the name of
//! the current file, if we are reading a text file. It is 0 if we
//! are reading from the terminal for normal input, or 1 if we are executing a
//! \&{readstring} command, or 2 if we are reading a string that was
//! moved into the buffer by \&{scantokens}.
//!
//! @ Additional information about the current line is available via the
//! |index| variable, which counts how many lines of characters are present
//! in the buffer below the current level. We have |index=0| when reading
//! from the terminal and prompting the user for each line; then if the user types,
//! e.g., `\.{input font}', we will have |index=1| while reading
//! the file \.{font.mf}. However, it does not follow that |index| is the
//! same as the input stack pointer, since many of the levels on the input
//! stack may come from token lists.
//!
//! The global variable |in_open| is equal to the |index|
//! value of the highest non-token-list level. Thus, the number of partially read
//! lines in the buffer is |in_open+1|, and we have |in_open=index|
//! when we are not reading a token list.
//!
//! If we are not currently reading from the terminal,
//! we are reading from the file variable |input_file[index]|. We use
//! the notation |terminal_input| as a convenient abbreviation for |name=0|,
//! and |cur_file| as an abbreviation for |input_file[index]|.
//!
//! The global variable |line| contains the line number in the topmost
//! open file, for use in error messages. If we are not reading from
//! the terminal, |line_stack[index]| holds the line number for the
//! enclosing level, so that |line| can be restored when the current
//! file has been read.
//!
//! If more information about the input state is needed, it can be
//! included in small arrays like those shown here. For example,
//! the current page or segment number in the input file might be
//! put into a variable |@!page|, maintained for enclosing levels in
//! `\ignorespaces|@!page_stack:array[1..max_in_open] of integer|\unskip'
//! by analogy with |line_stack|.
//! @^system dependencies@>
//!
//! @d terminal_input==(name=0) {are we reading from the terminal?}
//! @d cur_file==input_file[index] {the current |alpha_file| variable}
//!
//! @<Glob...@>=
//! @!in_open : 0..max_in_open; {the number of lines in the buffer, less one}
//! @!open_parens : 0..max_in_open; {the number of open text files}
//! @!input_file : array[1..max_in_open] of alpha_file;
//! @!line : integer; {current line number in the current source file}
//! @!line_stack : array[1..max_in_open] of integer;
//!
//! @ However, all this discussion about input state really applies only to the
//! case that we are inputting from a file. There is another important case,
//! namely when we are currently getting input from a token list. In this case
//! |index>max_in_open|, and the conventions about the other state variables
//! are different:
//!
//! \yskip\hang|loc| is a pointer to the current node in the token list, i.e.,
//! the node that will be read next. If |loc=null|, the token list has been
//! fully read.
//!
//! \yskip\hang|start| points to the first node of the token list; this node
//! may or may not contain a reference count, depending on the type of token
//! list involved.
//!
//! \yskip\hang|token_type|, which takes the place of |index| in the
//! discussion above, is a code number that explains what kind of token list
//! is being scanned.
//!
//! \yskip\hang|name| points to the |eqtb| address of the macro
//! being expanded, if the current token list is a macro not defined by
//! \&{vardef}. Macros defined by \&{vardef} have |name=null|; their name
//! can be deduced by looking at their first two parameters.
//!
//! \yskip\hang|param_start|, which takes the place of |limit|, tells where
//! the parameters of the current macro or loop text begin in the |param_stack|.
//!
//! \yskip\noindent The |token_type| can take several values, depending on
//! where the current token list came from:
//!
//! \yskip
//! \indent|forever_text|, if the token list being scanned is the body of
//! a \&{forever} loop;
//!
//! \indent|loop_text|, if the token list being scanned is the body of
//! a \&{for} or \&{forsuffixes} loop;
//!
//! \indent|parameter|, if a \&{text} or \&{suffix} parameter is being scanned;
//!
//! \indent|backed_up|, if the token list being scanned has been inserted as
//! `to be read again';
//!
//! \indent|inserted|, if the token list being scanned has been inserted as
//! part of error recovery;
//!
//! \indent|macro|, if the expansion of a user-defined symbolic token is being
//! scanned.
//!
//! \yskip\noindent
//! The token list begins with a reference count if and only if |token_type=
//! macro|.
//! @^reference counts@>
//!
//! @d token_type==index {type of current token list}
//! @d token_state==(index>max_in_open) {are we scanning a token list?}
//! @d file_state==(index<=max_in_open) {are we scanning a file line?}
//! @d param_start==limit {base of macro parameters in |param_stack|}
//! @d forever_text=max_in_open+1 {|token_type| code for loop texts}
//! @d loop_text=max_in_open+2 {|token_type| code for loop texts}
//! @d parameter=max_in_open+3 {|token_type| code for parameter texts}
//! @d backed_up=max_in_open+4 {|token_type| code for texts to be reread}
//! @d inserted=max_in_open+5 {|token_type| code for inserted texts}
//! @d macro=max_in_open+6 {|token_type| code for macro replacement texts}
//!
//! @ The |param_stack| is an auxiliary array used to hold pointers to the token
//! lists for parameters at the current level and subsidiary levels of input.
//! This stack grows at a different rate from the others.
//!
//! @<Glob...@>=
//! @!param_stack:array [0..param_size] of pointer;
//!   {token list pointers for parameters}
//! @!param_ptr:0..param_size; {first unused entry in |param_stack|}
//! @!max_param_stack:integer;
//!   {largest value of |param_ptr|}
//!
//! @ Thus, the ``current input state'' can be very complicated indeed; there
//! can be many levels and each level can arise in a variety of ways. The
//! |show_context| procedure, which is used by \MF's error-reporting routine to
//! print out the current input state on all levels down to the most recent
//! line of characters from an input file, illustrates most of these conventions.
//! The global variable |file_ptr| contains the lowest level that was
//! displayed by this procedure.
//!
//! @<Glob...@>=
//! @!file_ptr:0..stack_size; {shallowest level shown by |show_context|}
//!
//! @ The status at each level is indicated by printing two lines, where the first
//! line indicates what was read so far and the second line shows what remains
//! to be read. The context is cropped, if necessary, so that the first line
//! contains at most |half_error_line| characters, and the second contains
//! at most |error_line|. Non-current input levels whose |token_type| is
//! `|backed_up|' are shown only if they have not been fully read.
//!
//! @p procedure show_context; {prints where the scanner is}
//! label done;
//! var @!old_setting:0..max_selector; {saved |selector| setting}
//! @<Local variables for formatting calculations@>@/
//! begin file_ptr:=input_ptr; input_stack[file_ptr]:=cur_input;
//!   {store current state}
//! loop@+begin cur_input:=input_stack[file_ptr]; {enter into the context}
//!   @<Display the current context@>;
//!   if file_state then
//!     if (name>2) or (file_ptr=0) then goto done;
//!   decr(file_ptr);
//!   end;
//! done: cur_input:=input_stack[input_ptr]; {restore original state}
//! end;
//!
//! @ @<Display the current context@>=
//! if (file_ptr=input_ptr) or file_state or
//!    (token_type<>backed_up) or (loc<>null) then
//!     {we omit backed-up token lists that have already been read}
//!   begin tally:=0; {get ready to count characters}
//!   old_setting:=selector;
//!   if file_state then
//!     begin @<Print location of current line@>;
//!     @<Pseudoprint the line@>;
//!     end
//!   else  begin @<Print type of token list@>;
//!     @<Pseudoprint the token list@>;
//!     end;
//!   selector:=old_setting; {stop pseudoprinting}
//!   @<Print two lines using the tricky pseudoprinted information@>;
//!   end
//!
//! @ This routine should be changed, if necessary, to give the best possible
//! indication of where the current line resides in the input file.
//! For example, on some systems it is best to print both a page and line number.
//! @^system dependencies@>
//!
//! @<Print location of current line@>=
//! if name<=1 then
//!   if terminal_input and(file_ptr=0) then print_nl("<*>")
//!   else print_nl("<insert>")
//! else if name=2 then print_nl("<scantokens>")
//! else  begin print_nl("l."); print_int(line);
//!   end;
//! print_char(" ")
//!
//! @ @<Print type of token list@>=
//! case token_type of
//! forever_text: print_nl("<forever> ");
//! loop_text: @<Print the current loop value@>;
//! parameter: print_nl("<argument> ");
//! backed_up: if loc=null then print_nl("<recently read> ")
//!   else print_nl("<to be read again> ");
//! inserted: print_nl("<inserted text> ");
//! macro: begin print_ln;
//!   if name<>null then slow_print(text(name))
//!   else @<Print the name of a \&{vardef}'d macro@>;
//!   print("->");
//!   end;
//! othercases print_nl("?") {this should never happen}
//! @.?\relax@>
//! endcases
//!
//! @ The parameter that corresponds to a loop text is either a token list
//! (in the case of \&{forsuffixes}) or a ``capsule'' (in the case of \&{for}).
//! We'll discuss capsules later; for now, all we need to know is that
//! the |link| field in a capsule parameter is |void| and that
//! |print_exp(p,0)| displays the value of capsule~|p| in abbreviated form.
//!
//! @<Print the current loop value@>=
//! begin print_nl("<for("); p:=param_stack[param_start];
//! if p<>null then
//!   if link(p)=void then print_exp(p,0) {we're in a \&{for} loop}
//!   else show_token_list(p,null,20,tally);
//! print(")> ");
//! end
//!
//! @ The first two parameters of a macro defined by \&{vardef} will be token
//! lists representing the macro's prefix and ``at point.'' By putting these
//! together, we get the macro's full name.
//!
//! @<Print the name of a \&{vardef}'d macro@>=
//! begin p:=param_stack[param_start];
//! if p=null then show_token_list(param_stack[param_start+1],null,20,tally)
//! else  begin q:=p;
//!   while link(q)<>null do q:=link(q);
//!   link(q):=param_stack[param_start+1];
//!   show_token_list(p,null,20,tally);
//!   link(q):=null;
//!   end;
//! end
//!
//! @ Now it is necessary to explain a little trick. We don't want to store a long
//! string that corresponds to a token list, because that string might take up
//! lots of memory; and we are printing during a time when an error message is
//! being given, so we dare not do anything that might overflow one of \MF's
//! tables. So `pseudoprinting' is the answer: We enter a mode of printing
//! that stores characters into a buffer of length |error_line|, where character
//! $k+1$ is placed into \hbox{|trick_buf[k mod error_line]|} if
//! |k<trick_count|, otherwise character |k| is dropped. Initially we set
//! |tally:=0| and |trick_count:=1000000|; then when we reach the
//! point where transition from line 1 to line 2 should occur, we
//! set |first_count:=tally| and |trick_count:=@tmax@>(error_line,
//! tally+1+error_line-half_error_line)|. At the end of the
//! pseudoprinting, the values of |first_count|, |tally|, and
//! |trick_count| give us all the information we need to print the two lines,
//! and all of the necessary text is in |trick_buf|.
//!
//! Namely, let |l| be the length of the descriptive information that appears
//! on the first line. The length of the context information gathered for that
//! line is |k=first_count|, and the length of the context information
//! gathered for line~2 is $m=\min(|tally|, |trick_count|)-k$. If |l+k<=h|,
//! where |h=half_error_line|, we print |trick_buf[0..k-1]| after the
//! descriptive information on line~1, and set |n:=l+k|; here |n| is the
//! length of line~1. If $l+k>h$, some cropping is necessary, so we set |n:=h|
//! and print `\.{...}' followed by
//! $$\hbox{|trick_buf[(l+k-h+3)..k-1]|,}$$
//! where subscripts of |trick_buf| are circular modulo |error_line|. The
//! second line consists of |n|~spaces followed by |trick_buf[k..(k+m-1)]|,
//! unless |n+m>error_line|; in the latter case, further cropping is done.
//! This is easier to program than to explain.
//!
//! @<Local variables for formatting...@>=
//! @!i:0..buf_size; {index into |buffer|}
//! @!l:integer; {length of descriptive information on line 1}
//! @!m:integer; {context information gathered for line 2}
//! @!n:0..error_line; {length of line 1}
//! @!p: integer; {starting or ending place in |trick_buf|}
//! @!q: integer; {temporary index}
//!
//! @ The following code tells the print routines to gather
//! the desired information.
//!
//! @d begin_pseudoprint==
//!   begin l:=tally; tally:=0; selector:=pseudo;
//!   trick_count:=1000000;
//!   end
//! @d set_trick_count==
//!   begin first_count:=tally;
//!   trick_count:=tally+1+error_line-half_error_line;
//!   if trick_count<error_line then trick_count:=error_line;
//!   end
//!
//! @ And the following code uses the information after it has been gathered.
//!
//! @<Print two lines using the tricky pseudoprinted information@>=
//! if trick_count=1000000 then set_trick_count;
//!   {|set_trick_count| must be performed}
//! if tally<trick_count then m:=tally-first_count
//! else m:=trick_count-first_count; {context on line 2}
//! if l+first_count<=half_error_line then
//!   begin p:=0; n:=l+first_count;
//!   end
//! else  begin print("..."); p:=l+first_count-half_error_line+3;
//!   n:=half_error_line;
//!   end;
//! for q:=p to first_count-1 do print_char(trick_buf[q mod error_line]);
//! print_ln;
//! for q:=1 to n do print_char(" "); {print |n| spaces to begin line~2}
//! if m+n<=error_line then p:=first_count+m else p:=first_count+(error_line-n-3);
//! for q:=first_count to p-1 do print_char(trick_buf[q mod error_line]);
//! if m+n>error_line then print("...")
//!
//! @ But the trick is distracting us from our current goal, which is to
//! understand the input state. So let's concentrate on the data structures that
//! are being pseudoprinted as we finish up the |show_context| procedure.
//!
//! @<Pseudoprint the line@>=
//! begin_pseudoprint;
//! if limit>0 then for i:=start to limit-1 do
//!   begin if i=loc then set_trick_count;
//!   print(buffer[i]);
//!   end
//!
//! @ @<Pseudoprint the token list@>=
//! begin_pseudoprint;
//! if token_type<>macro then show_token_list(start,loc,100000,0)
//! else show_macro(start,loc,100000)
//!
//! @ Here is the missing piece of |show_token_list| that is activated when the
//! token beginning line~2 is about to be shown:
//!
//! @<Do magic computation@>=set_trick_count
//!
//! @* \[32] Maintaining the input stacks.
//! The following subroutines change the input status in commonly needed ways.
//!
//! First comes |push_input|, which stores the current state and creates a
//! new level (having, initially, the same properties as the old).
//!
//! @d push_input==@t@> {enter a new input level, save the old}
//!   begin if input_ptr>max_in_stack then
//!     begin max_in_stack:=input_ptr;
//!     if input_ptr=stack_size then overflow("input stack size",stack_size);
//! @:METAFONT capacity exceeded input stack size}{\quad input stack size@>
//!     end;
//!   input_stack[input_ptr]:=cur_input; {stack the record}
//!   incr(input_ptr);
//!   end
//!
//! @ And of course what goes up must come down.
//!
//! @d pop_input==@t@> {leave an input level, re-enter the old}
//!   begin decr(input_ptr); cur_input:=input_stack[input_ptr];
//!   end
//!
//! @ Here is a procedure that starts a new level of token-list input, given
//! a token list |p| and its type |t|. If |t=macro|, the calling routine should
//! set |name|, reset~|loc|, and increase the macro's reference count.
//!
//! @d back_list(#)==begin_token_list(#,backed_up) {backs up a simple token list}
//!
//! @p procedure begin_token_list(@!p:pointer;@!t:quarterword);
//! begin push_input; start:=p; token_type:=t;
//! param_start:=param_ptr; loc:=p;
//! end;
//!
//! @ When a token list has been fully scanned, the following computations
//! should be done as we leave that level of input.
//! @^inner loop@>
//!
//! @p procedure end_token_list; {leave a token-list input level}
//! label done;
//! var @!p:pointer; {temporary register}
//! begin if token_type>=backed_up then {token list to be deleted}
//!   if token_type<=inserted then
//!     begin flush_token_list(start); goto done;
//!     end
//!   else delete_mac_ref(start); {update reference count}
//! while param_ptr>param_start do {parameters must be flushed}
//!   begin decr(param_ptr);
//!   p:=param_stack[param_ptr];
//!   if p<>null then
//!     if link(p)=void then {it's an \&{expr} parameter}
//!       begin recycle_value(p); free_node(p,value_node_size);
//!       end
//!     else flush_token_list(p); {it's a \&{suffix} or \&{text} parameter}
//!   end;
//! done: pop_input; check_interrupt;
//! end;
//!
//! @ The contents of |cur_cmd,cur_mod,cur_sym| are placed into an equivalent
//! token by the |cur_tok| routine.
//! @^inner loop@>
//!
//! @p @t\4@>@<Declare the procedure called |make_exp_copy|@>@;@/
//! function cur_tok:pointer;
//! var @!p:pointer; {a new token node}
//! @!save_type:small_number; {|cur_type| to be restored}
//! @!save_exp:integer; {|cur_exp| to be restored}
//! begin if cur_sym=0 then
//!   if cur_cmd=capsule_token then
//!     begin save_type:=cur_type; save_exp:=cur_exp;
//!     make_exp_copy(cur_mod); p:=stash_cur_exp; link(p):=null;
//!     cur_type:=save_type; cur_exp:=save_exp;
//!     end
//!   else  begin p:=get_node(token_node_size);
//!     value(p):=cur_mod; name_type(p):=token;
//!     if cur_cmd=numeric_token then type(p):=known
//!     else type(p):=string_type;
//!     end
//! else  begin fast_get_avail(p); info(p):=cur_sym;
//!   end;
//! cur_tok:=p;
//! end;
//!
