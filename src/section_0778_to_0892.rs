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
