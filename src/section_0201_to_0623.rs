//! @ @<Set init...@>=
//! next(1):=0; text(1):=0; eq_type(1):=tag_token; equiv(1):=null;
//! for k:=2 to hash_end do
//!   begin hash[k]:=hash[1]; eqtb[k]:=eqtb[1];
//!   end;
//!
//! @ @<Initialize table entries...@>=
//! hash_used:=frozen_inaccessible; {nothing is used}
//! st_count:=0;@/
//! text(frozen_bad_vardef):="a bad variable";
//! text(frozen_fi):="fi";
//! text(frozen_end_group):="endgroup";
//! text(frozen_end_def):="enddef";
//! text(frozen_end_for):="endfor";@/
//! text(frozen_semicolon):=";";
//! text(frozen_colon):=":";
//! text(frozen_slash):="/";
//! text(frozen_left_bracket):="[";
//! text(frozen_right_delimiter):=")";@/
//! text(frozen_inaccessible):=" INACCESSIBLE";@/
//! eq_type(frozen_right_delimiter):=right_delimiter;
//!
//! @ @<Check the ``constant'' values...@>=
//! if hash_end+max_internal>max_halfword then bad:=21;
//!
//! @ Here is the subroutine that searches the hash table for an identifier
//! that matches a given string of length~|l| appearing in |buffer[j..
//! (j+l-1)]|. If the identifier is not found, it is inserted; hence it
//! will always be found, and the corresponding hash table address
//! will be returned.
//!
//! @p function id_lookup(@!j,@!l:integer):pointer; {search the hash table}
//! label found; {go here when you've found it}
//! var @!h:integer; {hash code}
//! @!p:pointer; {index in |hash| array}
//! @!k:pointer; {index in |buffer| array}
//! begin if l=1 then @<Treat special case of length 1 and |goto found|@>;
//! @<Compute the hash code |h|@>;
//! p:=h+hash_base; {we start searching here; note that |0<=h<hash_prime|}
//! loop@+  begin if text(p)>0 then if length(text(p))=l then
//!     if str_eq_buf(text(p),j) then goto found;
//!   if next(p)=0 then
//!     @<Insert a new symbolic token after |p|, then
//!       make |p| point to it and |goto found|@>;
//!   p:=next(p);
//!   end;
//! found: id_lookup:=p;
//! end;
//!
//! @ @<Treat special case of length 1...@>=
//! begin p:=buffer[j]+1; text(p):=p-1; goto found;
//! end
//!
//! @ @<Insert a new symbolic...@>=
//! begin if text(p)>0 then
//!   begin repeat if hash_is_full then
//!     overflow("hash size",hash_size);
//! @:METAFONT capacity exceeded hash size}{\quad hash size@>
//!   decr(hash_used);
//!   until text(hash_used)=0; {search for an empty location in |hash|}
//!   next(p):=hash_used; p:=hash_used;
//!   end;
//! str_room(l);
//! for k:=j to j+l-1 do append_char(buffer[k]);
//! text(p):=make_string; str_ref[text(p)]:=max_str_ref;
//! @!stat incr(st_count);@+tats@;@/
//! goto found;
//! end
//!
//! @ The value of |hash_prime| should be roughly 85\pct! of |hash_size|, and it
//! should be a prime number.  The theory of hashing tells us to expect fewer
//! than two table probes, on the average, when the search is successful.
//! [See J.~S. Vitter, {\sl Journal of the ACM\/ \bf30} (1983), 231--258.]
//! @^Vitter, Jeffrey Scott@>
//!
//! @<Compute the hash code |h|@>=
//! h:=buffer[j];
//! for k:=j+1 to j+l-1 do
//!   begin h:=h+h+buffer[k];
//!   while h>=hash_prime do h:=h-hash_prime;
//!   end
//!
//! @ @<Search |eqtb| for equivalents equal to |p|@>=
//! for q:=1 to hash_end do
//!   begin if equiv(q)=p then
//!     begin print_nl("EQUIV("); print_int(q); print_char(")");
//!     end;
//!   end
//!
//! @ We need to put \MF's ``primitive'' symbolic tokens into the hash
//! table, together with their command code (which will be the |eq_type|)
//! and an operand (which will be the |equiv|). The |primitive| procedure
//! does this, in a way that no \MF\ user can. The global value |cur_sym|
//! contains the new |eqtb| pointer after |primitive| has acted.
//!
//! @p @!init procedure primitive(@!s:str_number;@!c:halfword;@!o:halfword);
//! var @!k:pool_pointer; {index into |str_pool|}
//! @!j:small_number; {index into |buffer|}
//! @!l:small_number; {length of the string}
//! begin k:=str_start[s]; l:=str_start[s+1]-k;
//!   {we will move |s| into the (empty) |buffer|}
//! for j:=0 to l-1 do buffer[j]:=so(str_pool[k+j]);
//! cur_sym:=id_lookup(0,l);@/
//! if s>=256 then {we don't want to have the string twice}
//!   begin flush_string(str_ptr-1); text(cur_sym):=s;
//!   end;
//! eq_type(cur_sym):=c; equiv(cur_sym):=o;
//! end;
//! tini
//!
//! @ Many of \MF's primitives need no |equiv|, since they are identifiable
//! by their |eq_type| alone. These primitives are loaded into the hash table
//! as follows:
//!
//! @<Put each of \MF's primitives into the hash table@>=
//! primitive("..",path_join,0);@/
//! @!@:.._}{\.{..} primitive@>
//! primitive("[",left_bracket,0); eqtb[frozen_left_bracket]:=eqtb[cur_sym];@/
//! @!@:[ }{\.{[} primitive@>
//! primitive("]",right_bracket,0);@/
//! @!@:] }{\.{]} primitive@>
//! primitive("}",right_brace,0);@/
//! @!@:]]}{\.{\char`\}} primitive@>
//! primitive("{",left_brace,0);@/
//! @!@:][}{\.{\char`\{} primitive@>
//! primitive(":",colon,0); eqtb[frozen_colon]:=eqtb[cur_sym];@/
//! @!@:: }{\.{:} primitive@>
//! primitive("::",double_colon,0);@/
//! @!@::: }{\.{::} primitive@>
//! primitive("||:",bchar_label,0);@/
//! @!@:::: }{\.{\char'174\char'174:} primitive@>
//! primitive(":=",assignment,0);@/
//! @!@::=_}{\.{:=} primitive@>
//! primitive(",",comma,0);@/
//! @!@:, }{\., primitive@>
//! primitive(";",semicolon,0); eqtb[frozen_semicolon]:=eqtb[cur_sym];@/
//! @!@:; }{\.; primitive@>
//! primitive("\",relax,0);@/
//! @!@:]]\\}{\.{\char`\\} primitive@>
//! @#
//! primitive("addto",add_to_command,0);@/
//! @!@:add_to_}{\&{addto} primitive@>
//! primitive("at",at_token,0);@/
//! @!@:at_}{\&{at} primitive@>
//! primitive("atleast",at_least,0);@/
//! @!@:at_least_}{\&{atleast} primitive@>
//! primitive("begingroup",begin_group,0); bg_loc:=cur_sym;@/
//! @!@:begin_group_}{\&{begingroup} primitive@>
//! primitive("controls",controls,0);@/
//! @!@:controls_}{\&{controls} primitive@>
//! primitive("cull",cull_command,0);@/
//! @!@:cull_}{\&{cull} primitive@>
//! primitive("curl",curl_command,0);@/
//! @!@:curl_}{\&{curl} primitive@>
//! primitive("delimiters",delimiters,0);@/
//! @!@:delimiters_}{\&{delimiters} primitive@>
//! primitive("display",display_command,0);@/
//! @!@:display_}{\&{display} primitive@>
//! primitive("endgroup",end_group,0);
//!  eqtb[frozen_end_group]:=eqtb[cur_sym]; eg_loc:=cur_sym;@/
//! @!@:endgroup_}{\&{endgroup} primitive@>
//! primitive("everyjob",every_job_command,0);@/
//! @!@:every_job_}{\&{everyjob} primitive@>
//! primitive("exitif",exit_test,0);@/
//! @!@:exit_if_}{\&{exitif} primitive@>
//! primitive("expandafter",expand_after,0);@/
//! @!@:expand_after_}{\&{expandafter} primitive@>
//! primitive("from",from_token,0);@/
//! @!@:from_}{\&{from} primitive@>
//! primitive("inwindow",in_window,0);@/
//! @!@:in_window_}{\&{inwindow} primitive@>
//! primitive("interim",interim_command,0);@/
//! @!@:interim_}{\&{interim} primitive@>
//! primitive("let",let_command,0);@/
//! @!@:let_}{\&{let} primitive@>
//! primitive("newinternal",new_internal,0);@/
//! @!@:new_internal_}{\&{newinternal} primitive@>
//! primitive("of",of_token,0);@/
//! @!@:of_}{\&{of} primitive@>
//! primitive("openwindow",open_window,0);@/
//! @!@:open_window_}{\&{openwindow} primitive@>
//! primitive("randomseed",random_seed,0);@/
//! @!@:random_seed_}{\&{randomseed} primitive@>
//! primitive("save",save_command,0);@/
//! @!@:save_}{\&{save} primitive@>
//! primitive("scantokens",scan_tokens,0);@/
//! @!@:scan_tokens_}{\&{scantokens} primitive@>
//! primitive("shipout",ship_out_command,0);@/
//! @!@:ship_out_}{\&{shipout} primitive@>
//! primitive("skipto",skip_to,0);@/
//! @!@:skip_to_}{\&{skipto} primitive@>
//! primitive("step",step_token,0);@/
//! @!@:step_}{\&{step} primitive@>
//! primitive("str",str_op,0);@/
//! @!@:str_}{\&{str} primitive@>
//! primitive("tension",tension,0);@/
//! @!@:tension_}{\&{tension} primitive@>
//! primitive("to",to_token,0);@/
//! @!@:to_}{\&{to} primitive@>
//! primitive("until",until_token,0);@/
//! @!@:until_}{\&{until} primitive@>
//!
//! @ Each primitive has a corresponding inverse, so that it is possible to
//! display the cryptic numeric contents of |eqtb| in symbolic form.
//! Every call of |primitive| in this program is therefore accompanied by some
//! straightforward code that forms part of the |print_cmd_mod| routine
//! explained below.
//!
//! @<Cases of |print_cmd_mod| for symbolic printing of primitives@>=
//! add_to_command:print("addto");
//! assignment:print(":=");
//! at_least:print("atleast");
//! at_token:print("at");
//! bchar_label:print("||:");
//! begin_group:print("begingroup");
//! colon:print(":");
//! comma:print(",");
//! controls:print("controls");
//! cull_command:print("cull");
//! curl_command:print("curl");
//! delimiters:print("delimiters");
//! display_command:print("display");
//! double_colon:print("::");
//! end_group:print("endgroup");
//! every_job_command:print("everyjob");
//! exit_test:print("exitif");
//! expand_after:print("expandafter");
//! from_token:print("from");
//! in_window:print("inwindow");
//! interim_command:print("interim");
//! left_brace:print("{");
//! left_bracket:print("[");
//! let_command:print("let");
//! new_internal:print("newinternal");
//! of_token:print("of");
//! open_window:print("openwindow");
//! path_join:print("..");
//! random_seed:print("randomseed");
//! relax:print_char("\");
//! right_brace:print("}");
//! right_bracket:print("]");
//! save_command:print("save");
//! scan_tokens:print("scantokens");
//! semicolon:print(";");
//! ship_out_command:print("shipout");
//! skip_to:print("skipto");
//! step_token:print("step");
//! str_op:print("str");
//! tension:print("tension");
//! to_token:print("to");
//! until_token:print("until");
//!
//! @ We will deal with the other primitives later, at some point in the program
//! where their |eq_type| and |equiv| values are more meaningful.  For example,
//! the primitives for macro definitions will be loaded when we consider the
//! routines that define macros.
//! It is easy to find where each particular
//! primitive was treated by looking in the index at the end; for example, the
//! section where |"def"| entered |eqtb| is listed under `\&{def} primitive'.
//!
//! @* \[14] Token lists.
//! A \MF\ token is either symbolic or numeric or a string, or it denotes
//! a macro parameter or capsule; so there are five corresponding ways to encode it
//! @^token@>
//! internally: (1)~A symbolic token whose hash code is~|p|
//! is represented by the number |p|, in the |info| field of a single-word
//! node in~|mem|. (2)~A numeric token whose |scaled| value is~|v| is
//! represented in a two-word node of~|mem|; the |type| field is |known|,
//! the |name_type| field is |token|, and the |value| field holds~|v|.
//! The fact that this token appears in a two-word node rather than a
//! one-word node is, of course, clear from the node address.
//! (3)~A string token is also represented in a two-word node; the |type|
//! field is |string_type|, the |name_type| field is |token|, and the
//! |value| field holds the corresponding |str_number|.  (4)~Capsules have
//! |name_type=capsule|, and their |type| and |value| fields represent
//! arbitrary values (in ways to be explained later).  (5)~Macro parameters
//! are like symbolic tokens in that they appear in |info| fields of
//! one-word nodes. The $k$th parameter is represented by |expr_base+k| if it
//! is of type \&{expr}, or by |suffix_base+k| if it is of type \&{suffix}, or
//! by |text_base+k| if it is of type \&{text}.  (Here |0<=k<param_size|.)
//! Actual values of these parameters are kept in a separate stack, as we will
//! see later.  The constants |expr_base|, |suffix_base|, and |text_base| are,
//! of course, chosen so that there will be no confusion between symbolic
//! tokens and parameters of various types.
//!
//! It turns out that |value(null)=0|, because |null=null_coords|;
//! we will make use of this coincidence later.
//!
//! Incidentally, while we're speaking of coincidences, we might note that
//! the `\\{type}' field of a node has nothing to do with ``type'' in a
//! printer's sense. It's curious that the same word is used in such different ways.
//!
//! @d type(#) == mem[#].hh.b0 {identifies what kind of value this is}
//! @d name_type(#) == mem[#].hh.b1 {a clue to the name of this value}
//! @d token_node_size=2 {the number of words in a large token node}
//! @d value_loc(#)==#+1 {the word that contains the |value| field}
//! @d value(#)==mem[value_loc(#)].int {the value stored in a large token node}
//! @d expr_base==hash_end+1 {code for the zeroth \&{expr} parameter}
//! @d suffix_base==expr_base+param_size {code for the zeroth \&{suffix} parameter}
//! @d text_base==suffix_base+param_size {code for the zeroth \&{text} parameter}
//!
//! @<Check the ``constant''...@>=
//! if text_base+param_size>max_halfword then bad:=22;
//!
//! @ A numeric token is created by the following trivial routine.
//!
//! @p function new_num_tok(@!v:scaled):pointer;
//! var @!p:pointer; {the new node}
//! begin p:=get_node(token_node_size); value(p):=v;
//! type(p):=known; name_type(p):=token; new_num_tok:=p;
//! end;
//!
//! @ A token list is a singly linked list of nodes in |mem|, where
//! each node contains a token and a link.  Here's a subroutine that gets rid
//! of a token list when it is no longer needed.
//!
//! @p procedure@?token_recycle; forward;@t\2@>@;@/
//! procedure flush_token_list(@!p:pointer);
//! var @!q:pointer; {the node being recycled}
//! begin while p<>null do
//!   begin q:=p; p:=link(p);
//!   if q>=hi_mem_min then free_avail(q)
//!   else  begin case type(q) of
//!     vacuous,boolean_type,known:do_nothing;
//!     string_type:delete_str_ref(value(q));
//!     unknown_types,pen_type,path_type,future_pen,picture_type,
//!      pair_type,transform_type,dependent,proto_dependent,independent:
//!       begin g_pointer:=q; token_recycle;
//!       end;
//!     othercases confusion("token")
//! @:this can't happen token}{\quad token@>
//!     endcases;@/
//!     free_node(q,token_node_size);
//!     end;
//!   end;
//! end;
//!
//! @ The procedure |show_token_list|, which prints a symbolic form of
//! the token list that starts at a given node |p|, illustrates these
//! conventions. The token list being displayed should not begin with a reference
//! count. However, the procedure is intended to be fairly robust, so that if the
//! memory links are awry or if |p| is not really a pointer to a token list,
//! almost nothing catastrophic can happen.
//!
//! An additional parameter |q| is also given; this parameter is either null
//! or it points to a node in the token list where a certain magic computation
//! takes place that will be explained later. (Basically, |q| is non-null when
//! we are printing the two-line context information at the time of an error
//! message; |q| marks the place corresponding to where the second line
//! should begin.)
//!
//! The generation will stop, and `\.{\char`\ ETC.}' will be printed, if the length
//! of printing exceeds a given limit~|l|; the length of printing upon entry is
//! assumed to be a given amount called |null_tally|. (Note that
//! |show_token_list| sometimes uses itself recursively to print
//! variable names within a capsule.)
//! @^recursion@>
//!
//! Unusual entries are printed in the form of all-caps tokens
//! preceded by a space, e.g., `\.{\char`\ BAD}'.
//!
//! @<Declare the procedure called |show_token_list|@>=
//! procedure@?print_capsule; forward; @t\2@>@;@/
//! procedure show_token_list(@!p,@!q:integer;@!l,@!null_tally:integer);
//! label exit;
//! var @!class,@!c:small_number; {the |char_class| of previous and new tokens}
//! @!r,@!v:integer; {temporary registers}
//! begin class:=percent_class;
//! tally:=null_tally;
//! while (p<>null) and (tally<l) do
//!   begin if p=q then @<Do magic computation@>;
//!   @<Display token |p| and set |c| to its class;
//!     but |return| if there are problems@>;
//!   class:=c; p:=link(p);
//!   end;
//! if p<>null then print(" ETC.");
//! @.ETC@>
//! exit:
//! end;
//!
//! @ @<Display token |p| and set |c| to its class...@>=
//! c:=letter_class; {the default}
//! if (p<mem_min)or(p>mem_end) then
//!   begin print(" CLOBBERED"); return;
//! @.CLOBBERED@>
//!   end;
//! if p<hi_mem_min then @<Display two-word token@>
//! else  begin r:=info(p);
//!   if r>=expr_base then @<Display a parameter token@>
//!   else if r<1 then
//!     if r=0 then @<Display a collective subscript@>
//!     else print(" IMPOSSIBLE")
//! @.IMPOSSIBLE@>
//!   else  begin r:=text(r);
//!     if (r<0)or(r>=str_ptr) then print(" NONEXISTENT")
//! @.NONEXISTENT@>
//!     else @<Print string |r| as a symbolic token
//!       and set |c| to its class@>;
//!     end;
//!   end
//!
//! @ @<Display two-word token@>=
//! if name_type(p)=token then
//!   if type(p)=known then @<Display a numeric token@>
//!   else if type(p)<>string_type then print(" BAD")
//! @.BAD@>
//!   else  begin print_char(""""); slow_print(value(p)); print_char("""");
//!     c:=string_class;
//!     end
//! else if (name_type(p)<>capsule)or(type(p)<vacuous)or(type(p)>independent) then
//!   print(" BAD")
//! else  begin g_pointer:=p; print_capsule; c:=right_paren_class;
//!   end
//!
//! @ @<Display a numeric token@>=
//! begin if class=digit_class then print_char(" ");
//! v:=value(p);
//! if v<0 then
//!   begin if class=left_bracket_class then print_char(" ");
//!   print_char("["); print_scaled(v); print_char("]");
//!   c:=right_bracket_class;
//!   end
//! else  begin print_scaled(v); c:=digit_class;
//!   end;
//! end
//!
//! @ Strictly speaking, a genuine token will never have |info(p)=0|.
//! But we will see later (in the definition of attribute nodes) that
//! it is convenient to let |info(p)=0| stand for `\.{[]}'.
//!
//! @<Display a collective subscript@>=
//! begin if class=left_bracket_class then print_char(" ");
//! print("[]"); c:=right_bracket_class;
//! end
//!
//! @ @<Display a parameter token@>=
//! begin if r<suffix_base then
//!   begin print("(EXPR"); r:=r-(expr_base);
//! @.EXPR@>
//!   end
//! else if r<text_base then
//!   begin print("(SUFFIX"); r:=r-(suffix_base);
//! @.SUFFIX@>
//!   end
//! else  begin print("(TEXT"); r:=r-(text_base);
//! @.TEXT@>
//!   end;
//! print_int(r); print_char(")"); c:=right_paren_class;
//! end
//!
//! @ @<Print string |r| as a symbolic token...@>=
//! begin c:=char_class[so(str_pool[str_start[r]])];
//! if c=class then
//!   case c of
//!   letter_class:print_char(".");
//!   isolated_classes:do_nothing;
//!   othercases print_char(" ")
//!   endcases;
//! slow_print(r);
//! end
//!
//! @ The following procedures have been declared |forward| with no parameters,
//! because the author dislikes \PASCAL's convention about |forward| procedures
//! with parameters. It was necessary to do something, because |show_token_list|
//! is recursive (although the recursion is limited to one level), and because
//! |flush_token_list| is syntactically (but not semantically) recursive.
//! @^recursion@>
//!
//! @<Declare miscellaneous procedures that were declared |forward|@>=
//! procedure print_capsule;
//! begin print_char("("); print_exp(g_pointer,0); print_char(")");
//! end;
//! @#
//! procedure token_recycle;
//! begin recycle_value(g_pointer);
//! end;
//!
//! @ @<Glob...@>=
//! @!g_pointer:pointer; {(global) parameter to the |forward| procedures}
//!
//! @ Macro definitions are kept in \MF's memory in the form of token lists
//! that have a few extra one-word nodes at the beginning.
//!
//! The first node contains a reference count that is used to tell when the
//! list is no longer needed. To emphasize the fact that a reference count is
//! present, we shall refer to the |info| field of this special node as the
//! |ref_count| field.
//! @^reference counts@>
//!
//! The next node or nodes after the reference count serve to describe the
//! formal parameters. They consist of zero or more parameter tokens followed
//! by a code for the type of macro.
//!
//! @d ref_count==info {reference count preceding a macro definition or pen header}
//! @d add_mac_ref(#)==incr(ref_count(#)) {make a new reference to a macro list}
//! @d general_macro=0 {preface to a macro defined with a parameter list}
//! @d primary_macro=1 {preface to a macro with a \&{primary} parameter}
//! @d secondary_macro=2 {preface to a macro with a \&{secondary} parameter}
//! @d tertiary_macro=3 {preface to a macro with a \&{tertiary} parameter}
//! @d expr_macro=4 {preface to a macro with an undelimited \&{expr} parameter}
//! @d of_macro=5 {preface to a macro with
//!   undelimited `\&{expr} |x| \&{of}~|y|' parameters}
//! @d suffix_macro=6 {preface to a macro with an undelimited \&{suffix} parameter}
//! @d text_macro=7 {preface to a macro with an undelimited \&{text} parameter}
//!
//! @p procedure delete_mac_ref(@!p:pointer);
//!   {|p| points to the reference count of a macro list that is
//!     losing one reference}
//! begin if ref_count(p)=null then flush_token_list(p)
//! else decr(ref_count(p));
//! end;
//!
//! @ The following subroutine displays a macro, given a pointer to its
//! reference count.
//!
//! @p @t\4@>@<Declare the procedure called |print_cmd_mod|@>@;
//! procedure show_macro(@!p:pointer;@!q,@!l:integer);
//! label exit;
//! var @!r:pointer; {temporary storage}
//! begin p:=link(p); {bypass the reference count}
//! while info(p)>text_macro do
//!   begin r:=link(p); link(p):=null;
//!   show_token_list(p,null,l,0); link(p):=r; p:=r;
//!   if l>0 then l:=l-tally@+else return;
//!   end; {control printing of `\.{ETC.}'}
//! @.ETC@>
//! tally:=0;
//! case info(p) of
//! general_macro:print("->");
//! @.->@>
//! primary_macro,secondary_macro,tertiary_macro:begin print_char("<");
//!   print_cmd_mod(param_type,info(p)); print(">->");
//!   end;
//! expr_macro:print("<expr>->");
//! of_macro:print("<expr>of<primary>->");
//! suffix_macro:print("<suffix>->");
//! text_macro:print("<text>->");
//! end; {there are no other cases}
//! show_token_list(link(p),q,l-tally,0);
//! exit:end;
//!
//! @* \[15] Data structures for variables.
//! The variables of \MF\ programs can be simple, like `\.x', or they can
//! combine the structural properties of arrays and records, like `\.{x20a.b}'.
//! A \MF\ user assigns a type to a variable like \.{x20a.b} by saying, for
//! example, `\.{boolean} \.{x[]a.b}'. It's time for us to study how such
//! things are represented inside of the computer.
//!
//! Each variable value occupies two consecutive words, either in a two-word
//! node called a value node, or as a two-word subfield of a larger node.  One
//! of those two words is called the |value| field; it is an integer,
//! containing either a |scaled| numeric value or the representation of some
//! other type of quantity. (It might also be subdivided into halfwords, in
//! which case it is referred to by other names instead of |value|.) The other
//! word is broken into subfields called |type|, |name_type|, and |link|.  The
//! |type| field is a quarterword that specifies the variable's type, and
//! |name_type| is a quarterword from which \MF\ can reconstruct the
//! variable's name (sometimes by using the |link| field as well).  Thus, only
//! 1.25 words are actually devoted to the value itself; the other
//! three-quarters of a word are overhead, but they aren't wasted because they
//! allow \MF\ to deal with sparse arrays and to provide meaningful diagnostics.
//!
//! In this section we shall be concerned only with the structural aspects of
//! variables, not their values. Later parts of the program will change the
//! |type| and |value| fields, but we shall treat those fields as black boxes
//! whose contents should not be touched.
//!
//! However, if the |type| field is |structured|, there is no |value| field,
//! and the second word is broken into two pointer fields called |attr_head|
//! and |subscr_head|. Those fields point to additional nodes that
//! contain structural information, as we shall see.
//!
//! @d subscr_head_loc(#) == #+1 {where |value|, |subscr_head|, and |attr_head| are}
//! @d attr_head(#) == info(subscr_head_loc(#)) {pointer to attribute info}
//! @d subscr_head(#) == link(subscr_head_loc(#)) {pointer to subscript info}
//! @d value_node_size=2 {the number of words in a value node}
//!
//! @ An attribute node is three words long. Two of these words contain |type|
//! and |value| fields as described above, and the third word contains
//! additional information:  There is an |attr_loc| field, which contains the
//! hash address of the token that names this attribute; and there's also a
//! |parent| field, which points to the value node of |structured| type at the
//! next higher level (i.e., at the level to which this attribute is
//! subsidiary).  The |name_type| in an attribute node is `|attr|'.  The
//! |link| field points to the next attribute with the same parent; these are
//! arranged in increasing order, so that |attr_loc(link(p))>attr_loc(p)|. The
//! final attribute node links to the constant |end_attr|, whose |attr_loc|
//! field is greater than any legal hash address. The |attr_head| in the
//! parent points to a node whose |name_type| is |structured_root|; this
//! node represents the null attribute, i.e., the variable that is relevant
//! when no attributes are attached to the parent. The |attr_head| node
//! has the fields of either
//! a value node, a subscript node, or an attribute node, depending on what
//! the parent would be if it were not structured; but the subscript and
//! attribute fields are ignored, so it effectively contains only the data of
//! a value node. The |link| field in this special node points to an attribute
//! node whose |attr_loc| field is zero; the latter node represents a collective
//! subscript `\.{[]}' attached to the parent, and its |link| field points to
//! the first non-special attribute node (or to |end_attr| if there are none).
//!
//! A subscript node likewise occupies three words, with |type| and |value| fields
//! plus extra information; its |name_type| is |subscr|. In this case the
//! third word is called the |subscript| field, which is a |scaled| integer.
//! The |link| field points to the subscript node with the next larger
//! subscript, if any; otherwise the |link| points to the attribute node
//! for collective subscripts at this level. We have seen that the latter node
//! contains an upward pointer, so that the parent can be deduced.
//!
//! The |name_type| in a parent-less value node is |root|, and the |link|
//! is the hash address of the token that names this value.
//!
//! In other words, variables have a hierarchical structure that includes
//! enough threads running around so that the program is able to move easily
//! between siblings, parents, and children. An example should be helpful:
//! (The reader is advised to draw a picture while reading the following
//! description, since that will help to firm up the ideas.)
//! Suppose that `\.x' and `\.{x.a}' and `\.{x[]b}' and `\.{x5}'
//! and `\.{x20b}' have been mentioned in a user's program, where
//! \.{x[]b} has been declared to be of \&{boolean} type. Let |h(x)|, |h(a)|,
//! and |h(b)| be the hash addresses of \.x, \.a, and~\.b. Then
//! |eq_type(h(x))=tag_token| and |equiv(h(x))=p|, where |p|~is a two-word value
//! node with |name_type(p)=root| and |link(p)=h(x)|. We have |type(p)=structured|,
//! |attr_head(p)=q|, and |subscr_head(p)=r|, where |q| points to a value
//! node and |r| to a subscript node. (Are you still following this? Use
//! a pencil to draw a diagram.) The lone variable `\.x' is represented by
//! |type(q)| and |value(q)|; furthermore
//! |name_type(q)=structured_root| and |link(q)=q1|, where |q1| points
//! to an attribute node representing `\.{x[]}'. Thus |name_type(q1)=attr|,
//! |attr_loc(q1)=collective_subscript=0|, |parent(q1)=p|,
//! |type(q1)=structured|, |attr_head(q1)=qq|, and |subscr_head(q1)=qq1|;
//! |qq| is a three-word ``attribute-as-value'' node with |type(qq)=numeric_type|
//! (assuming that \.{x5} is numeric, because |qq| represents `\.{x[]}'
//! with no further attributes), |name_type(qq)=structured_root|,
//! |attr_loc(qq)=0|, |parent(qq)=p|, and
//! |link(qq)=qq1|. (Now pay attention to the next part.) Node |qq1| is
//! an attribute node representing `\.{x[][]}', which has never yet
//! occurred; its |type| field is |undefined|, and its |value| field is
//! undefined. We have |name_type(qq1)=attr|, |attr_loc(qq1)=collective_subscript|,
//! |parent(qq1)=q1|, and |link(qq1)=qq2|. Since |qq2| represents
//! `\.{x[]b}', |type(qq2)=unknown_boolean|; also |attr_loc(qq2)=h(b)|,
//! |parent(qq2)=q1|, |name_type(qq2)=attr|, |link(qq2)=end_attr|.
//! (Maybe colored lines will help untangle your picture.)
//!  Node |r| is a subscript node with |type| and |value|
//! representing `\.{x5}'; |name_type(r)=subscr|, |subscript(r)=5.0|,
//! and |link(r)=r1| is another subscript node. To complete the picture,
//! see if you can guess what |link(r1)| is; give up? It's~|q1|.
//! Furthermore |subscript(r1)=20.0|, |name_type(r1)=subscr|,
//! |type(r1)=structured|, |attr_head(r1)=qqq|, |subscr_head(r1)=qqq1|,
//! and we finish things off with three more nodes
//! |qqq|, |qqq1|, and |qqq2| hung onto~|r1|. (Perhaps you should start again
//! with a larger sheet of paper.) The value of variable `\.{x20b}'
//! appears in node~|qqq2=link(qqq1)|, as you can well imagine.
//! Similarly, the value of `\.{x.a}' appears in node |q2=link(q1)|, where
//! |attr_loc(q2)=h(a)| and |parent(q2)=p|.
//!
//! If the example in the previous paragraph doesn't make things crystal
//! clear, a glance at some of the simpler subroutines below will reveal how
//! things work out in practice.
//!
//! The only really unusual thing about these conventions is the use of
//! collective subscript attributes. The idea is to avoid repeating a lot of
//! type information when many elements of an array are identical macros
//! (for which distinct values need not be stored) or when they don't have
//! all of the possible attributes. Branches of the structure below collective
//! subscript attributes do not carry actual values except for macro identifiers;
//! branches of the structure below subscript nodes do not carry significant
//! information in their collective subscript attributes.
//!
//! @d attr_loc_loc(#)==#+2 {where the |attr_loc| and |parent| fields are}
//! @d attr_loc(#)==info(attr_loc_loc(#)) {hash address of this attribute}
//! @d parent(#)==link(attr_loc_loc(#)) {pointer to |structured| variable}
//! @d subscript_loc(#)==#+2 {where the |subscript| field lives}
//! @d subscript(#)==mem[subscript_loc(#)].sc {subscript of this variable}
//! @d attr_node_size=3 {the number of words in an attribute node}
//! @d subscr_node_size=3 {the number of words in a subscript node}
//! @d collective_subscript=0 {code for the attribute `\.{[]}'}
//!
//! @<Initialize table...@>=
//! attr_loc(end_attr):=hash_end+1; parent(end_attr):=null;
//!
//! @ Variables of type \&{pair} will have values that point to four-word
//! nodes containing two numeric values. The first of these values has
//! |name_type=x_part_sector| and the second has |name_type=y_part_sector|;
//! the |link| in the first points back to the node whose |value| points
//! to this four-word node.
//!
//! Variables of type \&{transform} are similar, but in this case their
//! |value| points to a 12-word node containing six values, identified by
//! |x_part_sector|, |y_part_sector|, |xx_part_sector|, |xy_part_sector|,
//! |yx_part_sector|, and |yy_part_sector|.
//!
//! When an entire structured variable is saved, the |root| indication
//! is temporarily replaced by |saved_root|.
//!
//! Some variables have no name; they just are used for temporary storage
//! while expressions are being evaluated. We call them {\sl capsules}.
//!
//! @d x_part_loc(#)==# {where the \&{xpart} is found in a pair or transform node}
//! @d y_part_loc(#)==#+2 {where the \&{ypart} is found in a pair or transform node}
//! @d xx_part_loc(#)==#+4 {where the \&{xxpart} is found in a transform node}
//! @d xy_part_loc(#)==#+6 {where the \&{xypart} is found in a transform node}
//! @d yx_part_loc(#)==#+8 {where the \&{yxpart} is found in a transform node}
//! @d yy_part_loc(#)==#+10 {where the \&{yypart} is found in a transform node}
//! @#
//! @d pair_node_size=4 {the number of words in a pair node}
//! @d transform_node_size=12 {the number of words in a transform node}
//!
//! @<Glob...@>=
//! @!big_node_size:array[transform_type..pair_type] of small_number;
//!
//! @ The |big_node_size| array simply contains two constants that \MF\
//! occasionally needs to know.
//!
//! @<Set init...@>=
//! big_node_size[transform_type]:=transform_node_size;
//! big_node_size[pair_type]:=pair_node_size;
//!
//! @ If |type(p)=pair_type| or |transform_type| and if |value(p)=null|, the
//! procedure call |init_big_node(p)| will allocate a pair or transform node
//! for~|p|.  The individual parts of such nodes are initially of type
//! |independent|.
//!
//! @p procedure init_big_node(@!p:pointer);
//! var @!q:pointer; {the new node}
//! @!s:small_number; {its size}
//! begin s:=big_node_size[type(p)]; q:=get_node(s);
//! repeat s:=s-2; @<Make variable |q+s| newly independent@>;
//! name_type(q+s):=half(s)+x_part_sector; link(q+s):=null;
//! until s=0;
//! link(q):=p; value(p):=q;
//! end;
//!
//! @ The |id_transform| function creates a capsule for the
//! identity transformation.
//!
//! @p function id_transform:pointer;
//! var @!p,@!q,@!r:pointer; {list manipulation registers}
//! begin p:=get_node(value_node_size); type(p):=transform_type;
//! name_type(p):=capsule; value(p):=null; init_big_node(p); q:=value(p);
//! r:=q+transform_node_size;
//! repeat r:=r-2;
//! type(r):=known; value(r):=0;
//! until r=q;
//! value(xx_part_loc(q)):=unity; value(yy_part_loc(q)):=unity;
//! id_transform:=p;
//! end;
//!
//! @ Tokens are of type |tag_token| when they first appear, but they point
//! to |null| until they are first used as the root of a variable.
//! The following subroutine establishes the root node on such grand occasions.
//!
//! @p procedure new_root(@!x:pointer);
//! var @!p:pointer; {the new node}
//! begin p:=get_node(value_node_size); type(p):=undefined; name_type(p):=root;
//! link(p):=x; equiv(x):=p;
//! end;
//!
//! @ These conventions for variable representation are illustrated by the
//! |print_variable_name| routine, which displays the full name of a
//! variable given only a pointer to its two-word value packet.
//!
//! @p procedure print_variable_name(@!p:pointer);
//! label found,exit;
//! var @!q:pointer; {a token list that will name the variable's suffix}
//! @!r:pointer; {temporary for token list creation}
//! begin while name_type(p)>=x_part_sector do
//!   @<Preface the output with a part specifier; |return| in the
//!     case of a capsule@>;
//! q:=null;
//! while name_type(p)>saved_root do
//!   @<Ascend one level, pushing a token onto list |q|
//!    and replacing |p| by its parent@>;
//! r:=get_avail; info(r):=link(p); link(r):=q;
//! if name_type(p)=saved_root then print("(SAVED)");
//! @.SAVED@>
//! show_token_list(r,null,el_gordo,tally); flush_token_list(r);
//! exit:end;
//!
//! @ @<Ascend one level, pushing a token onto list |q|...@>=
//! begin if name_type(p)=subscr then
//!   begin r:=new_num_tok(subscript(p));
//!   repeat p:=link(p);
//!   until name_type(p)=attr;
//!   end
//! else if name_type(p)=structured_root then
//!     begin p:=link(p); goto found;
//!     end
//! else  begin if name_type(p)<>attr then confusion("var");
//! @:this can't happen var}{\quad var@>
//!   r:=get_avail; info(r):=attr_loc(p);
//!   end;
//! link(r):=q; q:=r;
//! found:  p:=parent(p);
//! end
//!
//! @ @<Preface the output with a part specifier...@>=
//! begin case name_type(p) of
//! x_part_sector: print_char("x");
//! y_part_sector: print_char("y");
//! xx_part_sector: print("xx");
//! xy_part_sector: print("xy");
//! yx_part_sector: print("yx");
//! yy_part_sector: print("yy");
//! capsule: begin print("%CAPSULE"); print_int(p-null); return;
//! @.CAPSULE@>
//!   end;
//! end; {there are no other cases}
//! print("part "); p:=link(p-2*(name_type(p)-x_part_sector));
//! end
//!
//! @ The |interesting| function returns |true| if a given variable is not
//! in a capsule, or if the user wants to trace capsules.
//!
//! @p function interesting(@!p:pointer):boolean;
//! var @!t:small_number; {a |name_type|}
//! begin if internal[tracing_capsules]>0 then interesting:=true
//! else  begin t:=name_type(p);
//!   if t>=x_part_sector then if t<>capsule then
//!     t:=name_type(link(p-2*(t-x_part_sector)));
//!   interesting:=(t<>capsule);
//!   end;
//! end;
//!
//! @ Now here is a subroutine that converts an unstructured type into an
//! equivalent structured type, by inserting a |structured| node that is
//! capable of growing. This operation is done only when |name_type(p)=root|,
//! |subscr|, or |attr|.
//!
//! The procedure returns a pointer to the new node that has taken node~|p|'s
//! place in the structure. Node~|p| itself does not move, nor are its
//! |value| or |type| fields changed in any way.
//!
//! @p function new_structure(@!p:pointer):pointer;
//! var @!q,@!r:pointer; {list manipulation registers}
//! begin case name_type(p) of
//! root: begin q:=link(p); r:=get_node(value_node_size); equiv(q):=r;
//!   end;
//! subscr: @<Link a new subscript node |r| in place of node |p|@>;
//! attr: @<Link a new attribute node |r| in place of node |p|@>;
//! othercases confusion("struct")
//! @:this can't happen struct}{\quad struct@>
//! endcases;@/
//! link(r):=link(p); type(r):=structured; name_type(r):=name_type(p);
//! attr_head(r):=p; name_type(p):=structured_root;@/
//! q:=get_node(attr_node_size); link(p):=q; subscr_head(r):=q;
//! parent(q):=r; type(q):=undefined; name_type(q):=attr; link(q):=end_attr;
//! attr_loc(q):=collective_subscript; new_structure:=r;
//! end;
//!
//! @ @<Link a new subscript node |r| in place of node |p|@>=
//! begin q:=p;
//! repeat q:=link(q);
//! until name_type(q)=attr;
//! q:=parent(q); r:=subscr_head_loc(q); {|link(r)=subscr_head(q)|}
//! repeat q:=r; r:=link(r);
//! until r=p;
//! r:=get_node(subscr_node_size);
//! link(q):=r; subscript(r):=subscript(p);
//! end
//!
//! @ If the attribute is |collective_subscript|, there are two pointers to
//! node~|p|, so we must change both of them.
//!
//! @<Link a new attribute node |r| in place of node |p|@>=
//! begin q:=parent(p); r:=attr_head(q);
//! repeat q:=r; r:=link(r);
//! until r=p;
//! r:=get_node(attr_node_size); link(q):=r;@/
//! mem[attr_loc_loc(r)]:=mem[attr_loc_loc(p)]; {copy |attr_loc| and |parent|}
//! if attr_loc(p)=collective_subscript then
//!   begin q:=subscr_head_loc(parent(p));
//!   while link(q)<>p do q:=link(q);
//!   link(q):=r;
//!   end;
//! end
//!
//! @ The |find_variable| routine is given a pointer~|t| to a nonempty token
//! list of suffixes; it returns a pointer to the corresponding two-word
//! value. For example, if |t| points to token \.x followed by a numeric
//! token containing the value~7, |find_variable| finds where the value of
//! \.{x7} is stored in memory. This may seem a simple task, and it
//! usually is, except when \.{x7} has never been referenced before.
//! Indeed, \.x may never have even been subscripted before; complexities
//! arise with respect to updating the collective subscript information.
//!
//! If a macro type is detected anywhere along path~|t|, or if the first
//! item on |t| isn't a |tag_token|, the value |null| is returned.
//! Otherwise |p| will be a non-null pointer to a node such that
//! |undefined<type(p)<structured|.
//!
//! @d abort_find==begin find_variable:=null; return;@+end
//!
//! @p function find_variable(@!t:pointer):pointer;
//! label exit;
//! var @!p,@!q,@!r,@!s:pointer; {nodes in the ``value'' line}
//! @!pp,@!qq,@!rr,@!ss:pointer; {nodes in the ``collective'' line}
//! @!n:integer; {subscript or attribute}
//! @!save_word:memory_word; {temporary storage for a word of |mem|}
//! @^inner loop@>
//! begin p:=info(t); t:=link(t);
//! if eq_type(p) mod outer_tag<>tag_token then abort_find;
//! if equiv(p)=null then new_root(p);
//! p:=equiv(p); pp:=p;
//! while t<>null do
//!   begin @<Make sure that both nodes |p| and |pp| are of |structured| type@>;
//!   if t<hi_mem_min then
//!     @<Descend one level for the subscript |value(t)|@>
//!   else @<Descend one level for the attribute |info(t)|@>;
//!   t:=link(t);
//!   end;
//! if type(pp)>=structured then
//!   if type(pp)=structured then pp:=attr_head(pp)@+else abort_find;
//! if type(p)=structured then p:=attr_head(p);
//! if type(p)=undefined then
//!   begin if type(pp)=undefined then
//!     begin type(pp):=numeric_type; value(pp):=null;
//!     end;
//!   type(p):=type(pp); value(p):=null;
//!   end;
//! find_variable:=p;
//! exit:end;
//!
//! @ Although |pp| and |p| begin together, they diverge when a subscript occurs;
//! |pp|~stays in the collective line while |p|~goes through actual subscript
//! values.
//!
//! @<Make sure that both nodes |p| and |pp|...@>=
//! if type(pp)<>structured then
//!   begin if type(pp)>structured then abort_find;
//!   ss:=new_structure(pp);
//!   if p=pp then p:=ss;
//!   pp:=ss;
//!   end; {now |type(pp)=structured|}
//! if type(p)<>structured then {it cannot be |>structured|}
//!   p:=new_structure(p) {now |type(p)=structured|}
//!
//! @ We want this part of the program to be reasonably fast, in case there are
//! @^inner loop@>
//! lots of subscripts at the same level of the data structure. Therefore
//! we store an ``infinite'' value in the word that appears at the end of the
//! subscript list, even though that word isn't part of a subscript node.
//!
//! @<Descend one level for the subscript |value(t)|@>=
//! begin n:=value(t);
//! pp:=link(attr_head(pp)); {now |attr_loc(pp)=collective_subscript|}
//! q:=link(attr_head(p)); save_word:=mem[subscript_loc(q)];
//! subscript(q):=el_gordo; s:=subscr_head_loc(p); {|link(s)=subscr_head(p)|}
//! repeat r:=s; s:=link(s);
//! until n<=subscript(s);
//! if n=subscript(s) then p:=s
//! else  begin p:=get_node(subscr_node_size); link(r):=p; link(p):=s;
//!   subscript(p):=n; name_type(p):=subscr; type(p):=undefined;
//!   end;
//! mem[subscript_loc(q)]:=save_word;
//! end
//!
//! @ @<Descend one level for the attribute |info(t)|@>=
//! begin n:=info(t);
//! ss:=attr_head(pp);
//! repeat rr:=ss; ss:=link(ss);
//! until n<=attr_loc(ss);
//! if n<attr_loc(ss) then
//!   begin qq:=get_node(attr_node_size); link(rr):=qq; link(qq):=ss;
//!   attr_loc(qq):=n; name_type(qq):=attr; type(qq):=undefined;
//!   parent(qq):=pp; ss:=qq;
//!   end;
//! if p=pp then
//!   begin p:=ss; pp:=ss;
//!   end
//! else  begin pp:=ss; s:=attr_head(p);
//!   repeat r:=s; s:=link(s);
//!   until n<=attr_loc(s);
//!   if n=attr_loc(s) then p:=s
//!   else  begin q:=get_node(attr_node_size); link(r):=q; link(q):=s;
//!     attr_loc(q):=n; name_type(q):=attr; type(q):=undefined;
//!     parent(q):=p; p:=q;
//!     end;
//!   end;
//! end
//!
//! @ Variables lose their former values when they appear in a type declaration,
//! or when they are defined to be macros or \&{let} equal to something else.
//! A subroutine will be defined later that recycles the storage associated
//! with any particular |type| or |value|; our goal now is to study a higher
//! level process called |flush_variable|, which selectively frees parts of a
//! variable structure.
//!
//! This routine has some complexity because of examples such as
//! `\hbox{\tt numeric x[]a[]b}',
//! which recycles all variables of the form \.{x[i]a[j]b} (and no others), while
//! `\hbox{\tt vardef x[]a[]=...}'
//! discards all variables of the form \.{x[i]a[j]} followed by an arbitrary
//! suffix, except for the collective node \.{x[]a[]} itself. The obvious way
//! to handle such examples is to use recursion; so that's what we~do.
//! @^recursion@>
//!
//! Parameter |p| points to the root information of the variable;
//! parameter |t| points to a list of one-word nodes that represent
//! suffixes, with |info=collective_subscript| for subscripts.
//!
//! @p @t\4@>@<Declare subroutines for printing expressions@>@;@/
//! @t\4@>@<Declare basic dependency-list subroutines@>@;
//! @t\4@>@<Declare the recycling subroutines@>@;
//! @t\4@>@<Declare the procedure called |flush_cur_exp|@>@;
//! @t\4@>@<Declare the procedure called |flush_below_variable|@>@;
//! procedure flush_variable(@!p,@!t:pointer;@!discard_suffixes:boolean);
//! label exit;
//! var @!q,@!r:pointer; {list manipulation}
//! @!n:halfword; {attribute to match}
//! begin while t<>null do
//!   begin if type(p)<>structured then return;
//!   n:=info(t); t:=link(t);
//!   if n=collective_subscript then
//!     begin r:=subscr_head_loc(p); q:=link(r); {|q=subscr_head(p)|}
//!     while name_type(q)=subscr do
//!       begin flush_variable(q,t,discard_suffixes);
//!       if t=null then
//!         if type(q)=structured then r:=q
//!         else  begin link(r):=link(q); free_node(q,subscr_node_size);
//!           end
//!       else r:=q;
//!       q:=link(r);
//!       end;
//!     end;
//!   p:=attr_head(p);
//!   repeat r:=p; p:=link(p);
//!   until attr_loc(p)>=n;
//!   if attr_loc(p)<>n then return;
//!   end;
//! if discard_suffixes then flush_below_variable(p)
//! else  begin if type(p)=structured then p:=attr_head(p);
//!   recycle_value(p);
//!   end;
//! exit:end;
//!
//! @ The next procedure is simpler; it wipes out everything but |p| itself,
//! which becomes undefined.
//!
//! @<Declare the procedure called |flush_below_variable|@>=
//! procedure flush_below_variable(@!p:pointer);
//! var @!q,@!r:pointer; {list manipulation registers}
//! begin if type(p)<>structured then
//!   recycle_value(p) {this sets |type(p)=undefined|}
//! else  begin q:=subscr_head(p);
//!   while name_type(q)=subscr do
//!     begin flush_below_variable(q); r:=q; q:=link(q);
//!     free_node(r,subscr_node_size);
//!     end;
//!   r:=attr_head(p); q:=link(r); recycle_value(r);
//!   if name_type(p)<=saved_root then free_node(r,value_node_size)
//!   else free_node(r,subscr_node_size);
//!     {we assume that |subscr_node_size=attr_node_size|}
//!   repeat flush_below_variable(q); r:=q; q:=link(q); free_node(r,attr_node_size);
//!   until q=end_attr;
//!   type(p):=undefined;
//!   end;
//! end;
//!
//! @ Just before assigning a new value to a variable, we will recycle the
//! old value and make the old value undefined. The |und_type| routine
//! determines what type of undefined value should be given, based on
//! the current type before recycling.
//!
//! @p function und_type(@!p:pointer):small_number;
//! begin case type(p) of
//! undefined,vacuous:und_type:=undefined;
//! boolean_type,unknown_boolean:und_type:=unknown_boolean;
//! string_type,unknown_string:und_type:=unknown_string;
//! pen_type,unknown_pen,future_pen:und_type:=unknown_pen;
//! path_type,unknown_path:und_type:=unknown_path;
//! picture_type,unknown_picture:und_type:=unknown_picture;
//! transform_type,pair_type,numeric_type:und_type:=type(p);
//! known,dependent,proto_dependent,independent:und_type:=numeric_type;
//! end; {there are no other cases}
//! end;
//!
//! @ The |clear_symbol| routine is used when we want to redefine the equivalent
//! of a symbolic token. It must remove any variable structure or macro
//! definition that is currently attached to that symbol. If the |saving|
//! parameter is true, a subsidiary structure is saved instead of destroyed.
//!
//! @p procedure clear_symbol(@!p:pointer;@!saving:boolean);
//! var @!q:pointer; {|equiv(p)|}
//! begin q:=equiv(p);
//! case eq_type(p) mod outer_tag of
//! defined_macro,secondary_primary_macro,tertiary_secondary_macro,
//!  expression_tertiary_macro: if not saving then delete_mac_ref(q);
//! tag_token:if q<>null then
//!   if saving then name_type(q):=saved_root
//!   else  begin flush_below_variable(q); free_node(q,value_node_size);
//!     end;@;
//! othercases do_nothing
//! endcases;@/
//! eqtb[p]:=eqtb[frozen_undefined];
//! end;
//!
//! @* \[16] Saving and restoring equivalents.
//! The nested structure provided by \&{begingroup} and \&{endgroup}
//! allows |eqtb| entries to be saved and restored, so that temporary changes
//! can be made without difficulty.  When the user requests a current value to
//! be saved, \MF\ puts that value into its ``save stack.'' An appearance of
//! \&{endgroup} ultimately causes the old values to be removed from the save
//! stack and put back in their former places.
//!
//! The save stack is a linked list containing three kinds of entries,
//! distinguished by their |info| fields. If |p| points to a saved item,
//! then
//!
//! \smallskip\hang
//! |info(p)=0| stands for a group boundary; each \&{begingroup} contributes
//! such an item to the save stack and each \&{endgroup} cuts back the stack
//! until the most recent such entry has been removed.
//!
//! \smallskip\hang
//! |info(p)=q|, where |1<=q<=hash_end|, means that |mem[p+1]| holds the former
//! contents of |eqtb[q]|. Such save stack entries are generated by \&{save}
//! commands.
//!
//! \smallskip\hang
//! |info(p)=hash_end+q|, where |q>0|, means that |value(p)| is a |scaled|
//! integer to be restored to internal parameter number~|q|. Such entries
//! are generated by \&{interim} commands.
//!
//! \smallskip\noindent
//! The global variable |save_ptr| points to the top item on the save stack.
//!
//! @d save_node_size=2 {number of words per non-boundary save-stack node}
//! @d saved_equiv(#)==mem[#+1].hh {where an |eqtb| entry gets saved}
//! @d save_boundary_item(#)==begin #:=get_avail; info(#):=0;
//!   link(#):=save_ptr; save_ptr:=#;
//!   end
//!
//! @<Glob...@>=@!save_ptr:pointer; {the most recently saved item}
//!
//! @ @<Set init...@>=save_ptr:=null;
//!
//! @ The |save_variable| routine is given a hash address |q|; it salts this
//! address away in the save stack, together with its current equivalent,
//! then makes token~|q| behave as though it were brand new.
//!
//! Nothing is stacked when |save_ptr=null|, however; there's no way to remove
//! things from the stack when the program is not inside a group, so there's
//! no point in wasting the space.
//!
//! @p procedure save_variable(@!q:pointer);
//! var @!p:pointer; {temporary register}
//! begin if save_ptr<>null then
//!   begin p:=get_node(save_node_size); info(p):=q; link(p):=save_ptr;
//!   saved_equiv(p):=eqtb[q]; save_ptr:=p;
//!   end;
//! clear_symbol(q,(save_ptr<>null));
//! end;
//!
//! @ Similarly, |save_internal| is given the location |q| of an internal
//! quantity like |tracing_pens|. It creates a save stack entry of the
//! third kind.
//!
//! @p procedure save_internal(@!q:halfword);
//! var @!p:pointer; {new item for the save stack}
//! begin if save_ptr<>null then
//!   begin p:=get_node(save_node_size); info(p):=hash_end+q;
//!   link(p):=save_ptr; value(p):=internal[q]; save_ptr:=p;
//!   end;
//! end;
//!
//! @ At the end of a group, the |unsave| routine restores all of the saved
//! equivalents in reverse order. This routine will be called only when there
//! is at least one boundary item on the save stack.
//!
//! @p procedure unsave;
//! var @!q:pointer; {index to saved item}
//! @!p:pointer; {temporary register}
//! begin while info(save_ptr)<>0 do
//!   begin q:=info(save_ptr);
//!   if q>hash_end then
//!     begin if internal[tracing_restores]>0 then
//!       begin begin_diagnostic; print_nl("{restoring ");
//!       slow_print(int_name[q-(hash_end)]); print_char("=");
//!       print_scaled(value(save_ptr)); print_char("}");
//!       end_diagnostic(false);
//!       end;
//!     internal[q-(hash_end)]:=value(save_ptr);
//!     end
//!   else  begin if internal[tracing_restores]>0 then
//!       begin begin_diagnostic; print_nl("{restoring ");
//!       slow_print(text(q)); print_char("}");
//!       end_diagnostic(false);
//!       end;
//!     clear_symbol(q,false);
//!     eqtb[q]:=saved_equiv(save_ptr);
//!     if eq_type(q) mod outer_tag=tag_token then
//!       begin p:=equiv(q);
//!       if p<>null then name_type(p):=root;
//!       end;
//!     end;
//!   p:=link(save_ptr); free_node(save_ptr,save_node_size); save_ptr:=p;
//!   end;
//! p:=link(save_ptr); free_avail(save_ptr); save_ptr:=p;
//! end;
//!
//! @* \[17] Data structures for paths.
//! When a \MF\ user specifies a path, \MF\ will create a list of knots
//! and control points for the associated cubic spline curves. If the
//! knots are $z_0$, $z_1$, \dots, $z_n$, there are control points
//! $z_k^+$ and $z_{k+1}^-$ such that the cubic splines between knots
//! $z_k$ and $z_{k+1}$ are defined by B\'ezier's formula
//! @:Bezier}{B\'ezier, Pierre Etienne@>
//! $$\eqalign{z(t)&=B(z_k,z_k^+,z_{k+1}^-,z_{k+1};t)\cr
//! &=(1-t)^3z_k+3(1-t)^2tz_k^++3(1-t)t^2z_{k+1}^-+t^3z_{k+1}\cr}$$
//! for |0<=t<=1|.
//!
//! There is a 7-word node for each knot $z_k$, containing one word of
//! control information and six words for the |x| and |y| coordinates
//! of $z_k^-$ and $z_k$ and~$z_k^+$. The control information appears
//! in the |left_type| and |right_type| fields, which each occupy
//! a quarter of the first word in the node; they specify properties
//! of the curve as it enters and leaves the knot. There's also a
//! halfword |link| field, which points to the following knot.
//!
//! If the path is a closed contour, knots 0 and |n| are identical;
//! i.e., the |link| in knot |n-1| points to knot~0. But if the path
//! is not closed, the |left_type| of knot~0 and the |right_type| of knot~|n|
//! are equal to |endpoint|. In the latter case the |link| in knot~|n| points
//! to knot~0, and the control points $z_0^-$ and $z_n^+$ are not used.
//!
//! @d left_type(#) == mem[#].hh.b0 {characterizes the path entering this knot}
//! @d right_type(#) == mem[#].hh.b1 {characterizes the path leaving this knot}
//! @d endpoint=0 {|left_type| at path beginning and |right_type| at path end}
//! @d x_coord(#) == mem[#+1].sc {the |x| coordinate of this knot}
//! @d y_coord(#) == mem[#+2].sc {the |y| coordinate of this knot}
//! @d left_x(#) == mem[#+3].sc {the |x| coordinate of previous control point}
//! @d left_y(#) == mem[#+4].sc {the |y| coordinate of previous control point}
//! @d right_x(#) == mem[#+5].sc {the |x| coordinate of next control point}
//! @d right_y(#) == mem[#+6].sc {the |y| coordinate of next control point}
//! @d knot_node_size=7 {number of words in a knot node}
//!
//! @ Before the B\'ezier control points have been calculated, the memory
//! space they will ultimately occupy is taken up by information that can be
//! used to compute them. There are four cases:
//!
//! \yskip
//! \textindent{$\bullet$} If |right_type=open|, the curve should leave
//! the knot in the same direction it entered; \MF\ will figure out a
//! suitable direction.
//!
//! \yskip
//! \textindent{$\bullet$} If |right_type=curl|, the curve should leave the
//! knot in a direction depending on the angle at which it enters the next
//! knot and on the curl parameter stored in |right_curl|.
//!
//! \yskip
//! \textindent{$\bullet$} If |right_type=given|, the curve should leave the
//! knot in a nonzero direction stored as an |angle| in |right_given|.
//!
//! \yskip
//! \textindent{$\bullet$} If |right_type=explicit|, the B\'ezier control
//! point for leaving this knot has already been computed; it is in the
//! |right_x| and |right_y| fields.
//!
//! \yskip\noindent
//! The rules for |left_type| are similar, but they refer to the curve entering
//! the knot, and to \\{left} fields instead of \\{right} fields.
//!
//! Non-|explicit| control points will be chosen based on ``tension'' parameters
//! in the |left_tension| and |right_tension| fields. The
//! `\&{atleast}' option is represented by negative tension values.
//! @:at_least_}{\&{atleast} primitive@>
//!
//! For example, the \MF\ path specification
//! $$\.{z0..z1..tension atleast 1..\{curl 2\}z2..z3\{-1,-2\}..tension
//!   3 and 4..p},$$
//! where \.p is the path `\.{z4..controls z45 and z54..z5}', will be represented
//! by the six knots
//! \def\lodash{\hbox to 1.1em{\thinspace\hrulefill\thinspace}}
//! $$\vbox{\halign{#\hfil&&\qquad#\hfil\cr
//! |left_type|&\\{left} info&|x_coord,y_coord|&|right_type|&\\{right} info\cr
//! \noalign{\yskip}
//! |endpoint|&\lodash$,\,$\lodash&$x_0,y_0$&|curl|&$1.0,1.0$\cr
//! |open|&\lodash$,1.0$&$x_1,y_1$&|open|&\lodash$,-1.0$\cr
//! |curl|&$2.0,-1.0$&$x_2,y_2$&|curl|&$2.0,1.0$\cr
//! |given|&$d,1.0$&$x_3,y_3$&|given|&$d,3.0$\cr
//! |open|&\lodash$,4.0$&$x_4,y_4$&|explicit|&$x_{45},y_{45}$\cr
//! |explicit|&$x_{54},y_{54}$&$x_5,y_5$&|endpoint|&\lodash$,\,$\lodash\cr}}$$
//! Here |d| is the |angle| obtained by calling |n_arg(-unity,-two)|.
//! Of course, this example is more complicated than anything a normal user
//! would ever write.
//!
//! These types must satisfy certain restrictions because of the form of \MF's
//! path syntax:
//! (i)~|open| type never appears in the same node together with |endpoint|,
//! |given|, or |curl|.
//! (ii)~The |right_type| of a node is |explicit| if and only if the
//! |left_type| of the following node is |explicit|.
//! (iii)~|endpoint| types occur only at the ends, as mentioned above.
//!
//! @d left_curl==left_x {curl information when entering this knot}
//! @d left_given==left_x {given direction when entering this knot}
//! @d left_tension==left_y {tension information when entering this knot}
//! @d right_curl==right_x {curl information when leaving this knot}
//! @d right_given==right_x {given direction when leaving this knot}
//! @d right_tension==right_y {tension information when leaving this knot}
//! @d explicit=1 {|left_type| or |right_type| when control points are known}
//! @d given=2 {|left_type| or |right_type| when a direction is given}
//! @d curl=3 {|left_type| or |right_type| when a curl is desired}
//! @d open=4 {|left_type| or |right_type| when \MF\ should choose the direction}
//!
//! @ Here is a diagnostic routine that prints a given knot list
//! in symbolic form. It illustrates the conventions discussed above,
//! and checks for anomalies that might arise while \MF\ is being debugged.
//!
//! @<Declare subroutines for printing expressions@>=
//! procedure print_path(@!h:pointer;@!s:str_number;@!nuline:boolean);
//! label done,done1;
//! var @!p,@!q:pointer; {for list traversal}
//! begin print_diagnostic("Path",s,nuline); print_ln;
//! @.Path at line...@>
//! p:=h;
//! repeat q:=link(p);
//! if (p=null)or(q=null) then
//!   begin print_nl("???"); goto done; {this won't happen}
//! @.???@>
//!   end;
//! @<Print information for adjacent knots |p| and |q|@>;
//! p:=q;
//! if (p<>h)or(left_type(h)<>endpoint) then
//!   @<Print two dots, followed by |given| or |curl| if present@>;
//! until p=h;
//! if left_type(h)<>endpoint then print("cycle");
//! done:end_diagnostic(true);
//! end;
//!
//! @ @<Print information for adjacent knots...@>=
//! print_two(x_coord(p),y_coord(p));
//! case right_type(p) of
//! endpoint: begin if left_type(p)=open then print("{open?}"); {can't happen}
//! @.open?@>
//!   if (left_type(q)<>endpoint)or(q<>h) then q:=null; {force an error}
//!   goto done1;
//!   end;
//! explicit: @<Print control points between |p| and |q|, then |goto done1|@>;
//! open: @<Print information for a curve that begins |open|@>;
//! curl,given: @<Print information for a curve that begins |curl| or |given|@>;
//! othercases print("???") {can't happen}
//! @.???@>
//! endcases;@/
//! if left_type(q)<=explicit then print("..control?") {can't happen}
//! @.control?@>
//! else if (right_tension(p)<>unity)or(left_tension(q)<>unity) then
//!   @<Print tension between |p| and |q|@>;
//! done1:
//!
//! @ Since |n_sin_cos| produces |fraction| results, which we will print as if they
//! were |scaled|, the magnitude of a |given| direction vector will be~4096.
//!
//! @<Print two dots...@>=
//! begin print_nl(" ..");
//! if left_type(p)=given then
//!   begin n_sin_cos(left_given(p)); print_char("{");
//!   print_scaled(n_cos); print_char(",");
//!   print_scaled(n_sin); print_char("}");
//!   end
//! else if left_type(p)=curl then
//!   begin print("{curl "); print_scaled(left_curl(p)); print_char("}");
//!   end;
//! end
//!
//! @ @<Print tension between |p| and |q|@>=
//! begin print("..tension ");
//! if right_tension(p)<0 then print("atleast");
//! print_scaled(abs(right_tension(p)));
//! if right_tension(p)<>left_tension(q) then
//!   begin print(" and ");
//!   if left_tension(q)<0 then print("atleast");
//!   print_scaled(abs(left_tension(q)));
//!   end;
//! end
//!
//! @ @<Print control points between |p| and |q|, then |goto done1|@>=
//! begin print("..controls "); print_two(right_x(p),right_y(p)); print(" and ");
//! if left_type(q)<>explicit then print("??") {can't happen}
//! @.??@>
//! else print_two(left_x(q),left_y(q));
//! goto done1;
//! end
//!
//! @ @<Print information for a curve that begins |open|@>=
//! if (left_type(p)<>explicit)and(left_type(p)<>open) then
//!   print("{open?}") {can't happen}
//! @.open?@>
//!
//! @ A curl of 1 is shown explicitly, so that the user sees clearly that
//! \MF's default curl is present.
//!
//! @<Print information for a curve that begins |curl|...@>=
//! begin if left_type(p)=open then print("??"); {can't happen}
//! @.??@>
//! if right_type(p)=curl then
//!   begin print("{curl "); print_scaled(right_curl(p));
//!   end
//! else  begin n_sin_cos(right_given(p)); print_char("{");
//!   print_scaled(n_cos); print_char(","); print_scaled(n_sin);
//!   end;
//! print_char("}");
//! end
//!
//! @ If we want to duplicate a knot node, we can say |copy_knot|:
//!
//! @p function copy_knot(@!p:pointer):pointer;
//! var @!q:pointer; {the copy}
//! @!k:0..knot_node_size-1; {runs through the words of a knot node}
//! begin q:=get_node(knot_node_size);
//! for k:=0 to knot_node_size-1 do mem[q+k]:=mem[p+k];
//! copy_knot:=q;
//! end;
//!
//! @ The |copy_path| routine makes a clone of a given path.
//!
//! @p function copy_path(@!p:pointer):pointer;
//! label exit;
//! var @!q,@!pp,@!qq:pointer; {for list manipulation}
//! begin q:=get_node(knot_node_size); {this will correspond to |p|}
//! qq:=q; pp:=p;
//! loop@+  begin left_type(qq):=left_type(pp);
//!   right_type(qq):=right_type(pp);@/
//!   x_coord(qq):=x_coord(pp); y_coord(qq):=y_coord(pp);@/
//!   left_x(qq):=left_x(pp); left_y(qq):=left_y(pp);@/
//!   right_x(qq):=right_x(pp); right_y(qq):=right_y(pp);@/
//!   if link(pp)=p then
//!     begin link(qq):=q; copy_path:=q; return;
//!     end;
//!   link(qq):=get_node(knot_node_size); qq:=link(qq); pp:=link(pp);
//!   end;
//! exit:end;
//!
//! @ Similarly, there's a way to copy the {\sl reverse\/} of a path. This procedure
//! returns a pointer to the first node of the copy, if the path is a cycle,
//! but to the final node of a non-cyclic copy. The global
//! variable |path_tail| will point to the final node of the original path;
//! this trick makes it easier to implement `\&{doublepath}'.
//!
//! All node types are assumed to be |endpoint| or |explicit| only.
//!
//! @p function htap_ypoc(@!p:pointer):pointer;
//! label exit;
//! var @!q,@!pp,@!qq,@!rr:pointer; {for list manipulation}
//! begin q:=get_node(knot_node_size); {this will correspond to |p|}
//! qq:=q; pp:=p;
//! loop@+  begin right_type(qq):=left_type(pp); left_type(qq):=right_type(pp);@/
//!   x_coord(qq):=x_coord(pp); y_coord(qq):=y_coord(pp);@/
//!   right_x(qq):=left_x(pp); right_y(qq):=left_y(pp);@/
//!   left_x(qq):=right_x(pp); left_y(qq):=right_y(pp);@/
//!   if link(pp)=p then
//!     begin link(q):=qq; path_tail:=pp; htap_ypoc:=q; return;
//!     end;
//!   rr:=get_node(knot_node_size); link(rr):=qq; qq:=rr; pp:=link(pp);
//!   end;
//! exit:end;
//!
//! @ @<Glob...@>=
//! @!path_tail:pointer; {the node that links to the beginning of a path}
//!
//! @ When a cyclic list of knot nodes is no longer needed, it can be recycled by
//! calling the following subroutine.
//!
//! @<Declare the recycling subroutines@>=
//! procedure toss_knot_list(@!p:pointer);
//! var @!q:pointer; {the node being freed}
//! @!r:pointer; {the next node}
//! begin q:=p;
//! repeat r:=link(q); free_node(q,knot_node_size); q:=r;
//! until q=p;
//! end;
//!
//! @* \[18] Choosing control points.
//! Now we must actually delve into one of \MF's more difficult routines,
//! the |make_choices| procedure that chooses angles and control points for
//! the splines of a curve when the user has not specified them explicitly.
//! The parameter to |make_choices| points to a list of knots and
//! path information, as described above.
//!
//! A path decomposes into independent segments at ``breakpoint'' knots,
//! which are knots whose left and right angles are both prespecified in
//! some way (i.e., their |left_type| and |right_type| aren't both open).
//!
//! @p @t\4@>@<Declare the procedure called |solve_choices|@>@;
//! procedure make_choices(@!knots:pointer);
//! label done;
//! var @!h:pointer; {the first breakpoint}
//! @!p,@!q:pointer; {consecutive breakpoints being processed}
//! @<Other local variables for |make_choices|@>@;
//! begin check_arith; {make sure that |arith_error=false|}
//! if internal[tracing_choices]>0 then
//!   print_path(knots,", before choices",true);
//! @<If consecutive knots are equal, join them explicitly@>;
//! @<Find the first breakpoint, |h|, on the path;
//!   insert an artificial breakpoint if the path is an unbroken cycle@>;
//! p:=h;
//! repeat @<Fill in the control points between |p| and the next breakpoint,
//!   then advance |p| to that breakpoint@>;
//! until p=h;
//! if internal[tracing_choices]>0 then
//!   print_path(knots,", after choices",true);
//! if arith_error then @<Report an unexpected problem during the choice-making@>;
//! end;
//!
//! @ @<Report an unexpected problem during the choice...@>=
//! begin print_err("Some number got too big");
//! @.Some number got too big@>
//! help2("The path that I just computed is out of range.")@/
//!   ("So it will probably look funny. Proceed, for a laugh.");
//! put_get_error; arith_error:=false;
//! end
//!
//! @ Two knots in a row with the same coordinates will always be joined
//! by an explicit ``curve'' whose control points are identical with the
//! knots.
//!
//! @<If consecutive knots are equal, join them explicitly@>=
//! p:=knots;
//! repeat q:=link(p);
//! if x_coord(p)=x_coord(q) then if y_coord(p)=y_coord(q) then
//!  if right_type(p)>explicit then
//!   begin right_type(p):=explicit;
//!   if left_type(p)=open then
//!     begin left_type(p):=curl; left_curl(p):=unity;
//!     end;
//!   left_type(q):=explicit;
//!   if right_type(q)=open then
//!     begin right_type(q):=curl; right_curl(q):=unity;
//!     end;
//!   right_x(p):=x_coord(p); left_x(q):=x_coord(p);@/
//!   right_y(p):=y_coord(p); left_y(q):=y_coord(p);
//!   end;
//! p:=q;
//! until p=knots
//!
//! @ If there are no breakpoints, it is necessary to compute the direction
//! angles around an entire cycle. In this case the |left_type| of the first
//! node is temporarily changed to |end_cycle|.
//!
//! @d end_cycle=open+1
//!
//! @<Find the first breakpoint, |h|, on the path...@>=
//! h:=knots;
//! loop@+  begin if left_type(h)<>open then goto done;
//!   if right_type(h)<>open then goto done;
//!   h:=link(h);
//!   if h=knots then
//!     begin left_type(h):=end_cycle; goto done;
//!     end;
//!   end;
//! done:
//!
//! @ If |right_type(p)<given| and |q=link(p)|, we must have
//! |right_type(p)=left_type(q)=explicit| or |endpoint|.
//!
//! @<Fill in the control points between |p| and the next breakpoint...@>=
//! q:=link(p);
//! if right_type(p)>=given then
//!   begin while (left_type(q)=open)and(right_type(q)=open) do q:=link(q);
//!   @<Fill in the control information between
//!     consecutive breakpoints |p| and |q|@>;
//!   end;
//! p:=q
//!
//! @ Before we can go further into the way choices are made, we need to
//! consider the underlying theory. The basic ideas implemented in |make_choices|
//! are due to John Hobby, who introduced the notion of ``mock curvature''
//! @^Hobby, John Douglas@>
//! at a knot. Angles are chosen so that they preserve mock curvature when
//! a knot is passed, and this has been found to produce excellent results.
//!
//! It is convenient to introduce some notations that simplify the necessary
//! formulas. Let $d_{k,k+1}=\vert z\k-z_k\vert$ be the (nonzero) distance
//! between knots |k| and |k+1|; and let
//! $${z\k-z_k\over z_k-z_{k-1}}={d_{k,k+1}\over d_{k-1,k}}e^{i\psi_k}$$
//! so that a polygonal line from $z_{k-1}$ to $z_k$ to $z\k$ turns left
//! through an angle of~$\psi_k$. We assume that $\vert\psi_k\vert\L180^\circ$.
//! The control points for the spline from $z_k$ to $z\k$ will be denoted by
//! $$\eqalign{z_k^+&=z_k+
//!   \textstyle{1\over3}\rho_k e^{i\theta_k}(z\k-z_k),\cr
//!  z\k^-&=z\k-
//!   \textstyle{1\over3}\sigma\k e^{-i\phi\k}(z\k-z_k),\cr}$$
//! where $\rho_k$ and $\sigma\k$ are nonnegative ``velocity ratios'' at the
//! beginning and end of the curve, while $\theta_k$ and $\phi\k$ are the
//! corresponding ``offset angles.'' These angles satisfy the condition
//! $$\theta_k+\phi_k+\psi_k=0,\eqno(*)$$
//! whenever the curve leaves an intermediate knot~|k| in the direction that
//! it enters.
//!
//! @ Let $\alpha_k$ and $\beta\k$ be the reciprocals of the ``tension'' of
//! the curve at its beginning and ending points. This means that
//! $\rho_k=\alpha_k f(\theta_k,\phi\k)$ and $\sigma\k=\beta\k f(\phi\k,\theta_k)$,
//! where $f(\theta,\phi)$ is \MF's standard velocity function defined in
//! the |velocity| subroutine. The cubic spline $B(z_k^{\phantom+},z_k^+,
//! z\k^-,z\k^{\phantom+};t)$
//! has curvature
//! @^curvature@>
//! $${2\sigma\k\sin(\theta_k+\phi\k)-6\sin\theta_k\over\rho_k^2d_{k,k+1}}
//! \qquad{\rm and}\qquad
//! {2\rho_k\sin(\theta_k+\phi\k)-6\sin\phi\k\over\sigma\k^2d_{k,k+1}}$$
//! at |t=0| and |t=1|, respectively. The mock curvature is the linear
//! @^mock curvature@>
//! approximation to this true curvature that arises in the limit for
//! small $\theta_k$ and~$\phi\k$, if second-order terms are discarded.
//! The standard velocity function satisfies
//! $$f(\theta,\phi)=1+O(\theta^2+\theta\phi+\phi^2);$$
//! hence the mock curvatures are respectively
//! $${2\beta\k(\theta_k+\phi\k)-6\theta_k\over\alpha_k^2d_{k,k+1}}
//! \qquad{\rm and}\qquad
//! {2\alpha_k(\theta_k+\phi\k)-6\phi\k\over\beta\k^2d_{k,k+1}}.\eqno(**)$$
//!
//! @ The turning angles $\psi_k$ are given, and equation $(*)$ above
//! determines $\phi_k$ when $\theta_k$ is known, so the task of
//! angle selection is essentially to choose appropriate values for each
//! $\theta_k$. When equation~$(*)$ is used to eliminate $\phi$~variables
//! from $(**)$, we obtain a system of linear equations of the form
//! $$A_k\theta_{k-1}+(B_k+C_k)\theta_k+D_k\theta\k=-B_k\psi_k-D_k\psi\k,$$
//! where
//! $$A_k={\alpha_{k-1}\over\beta_k^2d_{k-1,k}},
//! \qquad B_k={3-\alpha_{k-1}\over\beta_k^2d_{k-1,k}},
//! \qquad C_k={3-\beta\k\over\alpha_k^2d_{k,k+1}},
//! \qquad D_k={\beta\k\over\alpha_k^2d_{k,k+1}}.$$
//! The tensions are always $3\over4$ or more, hence each $\alpha$ and~$\beta$
//! will be at most $4\over3$. It follows that $B_k\G{5\over4}A_k$ and
//! $C_k\G{5\over4}D_k$; hence the equations are diagonally dominant;
//! hence they have a unique solution. Moreover, in most cases the tensions
//! are equal to~1, so that $B_k=2A_k$ and $C_k=2D_k$. This makes the
//! solution numerically stable, and there is an exponential damping
//! effect: The data at knot $k\pm j$ affects the angle at knot~$k$ by
//! a factor of~$O(2^{-j})$.
//!
//! @ However, we still must consider the angles at the starting and ending
//! knots of a non-cyclic path. These angles might be given explicitly, or
//! they might be specified implicitly in terms of an amount of ``curl.''
//!
//! Let's assume that angles need to be determined for a non-cyclic path
//! starting at $z_0$ and ending at~$z_n$. Then equations of the form
//! $$A_k\theta_{k-1}+(B_k+C_k)\theta_k+D_k\theta_{k+1}=R_k$$
//! have been given for $0<k<n$, and it will be convenient to introduce
//! equations of the same form for $k=0$ and $k=n$, where
//! $$A_0=B_0=C_n=D_n=0.$$
//! If $\theta_0$ is supposed to have a given value $E_0$, we simply
//! define $C_0=1$, $D_0=0$, and $R_0=E_0$. Otherwise a curl
//! parameter, $\gamma_0$, has been specified at~$z_0$; this means
//! that the mock curvature at $z_0$ should be $\gamma_0$ times the
//! mock curvature at $z_1$; i.e.,
//! $${2\beta_1(\theta_0+\phi_1)-6\theta_0\over\alpha_0^2d_{01}}
//! =\gamma_0{2\alpha_0(\theta_0+\phi_1)-6\phi_1\over\beta_1^2d_{01}}.$$
//! This equation simplifies to
//! $$(\alpha_0\chi_0+3-\beta_1)\theta_0+
//!  \bigl((3-\alpha_0)\chi_0+\beta_1\bigr)\theta_1=
//!  -\bigl((3-\alpha_0)\chi_0+\beta_1\bigr)\psi_1,$$
//! where $\chi_0=\alpha_0^2\gamma_0/\beta_1^2$; so we can set $C_0=
//! \chi_0\alpha_0+3-\beta_1$, $D_0=(3-\alpha_0)\chi_0+\beta_1$, $R_0=-D_0\psi_1$.
//! It can be shown that $C_0>0$ and $C_0B_1-A_1D_0>0$ when $\gamma_0\G0$,
//! hence the linear equations remain nonsingular.
//!
//! Similar considerations apply at the right end, when the final angle $\phi_n$
//! may or may not need to be determined. It is convenient to let $\psi_n=0$,
//! hence $\theta_n=-\phi_n$. We either have an explicit equation $\theta_n=E_n$,
//! or we have
//! $$\bigl((3-\beta_n)\chi_n+\alpha_{n-1}\bigr)\theta_{n-1}+
//! (\beta_n\chi_n+3-\alpha_{n-1})\theta_n=0,\qquad
//!   \chi_n={\beta_n^2\gamma_n\over\alpha_{n-1}^2}.$$
//!
//! When |make_choices| chooses angles, it must compute the coefficients of
//! these linear equations, then solve the equations. To compute the coefficients,
//! it is necessary to compute arctangents of the given turning angles~$\psi_k$.
//! When the equations are solved, the chosen directions $\theta_k$ are put
//! back into the form of control points by essentially computing sines and
//! cosines.
//!
//! @ OK, we are ready to make the hard choices of |make_choices|.
//! Most of the work is relegated to an auxiliary procedure
//! called |solve_choices|, which has been introduced to keep
//! |make_choices| from being extremely long.
//!
//! @<Fill in the control information between...@>=
//! @<Calculate the turning angles $\psi_k$ and the distances $d_{k,k+1}$;
//!   set $n$ to the length of the path@>;
//! @<Remove |open| types at the breakpoints@>;
//! solve_choices(p,q,n)
//!
//! @ It's convenient to precompute quantities that will be needed several
//! times later. The values of |delta_x[k]| and |delta_y[k]| will be the
//! coordinates of $z\k-z_k$, and the magnitude of this vector will be
//! |delta[k]=@t$d_{k,k+1}$@>|. The path angle $\psi_k$ between $z_k-z_{k-1}$
//! and $z\k-z_k$ will be stored in |psi[k]|.
//!
//! @<Glob...@>=
//! @!delta_x,@!delta_y,@!delta:array[0..path_size] of scaled; {knot differences}
//! @!psi:array[1..path_size] of angle; {turning angles}
//!
//! @ @<Other local variables for |make_choices|@>=
//! @!k,@!n:0..path_size; {current and final knot numbers}
//! @!s,@!t:pointer; {registers for list traversal}
//! @!delx,@!dely:scaled; {directions where |open| meets |explicit|}
//! @!sine,@!cosine:fraction; {trig functions of various angles}
//!
//! @ @<Calculate the turning angles...@>=
//! k:=0; s:=p; n:=path_size;
//! repeat t:=link(s);
//! delta_x[k]:=x_coord(t)-x_coord(s);
//! delta_y[k]:=y_coord(t)-y_coord(s);
//! delta[k]:=pyth_add(delta_x[k],delta_y[k]);
//! if k>0 then
//!   begin sine:=make_fraction(delta_y[k-1],delta[k-1]);
//!   cosine:=make_fraction(delta_x[k-1],delta[k-1]);
//!   psi[k]:=n_arg(take_fraction(delta_x[k],cosine)+
//!       take_fraction(delta_y[k],sine),
//!     take_fraction(delta_y[k],cosine)-
//!       take_fraction(delta_x[k],sine));
//!   end;
//! @:METAFONT capacity exceeded path size}{\quad path size@>
//! incr(k); s:=t;
//! if k=path_size then overflow("path size",path_size);
//! if s=q then n:=k;
//! until (k>=n)and(left_type(s)<>end_cycle);
//! if k=n then psi[n]:=0@+else psi[k]:=psi[1]
//!
//! @ When we get to this point of the code, |right_type(p)| is either
//! |given| or |curl| or |open|. If it is |open|, we must have
//! |left_type(p)=end_cycle| or |left_type(p)=explicit|. In the latter
//! case, the |open| type is converted to |given|; however, if the
//! velocity coming into this knot is zero, the |open| type is
//! converted to a |curl|, since we don't know the incoming direction.
//!
//! Similarly, |left_type(q)| is either |given| or |curl| or |open| or
//! |end_cycle|. The |open| possibility is reduced either to |given| or to |curl|.
//!
//! @<Remove |open| types at the breakpoints@>=
//! if left_type(q)=open then
//!   begin delx:=right_x(q)-x_coord(q); dely:=right_y(q)-y_coord(q);
//!   if (delx=0)and(dely=0) then
//!     begin left_type(q):=curl; left_curl(q):=unity;
//!     end
//!   else  begin left_type(q):=given; left_given(q):=n_arg(delx,dely);
//!     end;
//!   end;
//! if (right_type(p)=open)and(left_type(p)=explicit) then
//!   begin delx:=x_coord(p)-left_x(p); dely:=y_coord(p)-left_y(p);
//!   if (delx=0)and(dely=0) then
//!     begin right_type(p):=curl; right_curl(p):=unity;
//!     end
//!   else  begin right_type(p):=given; right_given(p):=n_arg(delx,dely);
//!     end;
//!   end
//!
//! @ Linear equations need to be solved whenever |n>1|; and also when |n=1|
//! and exactly one of the breakpoints involves a curl. The simplest case occurs
//! when |n=1| and there is a curl at both breakpoints; then we simply draw
//! a straight line.
//!
//! But before coding up the simple cases, we might as well face the general case,
//! since we must deal with it sooner or later, and since the general case
//! is likely to give some insight into the way simple cases can be handled best.
//!
//! When there is no cycle, the linear equations to be solved form a tri-diagonal
//! system, and we can apply the standard technique of Gaussian elimination
//! to convert that system to a sequence of equations of the form
//! $$\theta_0+u_0\theta_1=v_0,\quad
//! \theta_1+u_1\theta_2=v_1,\quad\ldots,\quad
//! \theta_{n-1}+u_{n-1}\theta_n=v_{n-1},\quad
//! \theta_n=v_n.$$
//! It is possible to do this diagonalization while generating the equations.
//! Once $\theta_n$ is known, it is easy to determine $\theta_{n-1}$, \dots,
//! $\theta_1$, $\theta_0$; thus, the equations will be solved.
//!
//! The procedure is slightly more complex when there is a cycle, but the
//! basic idea will be nearly the same. In the cyclic case the right-hand
//! sides will be $v_k+w_k\theta_0$ instead of simply $v_k$, and we will start
//! the process off with $u_0=v_0=0$, $w_0=1$. The final equation will be not
//! $\theta_n=v_n$ but $\theta_n+u_n\theta_1=v_n+w_n\theta_0$; an appropriate
//! ending routine will take account of the fact that $\theta_n=\theta_0$ and
//! eliminate the $w$'s from the system, after which the solution can be
//! obtained as before.
//!
//! When $u_k$, $v_k$, and $w_k$ are being computed, the three pointer
//! variables |r|, |s|,~|t| will point respectively to knots |k-1|, |k|,
//! and~|k+1|. The $u$'s and $w$'s are scaled by $2^{28}$, i.e., they are
//! of type |fraction|; the $\theta$'s and $v$'s are of type |angle|.
//!
//! @<Glob...@>=
//! @!theta:array[0..path_size] of angle; {values of $\theta_k$}
//! @!uu:array[0..path_size] of fraction; {values of $u_k$}
//! @!vv:array[0..path_size] of angle; {values of $v_k$}
//! @!ww:array[0..path_size] of fraction; {values of $w_k$}
//!
//! @ Our immediate problem is to get the ball rolling by setting up the
//! first equation or by realizing that no equations are needed, and to fit
//! this initialization into a framework suitable for the overall computation.
//!
//! @<Declare the procedure called |solve_choices|@>=
//! @t\4@>@<Declare subroutines needed by |solve_choices|@>@;
//! procedure solve_choices(@!p,@!q:pointer;@!n:halfword);
//! label found,exit;
//! var @!k:0..path_size; {current knot number}
//! @!r,@!s,@!t:pointer; {registers for list traversal}
//! @<Other local variables for |solve_choices|@>@;
//! begin k:=0; s:=p;
//! loop@+  begin t:=link(s);
//!   if k=0 then @<Get the linear equations started; or |return|
//!     with the control points in place, if linear equations
//!     needn't be solved@>
//!   else  case left_type(s) of
//!     end_cycle,open:@<Set up equation to match mock curvatures
//!       at $z_k$; then |goto found| with $\theta_n$
//!       adjusted to equal $\theta_0$, if a cycle has ended@>;
//!     curl:@<Set up equation for a curl at $\theta_n$
//!       and |goto found|@>;
//!     given:@<Calculate the given value of $\theta_n$
//!       and |goto found|@>;
//!     end; {there are no other cases}
//!   r:=s; s:=t; incr(k);
//!   end;
//! found:@<Finish choosing angles and assigning control points@>;
//! exit:end;
//!
//! @ On the first time through the loop, we have |k=0| and |r| is not yet
//! defined. The first linear equation, if any, will have $A_0=B_0=0$.
//!
//! @<Get the linear equations started...@>=
//! case right_type(s) of
//! given: if left_type(t)=given then @<Reduce to simple case of two givens
//!     and |return|@>
//!   else @<Set up the equation for a given value of $\theta_0$@>;
//! curl: if left_type(t)=curl then @<Reduce to simple case of straight line
//!     and |return|@>
//!   else @<Set up the equation for a curl at $\theta_0$@>;
//! open: begin uu[0]:=0; vv[0]:=0; ww[0]:=fraction_one;
//!   end; {this begins a cycle}
//! end {there are no other cases}
//!
//! @ The general equation that specifies equality of mock curvature at $z_k$ is
//! $$A_k\theta_{k-1}+(B_k+C_k)\theta_k+D_k\theta\k=-B_k\psi_k-D_k\psi\k,$$
//! as derived above. We want to combine this with the already-derived equation
//! $\theta_{k-1}+u_{k-1}\theta_k=v_{k-1}+w_{k-1}\theta_0$ in order to obtain
//! a new equation
//! $\theta_k+u_k\theta\k=v_k+w_k\theta_0$. This can be done by dividing the
//! equation
//! $$(B_k-u_{k-1}A_k+C_k)\theta_k+D_k\theta\k=-B_k\psi_k-D_k\psi\k-A_kv_{k-1}
//!     -A_kw_{k-1}\theta_0$$
//! by $B_k-u_{k-1}A_k+C_k$. The trick is to do this carefully with
//! fixed-point arithmetic, avoiding the chance of overflow while retaining
//! suitable precision.
//!
//! The calculations will be performed in several registers that
//! provide temporary storage for intermediate quantities.
//!
//! @<Other local variables for |solve_choices|@>=
//! @!aa,@!bb,@!cc,@!ff,@!acc:fraction; {temporary registers}
//! @!dd,@!ee:scaled; {likewise, but |scaled|}
//! @!lt,@!rt:scaled; {tension values}
//!
//! @ @<Set up equation to match mock curvatures...@>=
//! begin @<Calculate the values $\\{aa}=A_k/B_k$, $\\{bb}=D_k/C_k$,
//!   $\\{dd}=(3-\alpha_{k-1})d_{k,k+1}$, $\\{ee}=(3-\beta\k)d_{k-1,k}$,
//!   and $\\{cc}=(B_k-u_{k-1}A_k)/B_k$@>;
//! @<Calculate the ratio $\\{ff}=C_k/(C_k+B_k-u_{k-1}A_k)$@>;
//! uu[k]:=take_fraction(ff,bb);
//! @<Calculate the values of $v_k$ and $w_k$@>;
//! if left_type(s)=end_cycle then
//!   @<Adjust $\theta_n$ to equal $\theta_0$ and |goto found|@>;
//! end
//!
//! @ Since tension values are never less than 3/4, the values |aa| and
//! |bb| computed here are never more than 4/5.
//!
//! @<Calculate the values $\\{aa}=...@>=
//! if abs(right_tension(r))=unity then
//!   begin aa:=fraction_half; dd:=2*delta[k];
//!   end
//! else  begin aa:=make_fraction(unity,3*abs(right_tension(r))-unity);
//!   dd:=take_fraction(delta[k],
//!     fraction_three-make_fraction(unity,abs(right_tension(r))));
//!   end;
//! if abs(left_tension(t))=unity then
//!   begin bb:=fraction_half; ee:=2*delta[k-1];
//!   end
//! else  begin bb:=make_fraction(unity,3*abs(left_tension(t))-unity);
//!   ee:=take_fraction(delta[k-1],
//!     fraction_three-make_fraction(unity,abs(left_tension(t))));
//!   end;
//! cc:=fraction_one-take_fraction(uu[k-1],aa)
//!
//! @ The ratio to be calculated in this step can be written in the form
//! $$\beta_k^2\cdot\\{ee}\over\beta_k^2\cdot\\{ee}+\alpha_k^2\cdot
//!   \\{cc}\cdot\\{dd},$$
//! because of the quantities just calculated. The values of |dd| and |ee|
//! will not be needed after this step has been performed.
//!
//! @<Calculate the ratio $\\{ff}=C_k/(C_k+B_k-u_{k-1}A_k)$@>=
//! dd:=take_fraction(dd,cc); lt:=abs(left_tension(s)); rt:=abs(right_tension(s));
//! if lt<>rt then {$\beta_k^{-1}\ne\alpha_k^{-1}$}
//!   if lt<rt then
//!     begin ff:=make_fraction(lt,rt);
//!     ff:=take_fraction(ff,ff); {$\alpha_k^2/\beta_k^2$}
//!     dd:=take_fraction(dd,ff);
//!     end
//!   else  begin ff:=make_fraction(rt,lt);
//!     ff:=take_fraction(ff,ff); {$\beta_k^2/\alpha_k^2$}
//!     ee:=take_fraction(ee,ff);
//!     end;
//! ff:=make_fraction(ee,ee+dd)
//!
//! @ The value of $u_{k-1}$ will be |<=1| except when $k=1$ and the previous
//! equation was specified by a curl. In that case we must use a special
//! method of computation to prevent overflow.
//!
//! Fortunately, the calculations turn out to be even simpler in this ``hard''
//! case. The curl equation makes $w_0=0$ and $v_0=-u_0\psi_1$, hence
//! $-B_1\psi_1-A_1v_0=-(B_1-u_0A_1)\psi_1=-\\{cc}\cdot B_1\psi_1$.
//!
//! @<Calculate the values of $v_k$ and $w_k$@>=
//! acc:=-take_fraction(psi[k+1],uu[k]);
//! if right_type(r)=curl then
//!   begin ww[k]:=0;
//!   vv[k]:=acc-take_fraction(psi[1],fraction_one-ff);
//!   end
//! else  begin ff:=make_fraction(fraction_one-ff,cc); {this is
//!     $B_k/(C_k+B_k-u_{k-1}A_k)<5$}
//!   acc:=acc-take_fraction(psi[k],ff);
//!   ff:=take_fraction(ff,aa); {this is $A_k/(C_k+B_k-u_{k-1}A_k)$}
//!   vv[k]:=acc-take_fraction(vv[k-1],ff);
//!   if ww[k-1]=0 then ww[k]:=0
//!   else ww[k]:=-take_fraction(ww[k-1],ff);
//!   end
//!
//! @ When a complete cycle has been traversed, we have $\theta_k+u_k\theta\k=
//! v_k+w_k\theta_0$, for |1<=k<=n|. We would like to determine the value of
//! $\theta_n$ and reduce the system to the form $\theta_k+u_k\theta\k=v_k$
//! for |0<=k<n|, so that the cyclic case can be finished up just as if there
//! were no cycle.
//!
//! The idea in the following code is to observe that
//! $$\eqalign{\theta_n&=v_n+w_n\theta_0-u_n\theta_1=\cdots\cr
//! &=v_n+w_n\theta_0-u_n\bigl(v_1+w_1\theta_0-u_1(v_2+\cdots
//!   -u_{n-2}(v_{n-1}+w_{n-1}\theta_0-u_{n-1}\theta_0)\ldots{})\bigr),\cr}$$
//! so we can solve for $\theta_n=\theta_0$.
//!
//! @<Adjust $\theta_n$ to equal $\theta_0$ and |goto found|@>=
//! begin aa:=0; bb:=fraction_one; {we have |k=n|}
//! repeat decr(k);
//! if k=0 then k:=n;
//! aa:=vv[k]-take_fraction(aa,uu[k]);
//! bb:=ww[k]-take_fraction(bb,uu[k]);
//! until k=n; {now $\theta_n=\\{aa}+\\{bb}\cdot\theta_n$}
//! aa:=make_fraction(aa,fraction_one-bb);
//! theta[n]:=aa; vv[0]:=aa;
//! for k:=1 to n-1 do vv[k]:=vv[k]+take_fraction(aa,ww[k]);
//! goto found;
//! end
//!
//! @ @d reduce_angle(#)==if abs(#)>one_eighty_deg then
//!   if #>0 then #:=#-three_sixty_deg@+else #:=#+three_sixty_deg
//!
//! @<Calculate the given value of $\theta_n$...@>=
//! begin theta[n]:=left_given(s)-n_arg(delta_x[n-1],delta_y[n-1]);
//! reduce_angle(theta[n]);
//! goto found;
//! end
//!
//! @ @<Set up the equation for a given value of $\theta_0$@>=
//! begin vv[0]:=right_given(s)-n_arg(delta_x[0],delta_y[0]);
//! reduce_angle(vv[0]);
//! uu[0]:=0; ww[0]:=0;
//! end
//!
//! @ @<Set up the equation for a curl at $\theta_0$@>=
//! begin cc:=right_curl(s); lt:=abs(left_tension(t)); rt:=abs(right_tension(s));
//! if (rt=unity)and(lt=unity) then
//!   uu[0]:=make_fraction(cc+cc+unity,cc+two)
//! else uu[0]:=curl_ratio(cc,rt,lt);
//! vv[0]:=-take_fraction(psi[1],uu[0]); ww[0]:=0;
//! end
//!
//! @ @<Set up equation for a curl at $\theta_n$...@>=
//! begin cc:=left_curl(s); lt:=abs(left_tension(s)); rt:=abs(right_tension(r));
//! if (rt=unity)and(lt=unity) then
//!   ff:=make_fraction(cc+cc+unity,cc+two)
//! else ff:=curl_ratio(cc,lt,rt);
//! theta[n]:=-make_fraction(take_fraction(vv[n-1],ff),
//!     fraction_one-take_fraction(ff,uu[n-1]));
//! goto found;
//! end
//!
//! @ The |curl_ratio| subroutine has three arguments, which our previous notation
//! encourages us to call $\gamma$, $\alpha^{-1}$, and $\beta^{-1}$. It is
//! a somewhat tedious program to calculate
//! $${(3-\alpha)\alpha^2\gamma+\beta^3\over
//!   \alpha^3\gamma+(3-\beta)\beta^2},$$
//! with the result reduced to 4 if it exceeds 4. (This reduction of curl
//! is necessary only if the curl and tension are both large.)
//! The values of $\alpha$ and $\beta$ will be at most~4/3.
//!
//! @<Declare subroutines needed by |solve_choices|@>=
//! function curl_ratio(@!gamma,@!a_tension,@!b_tension:scaled):fraction;
//! var @!alpha,@!beta,@!num,@!denom,@!ff:fraction; {registers}
//! begin alpha:=make_fraction(unity,a_tension);
//! beta:=make_fraction(unity,b_tension);@/
//! if alpha<=beta then
//!   begin ff:=make_fraction(alpha,beta); ff:=take_fraction(ff,ff);
//!   gamma:=take_fraction(gamma,ff);@/
//!   beta:=beta div @'10000; {convert |fraction| to |scaled|}
//!   denom:=take_fraction(gamma,alpha)+three-beta;
//!   num:=take_fraction(gamma,fraction_three-alpha)+beta;
//!   end
//! else  begin ff:=make_fraction(beta,alpha); ff:=take_fraction(ff,ff);
//!   beta:=take_fraction(beta,ff) div @'10000; {convert |fraction| to |scaled|}
//!   denom:=take_fraction(gamma,alpha)+(ff div 1365)-beta;
//!     {$1365\approx 2^{12}/3$}
//!   num:=take_fraction(gamma,fraction_three-alpha)+beta;
//!   end;
//! if num>=denom+denom+denom+denom then curl_ratio:=fraction_four
//! else curl_ratio:=make_fraction(num,denom);
//! end;
//!
//! @ We're in the home stretch now.
//!
//! @<Finish choosing angles and assigning control points@>=
//! for k:=n-1 downto 0 do theta[k]:=vv[k]-take_fraction(theta[k+1],uu[k]);
//! s:=p; k:=0;
//! repeat t:=link(s);@/
//! n_sin_cos(theta[k]); st:=n_sin; ct:=n_cos;@/
//! n_sin_cos(-psi[k+1]-theta[k+1]); sf:=n_sin; cf:=n_cos;@/
//! set_controls(s,t,k);@/
//! incr(k); s:=t;
//! until k=n
//!
//! @ The |set_controls| routine actually puts the control points into
//! a pair of consecutive nodes |p| and~|q|. Global variables are used to
//! record the values of $\sin\theta$, $\cos\theta$, $\sin\phi$, and
//! $\cos\phi$ needed in this calculation.
//!
//! @<Glob...@>=
//! @!st,@!ct,@!sf,@!cf:fraction; {sines and cosines}
//!
//! @ @<Declare subroutines needed by |solve_choices|@>=
//! procedure set_controls(@!p,@!q:pointer;@!k:integer);
//! var @!rr,@!ss:fraction; {velocities, divided by thrice the tension}
//! @!lt,@!rt:scaled; {tensions}
//! @!sine:fraction; {$\sin(\theta+\phi)$}
//! begin lt:=abs(left_tension(q)); rt:=abs(right_tension(p));
//! rr:=velocity(st,ct,sf,cf,rt);
//! ss:=velocity(sf,cf,st,ct,lt);
//! if (right_tension(p)<0)or(left_tension(q)<0) then @<Decrease the velocities,
//!   if necessary, to stay inside the bounding triangle@>;
//! right_x(p):=x_coord(p)+take_fraction(
//!   take_fraction(delta_x[k],ct)-take_fraction(delta_y[k],st),rr);
//! right_y(p):=y_coord(p)+take_fraction(
//!   take_fraction(delta_y[k],ct)+take_fraction(delta_x[k],st),rr);
//! left_x(q):=x_coord(q)-take_fraction(
//!   take_fraction(delta_x[k],cf)+take_fraction(delta_y[k],sf),ss);
//! left_y(q):=y_coord(q)-take_fraction(
//!   take_fraction(delta_y[k],cf)-take_fraction(delta_x[k],sf),ss);
//! right_type(p):=explicit; left_type(q):=explicit;
//! end;
//!
//! @ The boundedness conditions $\\{rr}\L\sin\phi\,/\sin(\theta+\phi)$ and
//! $\\{ss}\L\sin\theta\,/\sin(\theta+\phi)$ are to be enforced if $\sin\theta$,
//! $\sin\phi$, and $\sin(\theta+\phi)$ all have the same sign. Otherwise
//! there is no ``bounding triangle.''
//!
//! @<Decrease the velocities, if necessary...@>=
//! if((st>=0)and(sf>=0))or((st<=0)and(sf<=0)) then
//!   begin sine:=take_fraction(abs(st),cf)+take_fraction(abs(sf),ct);
//!   if sine>0 then
//!     begin sine:=take_fraction(sine,fraction_one+unity); {safety factor}
//!     if right_tension(p)<0 then
//!      if ab_vs_cd(abs(sf),fraction_one,rr,sine)<0 then
//!       rr:=make_fraction(abs(sf),sine);
//!     if left_tension(q)<0 then
//!      if ab_vs_cd(abs(st),fraction_one,ss,sine)<0 then
//!       ss:=make_fraction(abs(st),sine);
//!     end;
//!   end
//!
//! @ Only the simple cases remain to be handled.
//!
//! @<Reduce to simple case of two givens and |return|@>=
//! begin aa:=n_arg(delta_x[0],delta_y[0]);@/
//! n_sin_cos(right_given(p)-aa); ct:=n_cos; st:=n_sin;@/
//! n_sin_cos(left_given(q)-aa); cf:=n_cos; sf:=-n_sin;@/
//! set_controls(p,q,0); return;
//! end
//!
//! @ @<Reduce to simple case of straight line and |return|@>=
//! begin right_type(p):=explicit; left_type(q):=explicit;
//! lt:=abs(left_tension(q)); rt:=abs(right_tension(p));
//! if rt=unity then
//!   begin if delta_x[0]>=0 then right_x(p):=x_coord(p)+((delta_x[0]+1) div 3)
//!   else right_x(p):=x_coord(p)+((delta_x[0]-1) div 3);
//!   if delta_y[0]>=0 then right_y(p):=y_coord(p)+((delta_y[0]+1) div 3)
//!   else right_y(p):=y_coord(p)+((delta_y[0]-1) div 3);
//!   end
//! else  begin ff:=make_fraction(unity,3*rt); {$\alpha/3$}
//!   right_x(p):=x_coord(p)+take_fraction(delta_x[0],ff);
//!   right_y(p):=y_coord(p)+take_fraction(delta_y[0],ff);
//!   end;
//! if lt=unity then
//!   begin if delta_x[0]>=0 then left_x(q):=x_coord(q)-((delta_x[0]+1) div 3)
//!   else left_x(q):=x_coord(q)-((delta_x[0]-1) div 3);
//!   if delta_y[0]>=0 then left_y(q):=y_coord(q)-((delta_y[0]+1) div 3)
//!   else left_y(q):=y_coord(q)-((delta_y[0]-1) div 3);
//!   end
//! else  begin ff:=make_fraction(unity,3*lt); {$\beta/3$}
//!   left_x(q):=x_coord(q)-take_fraction(delta_x[0],ff);
//!   left_y(q):=y_coord(q)-take_fraction(delta_y[0],ff);
//!   end;
//! return;
//! end
//!
//! @* \[19] Generating discrete moves.
//! The purpose of the next part of \MF\ is to compute discrete approximations
//! to curves described as parametric polynomial functions $z(t)$.
//! We shall start with the low level first, because an efficient ``engine''
//! is needed to support the high-level constructions.
//!
//! Most of the subroutines are based on variations of a single theme,
//! namely the idea of {\sl bisection}. Given a Bernshte{\u\i}n polynomial
//! @^Bernshte{\u\i}n, Serge{\u\i} Natanovich@>
//! $$B(z_0,z_1,\ldots,z_n;t)=\sum_k{n\choose k}t^k(1-t)^{n-k}z_k,$$
//! we can conveniently bisect its range as follows:
//!
//! \smallskip
//! \textindent{1)} Let $z_k^{(0)}=z_k$, for |0<=k<=n|.
//!
//! \smallskip
//! \textindent{2)} Let $z_k^{(j+1)}={1\over2}(z_k^{(j)}+z\k^{(j)})$, for
//! |0<=k<n-j|, for |0<=j<n|.
//!
//! \smallskip\noindent
//! Then
//! $$B(z_0,z_1,\ldots,z_n;t)=B(z_0^{(0)},z_0^{(1)},\ldots,z_0^{(n)};2t)
//!  =B(z_0^{(n)},z_1^{(n-1)},\ldots,z_n^{(0)};2t-1).$$
//! This formula gives us the coefficients of polynomials to use over the ranges
//! $0\L t\L{1\over2}$ and ${1\over2}\L t\L1$.
//!
//! In our applications it will usually be possible to work indirectly with
//! numbers that allow us to deduce relevant properties of the polynomials
//! without actually computing the polynomial values. We will deal with
//! coefficients $Z_k=2^l(z_k-z_{k-1})$ for |1<=k<=n|, instead of
//! the actual numbers $z_0$, $z_1$, \dots,~$z_n$, and the value of~|l| will
//! increase by~1 at each bisection step. This technique reduces the
//! amount of calculation needed for bisection and also increases the
//! accuracy of evaluation (since one bit of precision is gained at each
//! bisection). Indeed, the bisection process now becomes one level shorter:
//!
//! \smallskip
//! \textindent{$1'$)} Let $Z_k^{(1)}=Z_k$, for |1<=k<=n|.
//!
//! \smallskip
//! \textindent{$2'$)} Let $Z_k^{(j+1)}={1\over2}(Z_k^{(j)}+Z\k^{(j)})$, for
//! |1<=k<=n-j|, for |1<=j<n|.
//!
//! \smallskip\noindent
//! The relevant coefficients $(Z'_1,\ldots,Z'_n)$ and $(Z''_1,\ldots,Z''_n)$
//! for the two subintervals after bisection are respectively
//! $(Z_1^{(1)},Z_1^{(2)},\ldots,Z_1^{(n)})$ and
//! $(Z_1^{(n)},Z_2^{(n-1)},\ldots,Z_n^{(1)})$.
//! And the values of $z_0$ appropriate for the bisected interval are $z'_0=z_0$
//! and $z''_0=z_0+(Z'_1+Z'_2+\cdots+Z'_n)/2^{l+1}$.
//!
//! Step $2'$ involves division by~2, which introduces computational errors
//! of at most $1\over2$ at each step; thus after $l$~levels of bisection the
//! integers $Z_k$ will differ from their true values by at most $(n-1)l/2$.
//! This error rate is quite acceptable, considering that we have $l$~more
//! bits of precision in the $Z$'s by comparison with the~$z$'s.  Note also
//! that the $Z$'s remain bounded; there's no danger of integer overflow, even
//! though we have the identity $Z_k=2^l(z_k-z_{k-1})$ for arbitrarily large~$l$.
//!
//! In fact, we can show not only that the $Z$'s remain bounded, but also that
//! they become nearly equal, since they are control points for a polynomial
//! of one less degree. If $\vert Z\k-Z_k\vert\L M$ initially, it is possible
//! to prove that $\vert Z\k-Z_k\vert\L\lceil M/2^l\rceil$ after $l$~levels
//! of bisection, even in the presence of rounding errors. Here's the
//! proof [cf.~Lane and Riesenfeld, {\sl IEEE Trans.\ on Pattern Analysis
//! @^Lane, Jeffrey Michael@>
//! @^Riesenfeld, Richard Franklin@>
//! and Machine Intelligence\/ \bf PAMI-2} (1980), 35--46]: Assuming that
//! $\vert Z\k-Z_k\vert\L M$ before bisection, we want to prove that
//! $\vert Z\k-Z_k\vert\L\lceil M/2\rceil$ afterward. First we show that
//! $\vert Z\k^{(j)}-Z_k^{(j)}\vert\L M$ for all $j$ and~$k$, by induction
//! on~$j$; this follows from the fact that
//! $$\bigl\vert\\{half}(a+b)-\\{half}(b+c)\bigr\vert\L
//!  \max\bigl(\vert a-b\vert,\vert b-c\vert\bigr)$$
//! holds for both of the rounding rules $\\{half}(x)=\lfloor x/2\rfloor$
//! and $\\{half}(x)={\rm sign}(x)\lfloor\vert x/2\vert\rfloor$.
//! (If $\vert a-b\vert$ and $\vert b-c\vert$ are equal, then
//! $a+b$ and $b+c$ are both even or both odd. The rounding errors either
//! cancel or round the numbers toward each other; hence
//! $$\eqalign{\bigl\vert\\{half}(a+b)-\\{half}(b+c)\bigr\vert
//! &\L\textstyle\bigl\vert{1\over2}(a+b)-{1\over2}(b+c)\bigr\vert\cr
//! &=\textstyle\bigl\vert{1\over2}(a-b)+{1\over2}(b-c)\bigr\vert
//! \L\max\bigl(\vert a-b\vert,\vert b-c\vert\bigr),\cr}$$
//! as required. A simpler argument applies if $\vert a-b\vert$ and
//! $\vert b-c\vert$ are unequal.)  Now it is easy to see that
//! $\vert Z_1^{(j+1)}-Z_1^{(j)}\vert\L\bigl\lfloor{1\over2}
//! \vert Z_2^{(j)}-Z_1^{(j)}\vert+{1\over2}\bigr\rfloor
//! \L\bigl\lfloor{1\over2}(M+1)\bigr\rfloor=\lceil M/2\rceil$.
//!
//! Another interesting fact about bisection is the identity
//! $$Z_1'+\cdots+Z_n'+Z_1''+\cdots+Z_n''=2(Z_1+\cdots+Z_n+E),$$
//! where $E$ is the sum of the rounding errors in all of the halving
//! operations ($\vert E\vert\L n(n-1)/4$).
//!
//! @ We will later reduce the problem of digitizing a complex cubic
//! $z(t)=B(z_0,z_1,z_2,z_3;t)$ to the following simpler problem:
//! Given two real cubics
//! $x(t)=B(x_0,x_1,x_2,x_3;t)$
//! and $y(t)=B(y_0,y_1,y_2,y_3;t)$ that are monotone nondecreasing,
//! determine the set of integer points
//! $$P=\bigl\{\bigl(\lfloor x(t)\rfloor,\lfloor y(t)\rfloor\bigr)
//! \bigm\vert 0\L t\L 1\bigr\}.$$
//! Well, the problem isn't actually quite so clean as this; when the path
//! goes very near an integer point $(a,b)$, computational errors may
//! make us think that $P$ contains $(a-1,b)$ while in reality it should
//! contain $(a,b-1)$. Furthermore, if the path goes {\sl exactly\/}
//! through the integer points $(a-1,b-1)$ and
//! $(a,b)$, we will want $P$ to contain one
//! of the two points $(a-1,b)$ or $(a,b-1)$, so that $P$ can be described
//! entirely by ``rook moves'' upwards or to the right; no diagonal
//! moves from $(a-1,b-1)$ to~$(a,b)$ will be allowed.
//!
//! Thus, the set $P$ we wish to compute will merely be an approximation
//! to the set described in the formula above. It will consist of
//! $\lfloor x(1)\rfloor-\lfloor x(0)\rfloor$ rightward moves and
//! $\lfloor y(1)\rfloor-\lfloor y(0)\rfloor$ upward moves, intermixed
//! in some order. Our job will be to figure out a suitable order.
//!
//! The following recursive strategy suggests itself, when we recall that
//! $x(0)=x_0$, $x(1)=x_3$, $y(0)=y_0$, and $y(1)=y_3$:
//!
//! \smallskip
//! If $\lfloor x_0\rfloor=\lfloor x_3\rfloor$ then take
//! $\lfloor y_3\rfloor-\lfloor y_0\rfloor$ steps up.
//!
//! Otherwise if $\lfloor y_0\rfloor=\lfloor y_3\rfloor$ then take
//! $\lfloor x_3\rfloor-\lfloor x_0\rfloor$ steps to the right.
//!
//! Otherwise bisect the current cubics and repeat the process on both halves.
//!
//! \yskip\noindent
//! This intuitively appealing formulation does not quite solve the problem,
//! because it may never terminate. For example, it's not hard to see that
//! no steps will {\sl ever\/} be taken if $(x_0,x_1,x_2,x_3)=(y_0,y_1,y_2,y_3)$!
//! However, we can surmount this difficulty with a bit of care; so let's
//! proceed to flesh out the algorithm as stated, before worrying about
//! such details.
//!
//! The bisect-and-double strategy discussed above suggests that we represent
//! $(x_0,x_1,x_2,x_3)$ by $(X_1,X_2,X_3)$, where $X_k=2^l(x_k-x_{k-1})$
//! for some~$l$. Initially $l=16$, since the $x$'s are |scaled|.
//! In order to deal with other aspects of the algorithm we will want to
//! maintain also the quantities $m=\lfloor x_3\rfloor-\lfloor x_0\rfloor$
//! and $R=2^l(x_0\bmod 1)$. Similarly,
//! $(y_0,y_1,y_2,y_3)$ will be represented by $(Y_1,Y_2,Y_3)$,
//! $n=\lfloor y_3\rfloor-\lfloor y_0\rfloor$,
//! and $S=2^l(y_0\bmod 1)$. The algorithm now takes the following form:
//!
//! \smallskip
//! If $m=0$ then take $n$ steps up.
//!
//! Otherwise if $n=0$ then take $m$ steps to the right.
//!
//! Otherwise bisect the current cubics and repeat the process on both halves.
//!
//! \smallskip\noindent
//! The bisection process for $(X_1,X_2,X_3,m,R,l)$ reduces, in essence,
//! to the following formulas:
//! $$\vbox{\halign{$#\hfil$\cr
//! X_2'=\\{half}(X_1+X_2),\quad
//! X_2''=\\{half}(X_2+X_3),\quad
//! X_3'=\\{half}(X_2'+X_2''),\cr
//! X_1'=X_1,\quad
//! X_1''=X_3',\quad
//! X_3''=X_3,\cr
//! R'=2R,\quad
//! T=X_1'+X_2'+X_3'+R',\quad
//! R''=T\bmod 2^{l+1},\cr
//! m'=\lfloor T/2^{l+1}\rfloor,\quad
//! m''=m-m'.\cr}}$$
//!
//! @ When $m=n=1$, the computation can be speeded up because we simply
//! need to decide between two alternatives, (up,\thinspace right)
//! versus (right,\thinspace up). There appears to be no simple, direct
//! way to make the correct decision by looking at the values of
//! $(X_1,X_2,X_3,R)$ and
//! $(Y_1,Y_2,Y_3,S)$; but we can streamline the bisection process, and
//! we can use the fact that only one of the two descendants needs to
//! be examined after each bisection. Furthermore, we observed earlier
//! that after several levels of bisection the $X$'s and $Y$'s will be nearly
//! equal; so we will be justified in assuming that the curve is essentially a
//! straight line. (This, incidentally, solves the problem of infinite
//! recursion mentioned earlier.)
//!
//! It is possible to show that
//! $$m=\bigl\lfloor(X_1+X_2+X_3+R+E)\,/\,2^l\bigr\rfloor,$$
//! where $E$ is an accumulated rounding error that is at most
//! $3\cdot(2^{l-16}-1)$ in absolute value. We will make sure that
//! the $X$'s are less than $2^{28}$; hence when $l=30$ we must
//! have |m<=1|. This proves that the special case $m=n=1$ is
//! bound to be reached by the time $l=30$. Furthermore $l=30$ is
//! a suitable time to make the straight line approximation,
//! if the recursion hasn't already died out, because the maximum
//! difference between $X$'s will then be $<2^{14}$; this corresponds
//! to an error of $<1$ with respect to the original scaling.
//! (Stating this another way, each bisection makes the curve two bits
//! closer to a straight line, hence 14 bisections are sufficient for
//! 28-bit accuracy.)
//!
//! In the case of a straight line, the curve goes first right, then up,
//! if and only if $(T-2^l)(2^l-S)>(U-2^l)(2^l-R)$, where
//! $T=X_1+X_2+X_3+R$ and $U=Y_1+Y_2+Y_3+S$. For the actual curve
//! essentially runs from $(R/2^l,S/2^l)$ to $(T/2^l,U/2^l)$, and
//! we are testing whether or not $(1,1)$ is above the straight
//! line connecting these two points. (This formula assumes that $(1,1)$
//! is not exactly on the line.)
//!
//! @ We have glossed over the problem of tie-breaking in ambiguous
//! cases when the cubic curve passes exactly through integer points.
//! \MF\ finesses this problem by assuming that coordinates
//! $(x,y)$ actually stand for slightly perturbed values $(x+\xi,y+\eta)$,
//! where $\xi$ and~$\eta$ are infinitesimals whose signs will determine
//! what to do when $x$ and/or~$y$ are exact integers. The quantities
//! $\lfloor x\rfloor$ and~$\lfloor y\rfloor$ in the formulas above
//! should actually read $\lfloor x+\xi\rfloor$ and $\lfloor y+\eta\rfloor$.
//!
//! If $x$ is a |scaled| value, we have $\lfloor x+\xi\rfloor=\lfloor x\rfloor$
//! if $\xi>0$, and $\lfloor x+\xi\rfloor=\lfloor x-2^{-16}\rfloor$ if
//! $\xi<0$. It is convenient to represent $\xi$ by the integer |xi_corr|,
//! defined to be 0~if $\xi>0$ and 1~if $\xi<0$; then, for example, the
//! integer $\lfloor x+\xi\rfloor$ can be computed as
//! |floor_unscaled(x-xi_corr)|. Similarly, $\eta$ is conveniently
//! represented by~|eta_corr|.
//!
//! In our applications the sign of $\xi-\eta$ will always be the same as
//! the sign of $\xi$. Therefore it turns out that the rule for straight
//! lines, as stated above, should be modified as follows in the case of
//! ties: The line goes first right, then up, if and only if
//! $(T-2^l)(2^l-S)+\xi>(U-2^l)(2^l-R)$. And this relation holds iff
//! $|ab_vs_cd|(T-2^l,2^l-S,U-2^l,2^l-R)-|xi_corr|\ge0$.
//!
//! These conventions for rounding are symmetrical, in the sense that the
//! digitized moves obtained from $(x_0,x_1,x_2,x_3,y_0,y_1,y_2,y_3,\xi,\eta)$
//! will be exactly complementary to the moves that would be obtained from
//! $(-x_3,-x_2,-x_1,-x_0,-y_3,-y_2,-y_1,-y_0,-\xi,-\eta)$, if arithmetic
//! is exact. However, truncation errors in the bisection process might
//! upset the symmetry. We can restore much of the lost symmetry by adding
//! |xi_corr| or |eta_corr| when halving the data.
//!
//! @ One further possibility needs to be mentioned: The algorithm
//! will be applied only to cubic polynomials $B(x_0,x_1,x_2,x_3;t)$ that
//! are nondecreasing as $t$~varies from 0 to~1; this condition turns
//! out to hold if and only if $x_0\L x_1$ and $x_2\L x_3$, and either
//! $x_1\L x_2$ or $(x_1-x_2)^2\L(x_1-x_0)(x_3-x_2)$. If bisection were
//! carried out with perfect accuracy, these relations would remain
//! invariant. But rounding errors can creep in, hence the bisection
//! algorithm can produce non-monotonic subproblems from monotonic
//! initial conditions. This leads to the potential danger that $m$ or~$n$
//! could become negative in the algorithm described above.
//!
//! For example, if we start with $(x_1-x_0,x_2-x_1,x_3-x_2)=
//! (X_1,X_2,X_3)=(7,-16,39)$, the corresponding polynomial is
//! monotonic, because $16^2<7\cdot39$. But the bisection algorithm
//! produces the left descendant $(7,-5,3)$, which is nonmonotonic;
//! its right descendant is~$(0,-1,3)$.
//!
//! \def\xt{{\tilde x}}
//! Fortunately we can prove that such rounding errors will never cause
//! the algorithm to make a tragic mistake. At every stage we are working
//! with numbers corresponding to a cubic polynomial $B(\xt_0,
//! \xt_1,\xt_2,\xt_3)$ that approximates some
//! monotonic polynomial $B(x_0,x_1,x_2,x_3)$. The accumulated errors are
//! controlled so that $\vert x_k-\xt_k\vert<\epsilon=3\cdot2^{-16}$.
//! If bisection is done at some stage of the recursion, we have
//! $m=\lfloor\xt_3\rfloor-\lfloor\xt_0\rfloor>0$, and the algorithm
//! computes a bisection value $\bar x$ such that $m'=\lfloor\bar x\rfloor-
//! \lfloor\xt_0\rfloor$
//! and $m''=\lfloor\xt_3\rfloor-\lfloor\bar x\rfloor$. We want to prove
//! that neither $m'$ nor $m''$ can be negative. Since $\bar x$ is an
//! approximation to a value in the interval $[x_0,x_3]$, we have
//! $\bar x>x_0-\epsilon$ and $\bar x<x_3+\epsilon$, hence $\bar x>
//! \xt_0-2\epsilon$ and $\bar x<\xt_3+2\epsilon$.
//! If $m'$ is negative we must have $\xt_0\bmod 1<2\epsilon$;
//! if $m''$ is negative we must have $\xt_3\bmod 1>1-2\epsilon$.
//! In either case the condition $\lfloor\xt_3\rfloor-\lfloor\xt_0\rfloor>0$
//! implies that $\xt_3-\xt_0>1-2\epsilon$, hence $x_3-x_0>1-4\epsilon$.
//! But it can be shown that if $B(x_0,x_1,x_2,x_3;t)$ is a monotonic
//! cubic, then $B(x_0,x_1,x_2,x_3;{1\over2})$ is always between
//! $.06[x_0,x_3]$ and $.94[x_0,x_3]$; and it is impossible for $\bar x$
//! to be within~$\epsilon$ of such a number. Contradiction!
//! (The constant .06 is actually $(2-\sqrt3\,)/4$; the worst case
//! occurs for polynomials like $B(0,2-\sqrt3,1-\sqrt3,3;t)$.)
//!
//! @ OK, now that a long theoretical preamble has justified the
//! bisection-and-doubling algorithm, we are ready to proceed with
//! its actual coding. But we still haven't discussed the
//! form of the output.
//!
//! For reasons to be discussed later, we shall find it convenient to
//! record the output as follows: Moving one step up is represented by
//! appending a `1' to a list; moving one step right is represented by
//! adding unity to the element at the end of the list. Thus, for example,
//! the net effect of ``(up, right, right, up, right)'' is to append
//! $(3,2)$.
//!
//! The list is kept in a global array called |move|. Before starting the
//! algorithm, \MF\ should check that $\\{move\_ptr}+\lfloor y_3\rfloor
//! -\lfloor y_0\rfloor\L\\{move\_size}$, so that the list won't exceed
//! the bounds of this array.
//!
//! @<Glob...@>=
//! @!move:array[0..move_size] of integer; {the recorded moves}
//! @!move_ptr:0..move_size; {the number of items in the |move| list}
//!
//! @ When bisection occurs, we ``push'' the subproblem corresponding
//! to the right-hand subinterval onto the |bisect_stack| while
//! we continue to work on the left-hand subinterval. Thus, the |bisect_stack|
//! will hold $(X_1,X_2,X_3,R,m,Y_1,Y_2,Y_3,S,n,l)$ values for
//! subproblems yet to be tackled.
//!
//! At most 15 subproblems will be on the stack at once (namely, for
//! $l=15$,~16, \dots,~29); but the stack is bigger than this, because
//! it is used also for more complicated bisection algorithms.
//!
//! @d stack_x1==bisect_stack[bisect_ptr] {stacked value of $X_1$}
//! @d stack_x2==bisect_stack[bisect_ptr+1] {stacked value of $X_2$}
//! @d stack_x3==bisect_stack[bisect_ptr+2] {stacked value of $X_3$}
//! @d stack_r==bisect_stack[bisect_ptr+3] {stacked value of $R$}
//! @d stack_m==bisect_stack[bisect_ptr+4] {stacked value of $m$}
//! @d stack_y1==bisect_stack[bisect_ptr+5] {stacked value of $Y_1$}
//! @d stack_y2==bisect_stack[bisect_ptr+6] {stacked value of $Y_2$}
//! @d stack_y3==bisect_stack[bisect_ptr+7] {stacked value of $Y_3$}
//! @d stack_s==bisect_stack[bisect_ptr+8] {stacked value of $S$}
//! @d stack_n==bisect_stack[bisect_ptr+9] {stacked value of $n$}
//! @d stack_l==bisect_stack[bisect_ptr+10] {stacked value of $l$}
//! @d move_increment=11 {number of items pushed by |make_moves|}
//!
//! @<Glob...@>=
//! @!bisect_stack:array[0..bistack_size] of integer;
//! @!bisect_ptr:0..bistack_size;
//!
//! @ @<Check the ``constant'' values...@>=
//! if 15*move_increment>bistack_size then bad:=31;
//!
//! @ The |make_moves| subroutine is given |scaled| values $(x_0,x_1,x_2,x_3)$
//! and $(y_0,y_1,y_2,y_3)$ that represent monotone-nondecreasing polynomials;
//! it makes $\lfloor x_3+\xi\rfloor-\lfloor x_0+\xi\rfloor$ rightward moves
//! and $\lfloor y_3+\eta\rfloor-\lfloor y_0+\eta\rfloor$ upward moves, as
//! explained earlier.  (Here $\lfloor x+\xi\rfloor$ actually stands for
//! $\lfloor x/2^{16}-|xi_corr|\rfloor$, if $x$ is regarded as an integer
//! without scaling.) The unscaled integers $x_k$ and~$y_k$ should be less
//! than $2^{28}$ in magnitude.
//!
//! It is assumed that $|move_ptr| + \lfloor y_3+\eta\rfloor -
//! \lfloor y_0+\eta\rfloor < |move_size|$ when this procedure is called,
//! so that the capacity of the |move| array will not be exceeded.
//!
//! The variables |r| and |s| in this procedure stand respectively for
//! $R-|xi_corr|$ and $S-|eta_corr|$ in the theory discussed above.
//!
//! @p procedure make_moves(@!xx0,@!xx1,@!xx2,@!xx3,@!yy0,@!yy1,@!yy2,@!yy3:
//!   scaled;@!xi_corr,@!eta_corr:small_number);
//! label continue, done, exit;
//! var @!x1,@!x2,@!x3,@!m,@!r,@!y1,@!y2,@!y3,@!n,@!s,@!l:integer;
//!   {bisection variables explained above}
//! @!q,@!t,@!u,@!x2a,@!x3a,@!y2a,@!y3a:integer; {additional temporary registers}
//! begin if (xx3<xx0)or(yy3<yy0) then confusion("m");
//! @:this can't happen m}{\quad m@>
//! l:=16; bisect_ptr:=0;@/
//! x1:=xx1-xx0; x2:=xx2-xx1; x3:=xx3-xx2;
//! if xx0>=xi_corr then r:=(xx0-xi_corr) mod unity
//! else r:=unity-1-((-xx0+xi_corr-1) mod unity);
//! m:=(xx3-xx0+r) div unity;@/
//! y1:=yy1-yy0; y2:=yy2-yy1; y3:=yy3-yy2;
//! if yy0>=eta_corr then s:=(yy0-eta_corr) mod unity
//! else s:=unity-1-((-yy0+eta_corr-1) mod unity);
//! n:=(yy3-yy0+s) div unity;@/
//! if (xx3-xx0>=fraction_one)or(yy3-yy0>=fraction_one) then
//!   @<Divide the variables by two, to avoid overflow problems@>;
//! loop@+  begin continue:@<Make moves for current subinterval;
//!     if bisection is necessary, push the second subinterval
//!     onto the stack, and |goto continue| in order to handle
//!     the first subinterval@>;
//!   if bisect_ptr=0 then return;
//!   @<Remove a subproblem for |make_moves| from the stack@>;
//!   end;
//! exit: end;
//!
//! @ @<Remove a subproblem for |make_moves| from the stack@>=
//! bisect_ptr:=bisect_ptr-move_increment;@/
//! x1:=stack_x1; x2:=stack_x2; x3:=stack_x3; r:=stack_r; m:=stack_m;@/
//! y1:=stack_y1; y2:=stack_y2; y3:=stack_y3; s:=stack_s; n:=stack_n;@/
//! l:=stack_l
//!
//! @ Our variables |(x1,x2,x3)| correspond to $(X_1,X_2,X_3)$ in the notation
//! of the theory developed above. We need to keep them less than $2^{28}$
//! in order to avoid integer overflow in weird circumstances.
//! For example, data like $x_0=-2^{28}+2^{16}-1$ and $x_1=x_2=x_3=2^{28}-1$
//! would otherwise be problematical. Hence this part of the code is
//! needed, if only to thwart malicious users.
//!
//! @<Divide the variables by two, to avoid overflow problems@>=
//! begin x1:=half(x1+xi_corr); x2:=half(x2+xi_corr); x3:=half(x3+xi_corr);
//! r:=half(r+xi_corr);@/
//! y1:=half(y1+eta_corr); y2:=half(y2+eta_corr); y3:=half(y3+eta_corr);
//! s:=half(s+eta_corr);@/
//! l:=15;
//! end
//!
//! @ @<Make moves...@>=
//! if m=0 then @<Move upward |n| steps@>
//! else if n=0 then @<Move to the right |m| steps@>
//! else if m+n=2 then @<Make one move of each kind@>
//! else  begin incr(l); stack_l:=l;@/
//!   stack_x3:=x3; stack_x2:=half(x2+x3+xi_corr); x2:=half(x1+x2+xi_corr);
//!   x3:=half(x2+stack_x2+xi_corr); stack_x1:=x3;@/
//!   r:=r+r+xi_corr; t:=x1+x2+x3+r;@/
//!   q:=t div two_to_the[l]; stack_r:=t mod two_to_the[l];@/
//!   stack_m:=m-q; m:=q;@/
//!   stack_y3:=y3; stack_y2:=half(y2+y3+eta_corr); y2:=half(y1+y2+eta_corr);
//!   y3:=half(y2+stack_y2+eta_corr); stack_y1:=y3;@/
//!   s:=s+s+eta_corr; u:=y1+y2+y3+s;@/
//!   q:=u div two_to_the[l]; stack_s:=u mod two_to_the[l];@/
//!   stack_n:=n-q; n:=q;@/
//!   bisect_ptr:=bisect_ptr+move_increment; goto continue;
//!   end
//!
//! @ @<Move upward |n| steps@>=
//! while n>0 do
//!   begin incr(move_ptr); move[move_ptr]:=1; decr(n);
//!   end
//!
//! @ @<Move to the right |m| steps@>=
//! move[move_ptr]:=move[move_ptr]+m
//!
//! @ @<Make one move of each kind@>=
//! begin r:=two_to_the[l]-r; s:=two_to_the[l]-s;@/
//! while l<30 do
//!   begin x3a:=x3; x2a:=half(x2+x3+xi_corr); x2:=half(x1+x2+xi_corr);
//!   x3:=half(x2+x2a+xi_corr);
//!   t:=x1+x2+x3; r:=r+r-xi_corr;@/
//!   y3a:=y3; y2a:=half(y2+y3+eta_corr); y2:=half(y1+y2+eta_corr);
//!   y3:=half(y2+y2a+eta_corr);
//!   u:=y1+y2+y3; s:=s+s-eta_corr;@/
//!   if t<r then if u<s then @<Switch to the right subinterval@>
//!     else  begin @<Move up then right@>; goto done;
//!       end
//!   else if u<s then
//!     begin @<Move right then up@>; goto done;
//!     end;
//!   incr(l);
//!   end;
//! r:=r-xi_corr; s:=s-eta_corr;
//! if ab_vs_cd(x1+x2+x3,s,y1+y2+y3,r)-xi_corr>=0 then @<Move right then up@>
//!   else @<Move up then right@>;
//! done:
//! end
//!
//! @ @<Switch to the right subinterval@>=
//! begin x1:=x3; x2:=x2a; x3:=x3a; r:=r-t;
//! y1:=y3; y2:=y2a; y3:=y3a; s:=s-u;
//! end
//!
//! @ @<Move right then up@>=
//! begin incr(move[move_ptr]); incr(move_ptr); move[move_ptr]:=1;
//! end
//!
//! @ @<Move up then right@>=
//! begin incr(move_ptr); move[move_ptr]:=2;
//! end
//!
//! @ After |make_moves| has acted, possibly for several curves that move toward
//! the same octant, a ``smoothing'' operation might be done on the |move| array.
//! This removes optical glitches that can arise even when the curve has been
//! digitized without rounding errors.
//!
//! The smoothing process replaces the integers $a_0\ldots a_n$ in
//! |move[b..t]| by ``smoothed'' integers $a_0'\ldots a_n'$ defined as
//! follows:
//! $$a_k'=a_k+\delta\k-\delta_k;\qquad
//! \delta_k=\cases{+1,&if $1<k<n$ and $a_{k-2}\G a_{k-1}\ll a_k\G a\k$;\cr
//! -1,&if $1<k<n$ and $a_{k-2}\L a_{k-1}\gg a_k\L a\k$;\cr
//! 0,&otherwise.\cr}$$
//! Here $a\ll b$ means that $a\L b-2$, and $a\gg b$ means that $a\G b+2$.
//!
//! The smoothing operation is symmetric in the sense that, if $a_0\ldots a_n$
//! smooths to $a_0'\ldots a_n'$, then the reverse sequence $a_n\ldots a_0$
//! smooths to $a_n'\ldots a_0'$; also the complementary sequence
//! $(m-a_0)\ldots(m-a_n)$ smooths to $(m-a_0')\ldots(m-a_n')$.
//! We have $a_0'+\cdots+a_n'=a_0+\cdots+a_n$ because $\delta_0=\delta_{n+1}=0$.
//!
//! @p procedure smooth_moves(@!b,@!t:integer);
//! var@!k:1..move_size; {index into |move|}
//! @!a,@!aa,@!aaa:integer; {original values of |move[k],move[k-1],move[k-2]|}
//! begin if t-b>=3 then
//!   begin k:=b+2; aa:=move[k-1]; aaa:=move[k-2];
//!   repeat a:=move[k];
//!   if abs(a-aa)>1 then
//!     @<Increase and decrease |move[k-1]| and |move[k]| by $\delta_k$@>;
//!   incr(k); aaa:=aa; aa:=a;
//!   until k=t;
//!   end;
//! end;
//!
//! @ @<Increase and decrease |move[k-1]| and |move[k]| by $\delta_k$@>=
//! if a>aa then
//!   begin if aaa>=aa then if a>=move[k+1] then
//!     begin incr(move[k-1]); move[k]:=a-1;
//!     end;
//!   end
//! else  begin if aaa<=aa then if a<=move[k+1] then
//!     begin decr(move[k-1]); move[k]:=a+1;
//!     end;
//!   end
//!
//! @* \[20] Edge structures.
//! Now we come to \MF's internal scheme for representing what the user can
//! actually ``see,'' the edges between pixels. Each pixel has an integer
//! weight, obtained by summing the weights on all edges to its left. \MF\
//! represents only the nonzero edge weights, since most of the edges are
//! weightless; in this way, the data storage requirements grow only linearly
//! with respect to the number of pixels per point, even though two-dimensional
//! data is being represented. (Well, the actual dependence on the underlying
//! resolution is order $n\log n$, but the $\log n$ factor is buried in our
//! implicit restriction on the maximum raster size.) The sum of all edge
//! weights in each row should be zero.
//!
//! The data structure for edge weights must be compact and flexible,
//! yet it should support efficient updating and display operations. We
//! want to be able to have many different edge structures in memory at
//! once, and we want the computer to be able to translate them, reflect them,
//! and/or merge them together with relative ease.
//!
//! \MF's solution to this problem requires one single-word node per
//! nonzero edge weight, plus one two-word node for each row in a contiguous
//! set of rows. There's also a header node that provides global information
//! about the entire structure.
//!
//! @ Let's consider the edge-weight nodes first. The |info| field of such
//! nodes contains both an $m$~value and a weight~$w$, in the form
//! $8m+w+c$, where $c$ is a constant that depends on data found in the header.
//! We shall consider $c$ in detail later; for now, it's best just to think
//! of it as a way to compensate for the fact that $m$ and~$w$ can be negative,
//! together with the fact that an |info| field must have a value between
//! |min_halfword| and |max_halfword|. The $m$ value is an unscaled $x$~coordinate,
//! so it satisfies $\vert m\vert<
//! 4096$; the $w$ value is always in the range $1\L\vert w\vert\L3$. We can
//! unpack the data in the |info| field by fetching |ho(info(p))=
//! info(p)-min_halfword| and dividing this nonnegative number by~8;
//! the constant~$c$ will be chosen so that the remainder of this division
//! is $4+w$. Thus, for example, a remainder of~3 will correspond to
//! the edge weight $w=-1$.
//!
//! Every row of an edge structure contains two lists of such edge-weight
//! nodes, called the |sorted| and |unsorted| lists, linked together by their
//! |link| fields in the normal way. The difference between them is that we
//! always have |info(p)<=info(link(p))| in the |sorted| list, but there's no
//! such restriction on the elements of the |unsorted| list. The reason for
//! this distinction is that it would take unnecessarily long to maintain
//! edge-weight lists in sorted order while they're being updated; but when we
//! need to process an entire row from left to right in order of the
//! $m$~values, it's fairly easy and quick to sort a short list of unsorted
//! elements and to merge them into place among their sorted cohorts.
//! Furthermore, the fact that the |unsorted| list is empty can sometimes be
//! used to good advantage, because it allows us to conclude that a particular
//! row has not changed since the last time we sorted it.
//!
//! The final |link| of the |sorted| list will be |sentinel|, which points to
//! a special one-word node whose |info| field is essentially infinite; this
//! facilitates the sorting and merging operations. The final |link| of the
//! |unsorted| list will be either |null| or |void|, where |void=null+1|
//! is used to avoid redisplaying data that has not changed:
//! A |void| value is stored at the head of the
//! unsorted list whenever the corresponding row has been displayed.
//!
//! @d zero_w=4
//! @d void==null+1
//!
//! @<Initialize table entries...@>=
//! info(sentinel):=max_halfword; {|link(sentinel)=null|}
//!
//! @ The rows themselves are represented by row header nodes that
//! contain four link fields. Two of these four, |sorted| and |unsorted|,
//! point to the first items of the edge-weight lists just mentioned.
//! The other two, |link| and |knil|, point to the headers of the two
//! adjacent rows. If |p| points to the header for row number~|n|, then
//! |link(p)| points up to the header for row~|n+1|, and |knil(p)| points
//! down to the header for row~|n-1|. This double linking makes it
//! convenient to move through consecutive rows either upward or downward;
//! as usual, we have |link(knil(p))=knil(link(p))=p| for all row headers~|p|.
//!
//! The row associated with a given value of |n| contains weights for
//! edges that run between the lattice points |(m,n)| and |(m,n+1)|.
//!
//! @d knil==info {inverse of the |link| field, in a doubly linked list}
//! @d sorted_loc(#)==#+1 {where the |sorted| link field resides}
//! @d sorted(#)==link(sorted_loc(#)) {beginning of the list of sorted edge weights}
//! @d unsorted(#)==info(#+1) {beginning of the list of unsorted edge weights}
//! @d row_node_size=2 {number of words in a row header node}
//!
//! @ The main header node |h| for an edge structure has |link| and |knil|
//! fields that link it above the topmost row and below the bottommost row.
//! It also has fields called |m_min|, |m_max|, |n_min|, and |n_max| that
//! bound the current extent of the edge data: All |m| values in edge-weight
//! nodes should lie between |m_min(h)-4096| and |m_max(h)-4096|, inclusive.
//! Furthermore the topmost row header, pointed to by |knil(h)|,
//! is for row number |n_max(h)-4096|; the bottommost row header, pointed to by
//! |link(h)|, is for row number |n_min(h)-4096|.
//!
//! The offset constant |c| that's used in all of the edge-weight data is
//! represented implicitly in |m_offset(h)|; its actual value is
//! $$\hbox{|c=min_halfword+zero_w+8*m_offset(h)|.}$$
//! Notice that it's possible to shift an entire edge structure by an
//! amount $(\Delta m,\Delta n)$ by adding $\Delta n$ to |n_min(h)| and |n_max(h)|,
//! adding $\Delta m$ to |m_min(h)| and |m_max(h)|, and subtracting
//! $\Delta m$ from |m_offset(h)|;
//! none of the other edge data needs to be modified. Initially the |m_offset|
//! field is~4096, but it will change if the user requests such a shift.
//! The contents of these five fields should always be positive and less than
//! 8192; |n_max| should, in fact, be less than 8191.  Furthermore
//! |m_min+m_offset-4096| and |m_max+m_offset-4096| must also lie strictly
//! between 0 and 8192, so that the |info| fields of edge-weight nodes will
//! fit in a halfword.
//!
//! The header node of an edge structure also contains two somewhat unusual
//! fields that are called |last_window(h)| and |last_window_time(h)|. When this
//! structure is displayed in window~|k| of the user's screen, after that
//! window has been updated |t| times, \MF\ sets |last_window(h):=k| and
//! |last_window_time(h):=t|; it also sets |unsorted(p):=void| for all row
//! headers~|p|, after merging any existing unsorted weights with the sorted
//! ones.  A subsequent display in the same window will be able to avoid
//! redisplaying rows whose |unsorted| list is still |void|, if the window
//! hasn't been used for something else in the meantime.
//!
//! A pointer to the row header of row |n_pos(h)-4096| is provided in
//! |n_rover(h)|. Most of the algorithms that update an edge structure
//! are able to get by without random row references; they usually
//! access rows that are neighbors of each other or of the current |n_pos| row.
//! Exception: If |link(h)=h| (so that the edge structure contains
//! no rows), we have |n_rover(h)=h|, and |n_pos(h)| is irrelevant.
//!
//! @d zero_field=4096 {amount added to coordinates to make them positive}
//! @d n_min(#)==info(#+1) {minimum row number present, plus |zero_field|}
//! @d n_max(#)==link(#+1) {maximum row number present, plus |zero_field|}
//! @d m_min(#)==info(#+2) {minimum column number present, plus |zero_field|}
//! @d m_max(#)==link(#+2) {maximum column number present, plus |zero_field|}
//! @d m_offset(#)==info(#+3) {translation of $m$ data in edge-weight nodes}
//! @d last_window(#)==link(#+3) {the last display went into this window}
//! @d last_window_time(#)==mem[#+4].int {after this many window updates}
//! @d n_pos(#)==info(#+5) {the row currently in |n_rover|, plus |zero_field|}
//! @d n_rover(#)==link(#+5) {a row recently referenced}
//! @d edge_header_size=6 {number of words in an edge-structure header}
//! @d valid_range(#)==(abs(#-4096)<4096) {is |#| strictly between 0 and 8192?}
//! @d empty_edges(#)==link(#)=# {are there no rows in this edge header?}
//!
//! @p procedure init_edges(@!h:pointer); {initialize an edge header to null values}
//! begin knil(h):=h; link(h):=h;@/
//! n_min(h):=zero_field+4095; n_max(h):=zero_field-4095;
//! m_min(h):=zero_field+4095; m_max(h):=zero_field-4095;
//! m_offset(h):=zero_field;@/
//! last_window(h):=0; last_window_time(h):=0;@/
//! n_rover(h):=h; n_pos(h):=0;@/
//! end;
//!
//! @ When a lot of work is being done on a particular edge structure, we plant
//! a pointer to its main header in the global variable |cur_edges|.
//! This saves us from having to pass this pointer as a parameter over and
//! over again between subroutines.
//!
//! Similarly, |cur_wt| is a global weight that is being used by several
//! procedures at once.
//!
//! @<Glob...@>=
//! @!cur_edges:pointer; {the edge structure of current interest}
//! @!cur_wt:integer; {the edge weight of current interest}
//!
//! @ The |fix_offset| routine goes through all the edge-weight nodes of
//! |cur_edges| and adds a constant to their |info| fields, so that
//! |m_offset(cur_edges)| can be brought back to |zero_field|. (This
//! is necessary only in unusual cases when the offset has gotten too
//! large or too small.)
//!
//! @p procedure fix_offset;
//! var @!p,@!q:pointer; {list traversers}
//! @!delta:integer; {the amount of change}
//! begin delta:=8*(m_offset(cur_edges)-zero_field);
//! m_offset(cur_edges):=zero_field;
//! q:=link(cur_edges);
//! while q<>cur_edges do
//!   begin p:=sorted(q);
//!   while p<>sentinel do
//!     begin info(p):=info(p)-delta; p:=link(p);
//!     end;
//!   p:=unsorted(q);
//!   while p>void do
//!     begin info(p):=info(p)-delta; p:=link(p);
//!     end;
//!   q:=link(q);
//!   end;
//! end;
//!
//! @ The |edge_prep| routine makes the |cur_edges| structure ready to
//! accept new data whose coordinates satisfy |ml<=m<=mr| and |nl<=n<=nr-1|,
//! assuming that |-4096<ml<=mr<4096| and |-4096<nl<=nr<4096|. It makes
//! appropriate adjustments to |m_min|, |m_max|, |n_min|, and |n_max|,
//! adding new empty rows if necessary.
//!
//! @p procedure edge_prep(@!ml,@!mr,@!nl,@!nr:integer);
//! var @!delta:halfword; {amount of change}
//! @!p,@!q:pointer; {for list manipulation}
//! begin ml:=ml+zero_field; mr:=mr+zero_field;
//! nl:=nl+zero_field; nr:=nr-1+zero_field;@/
//! if ml<m_min(cur_edges) then m_min(cur_edges):=ml;
//! if mr>m_max(cur_edges) then m_max(cur_edges):=mr;
//! if not valid_range(m_min(cur_edges)+m_offset(cur_edges)-zero_field) or@|
//!  not valid_range(m_max(cur_edges)+m_offset(cur_edges)-zero_field) then
//!   fix_offset;
//! if empty_edges(cur_edges) then {there are no rows}
//!   begin n_min(cur_edges):=nr+1; n_max(cur_edges):=nr;
//!   end;
//! if nl<n_min(cur_edges) then
//!   @<Insert exactly |n_min(cur_edges)-nl| empty rows at the bottom@>;
//! if nr>n_max(cur_edges) then
//!   @<Insert exactly |nr-n_max(cur_edges)| empty rows at the top@>;
//! end;
//!
//! @ @<Insert exactly |n_min(cur_edges)-nl| empty rows at the bottom@>=
//! begin delta:=n_min(cur_edges)-nl; n_min(cur_edges):=nl;
//! p:=link(cur_edges);
//! repeat q:=get_node(row_node_size); sorted(q):=sentinel; unsorted(q):=void;
//! knil(p):=q; link(q):=p; p:=q; decr(delta);
//! until delta=0;
//! knil(p):=cur_edges; link(cur_edges):=p;
//! if n_rover(cur_edges)=cur_edges then n_pos(cur_edges):=nl-1;
//! end
//!
//! @ @<Insert exactly |nr-n_max(cur_edges)| empty rows at the top@>=
//! begin delta:=nr-n_max(cur_edges); n_max(cur_edges):=nr;
//! p:=knil(cur_edges);
//! repeat q:=get_node(row_node_size); sorted(q):=sentinel; unsorted(q):=void;
//! link(p):=q; knil(q):=p; p:=q; decr(delta);
//! until delta=0;
//! link(p):=cur_edges; knil(cur_edges):=p;
//! if n_rover(cur_edges)=cur_edges then n_pos(cur_edges):=nr+1;
//! end
//!
//! @ The |print_edges| subroutine gives a symbolic rendition of an edge
//! structure, for use in `\&{show}' commands. A rather terse output
//! format has been chosen since edge structures can grow quite large.
//!
//! @<Declare subroutines for printing expressions@>=
//! @t\4@>@<Declare the procedure called |print_weight|@>@;@/
//! procedure print_edges(@!s:str_number;@!nuline:boolean;@!x_off,@!y_off:integer);
//! var @!p,@!q,@!r:pointer; {for list traversal}
//! @!n:integer; {row number}
//! begin print_diagnostic("Edge structure",s,nuline);
//! p:=knil(cur_edges); n:=n_max(cur_edges)-zero_field;
//! while p<>cur_edges do
//!   begin q:=unsorted(p); r:=sorted(p);
//!   if(q>void)or(r<>sentinel) then
//!     begin print_nl("row "); print_int(n+y_off); print_char(":");
//!     while q>void do
//!       begin print_weight(q,x_off); q:=link(q);
//!       end;
//!     print(" |");
//!     while r<>sentinel do
//!       begin print_weight(r,x_off); r:=link(r);
//!       end;
//!     end;
//!   p:=knil(p); decr(n);
//!   end;
//! end_diagnostic(true);
//! end;
//!
//! @ @<Declare the procedure called |print_weight|@>=
//! procedure print_weight(@!q:pointer;@!x_off:integer);
//! var @!w,@!m:integer; {unpacked weight and coordinate}
//! @!d:integer; {temporary data register}
//! begin d:=ho(info(q)); w:=d mod 8; m:=(d div 8)-m_offset(cur_edges);
//! if file_offset>max_print_line-9 then print_nl(" ")
//! else print_char(" ");
//! print_int(m+x_off);
//! while w>zero_w do
//!   begin print_char("+"); decr(w);
//!   end;
//! while w<zero_w do
//!   begin print_char("-"); incr(w);
//!   end;
//! end;
//!
//! @ Here's a trivial subroutine that copies an edge structure. (Let's hope
//! that the given structure isn't too gigantic.)
//!
//! @p function copy_edges(@!h:pointer):pointer;
//! var @!p,@!r:pointer; {variables that traverse the given structure}
//! @!hh,@!pp,@!qq,@!rr,@!ss:pointer; {variables that traverse the new structure}
//! begin hh:=get_node(edge_header_size);
//! mem[hh+1]:=mem[h+1]; mem[hh+2]:=mem[h+2];
//! mem[hh+3]:=mem[h+3]; mem[hh+4]:=mem[h+4]; {we've now copied |n_min|, |n_max|,
//!   |m_min|, |m_max|, |m_offset|, |last_window|, and |last_window_time|}
//! n_pos(hh):=n_max(hh)+1;n_rover(hh):=hh;@/
//! p:=link(h); qq:=hh;
//! while p<>h do
//!   begin pp:=get_node(row_node_size); link(qq):=pp; knil(pp):=qq;
//!   @<Copy both |sorted| and |unsorted| lists of |p| to |pp|@>;
//!   p:=link(p); qq:=pp;
//!   end;
//! link(qq):=hh; knil(hh):=qq;
//! copy_edges:=hh;
//! end;
//!
//! @ @<Copy both |sorted| and |unsorted|...@>=
//! r:=sorted(p); rr:=sorted_loc(pp); {|link(rr)=sorted(pp)|}
//! while r<>sentinel do
//!   begin ss:=get_avail; link(rr):=ss; rr:=ss; info(rr):=info(r);@/
//!   r:=link(r);
//!   end;
//! link(rr):=sentinel;@/
//! r:=unsorted(p); rr:=temp_head;
//! while r>void do
//!   begin ss:=get_avail; link(rr):=ss; rr:=ss; info(rr):=info(r);@/
//!   r:=link(r);
//!   end;
//! link(rr):=r; unsorted(pp):=link(temp_head)
//!
//! @ Another trivial routine flips |cur_edges| about the |x|-axis
//! (i.e., negates all the |y| coordinates), assuming that at least
//! one row is present.
//!
//! @p procedure y_reflect_edges;
//! var @!p,@!q,@!r:pointer; {list manipulation registers}
//! begin p:=n_min(cur_edges);
//! n_min(cur_edges):=zero_field+zero_field-1-n_max(cur_edges);
//! n_max(cur_edges):=zero_field+zero_field-1-p;
//! n_pos(cur_edges):=zero_field+zero_field-1-n_pos(cur_edges);@/
//! p:=link(cur_edges); q:=cur_edges; {we assume that |p<>q|}
//! repeat r:=link(p); link(p):=q; knil(q):=p; q:=p; p:=r;
//! until q=cur_edges;
//! last_window_time(cur_edges):=0;
//! end;
//!
//! @ It's somewhat more difficult, yet not too hard, to reflect about the |y|-axis.
//!
//! @p procedure x_reflect_edges;
//! var @!p,@!q,@!r,@!s:pointer; {list manipulation registers}
//! @!m:integer; {|info| fields will be reflected with respect to this number}
//! begin p:=m_min(cur_edges);
//! m_min(cur_edges):=zero_field+zero_field-m_max(cur_edges);
//! m_max(cur_edges):=zero_field+zero_field-p;
//! m:=(zero_field+m_offset(cur_edges))*8+zero_w+min_halfword+zero_w+min_halfword;
//! m_offset(cur_edges):=zero_field;
//! p:=link(cur_edges);
//! repeat @<Reflect the edge-and-weight data in |sorted(p)|@>;
//! @<Reflect the edge-and-weight data in |unsorted(p)|@>;
//! p:=link(p);
//! until p=cur_edges;
//! last_window_time(cur_edges):=0;
//! end;
//!
//! @ We want to change the sign of the weight as we change the sign of the
//! |x|~coordinate. Fortunately, it's easier to do this than to negate
//! one without the other.
//!
//! @<Reflect the edge-and-weight data in |unsorted(p)|@>=
//! q:=unsorted(p);
//! while q>void do
//!   begin info(q):=m-info(q); q:=link(q);
//!   end
//!
//! @ Reversing the order of a linked list is best thought of as the process of
//! popping nodes off one stack and pushing them on another. In this case we
//! pop from stack~|q| and push to stack~|r|.
//!
//! @<Reflect the edge-and-weight data in |sorted(p)|@>=
//! q:=sorted(p); r:=sentinel;
//! while q<>sentinel do
//!   begin s:=link(q); link(q):=r; r:=q; info(r):=m-info(q); q:=s;
//!   end;
//! sorted(p):=r
//!
//! @ Now let's multiply all the $y$~coordinates of a nonempty edge structure
//! by a small integer $s>1$:
//!
//! @p procedure y_scale_edges(@!s:integer);
//! var @!p,@!q,@!pp,@!r,@!rr,@!ss:pointer; {list manipulation registers}
//! @!t:integer; {replication counter}
//! begin if (s*(n_max(cur_edges)+1-zero_field)>=4096) or@|
//!  (s*(n_min(cur_edges)-zero_field)<=-4096) then
//!   begin print_err("Scaled picture would be too big");
//! @.Scaled picture...big@>
//!   help3("I can't yscale the picture as requested---it would")@/
//!     ("make some coordinates too large or too small.")@/
//!     ("Proceed, and I'll omit the transformation.");
//!   put_get_error;
//!   end
//! else  begin n_max(cur_edges):=s*(n_max(cur_edges)+1-zero_field)-1+zero_field;
//!   n_min(cur_edges):=s*(n_min(cur_edges)-zero_field)+zero_field;
//!   @<Replicate every row exactly $s$ times@>;
//!   last_window_time(cur_edges):=0;
//!   end;
//! end;
//!
//! @ @<Replicate...@>=
//! p:=cur_edges;
//! repeat q:=p; p:=link(p);
//! for t:=2 to s do
//!   begin pp:=get_node(row_node_size); link(q):=pp; knil(p):=pp;
//!   link(pp):=p; knil(pp):=q; q:=pp;
//!   @<Copy both |sorted| and |unsorted|...@>;
//!   end;
//! until link(p)=cur_edges
//!
//! @ Scaling the $x$~coordinates is, of course, our next task.
//!
//! @p procedure x_scale_edges(@!s:integer);
//! var @!p,@!q:pointer; {list manipulation registers}
//! @!t:0..65535; {unpacked |info| field}
//! @!w:0..7; {unpacked weight}
//! @!delta:integer; {amount added to scaled |info|}
//! begin if (s*(m_max(cur_edges)-zero_field)>=4096) or@|
//!  (s*(m_min(cur_edges)-zero_field)<=-4096) then
//!   begin print_err("Scaled picture would be too big");
//! @.Scaled picture...big@>
//!   help3("I can't xscale the picture as requested---it would")@/
//!     ("make some coordinates too large or too small.")@/
//!     ("Proceed, and I'll omit the transformation.");
//!   put_get_error;
//!   end
//! else if (m_max(cur_edges)<>zero_field)or(m_min(cur_edges)<>zero_field) then
//!   begin m_max(cur_edges):=s*(m_max(cur_edges)-zero_field)+zero_field;
//!   m_min(cur_edges):=s*(m_min(cur_edges)-zero_field)+zero_field;
//!   delta:=8*(zero_field-s*m_offset(cur_edges))+min_halfword;
//!   m_offset(cur_edges):=zero_field;@/
//!   @<Scale the $x$~coordinates of each row by $s$@>;
//!   last_window_time(cur_edges):=0;
//!   end;
//! end;
//!
//! @ The multiplications cannot overflow because we know that |s<4096|.
//!
//! @<Scale the $x$~coordinates of each row by $s$@>=
//! q:=link(cur_edges);
//! repeat p:=sorted(q);
//! while p<>sentinel do
//!   begin t:=ho(info(p)); w:=t mod 8; info(p):=(t-w)*s+w+delta; p:=link(p);
//!   end;
//! p:=unsorted(q);
//! while p>void do
//!   begin t:=ho(info(p)); w:=t mod 8; info(p):=(t-w)*s+w+delta; p:=link(p);
//!   end;
//! q:=link(q);
//! until q=cur_edges
//!
//! @ Here is a routine that changes the signs of all the weights, without
//! changing anything else.
//!
//! @p procedure negate_edges(@!h:pointer);
//! label done;
//! var @!p,@!q,@!r,@!s,@!t,@!u:pointer; {structure traversers}
//! begin p:=link(h);
//! while p<>h do
//!   begin q:=unsorted(p);
//!   while q>void do
//!     begin info(q):=8-2*((ho(info(q))) mod 8)+info(q); q:=link(q);
//!     end;
//!   q:=sorted(p);
//!   if q<>sentinel then
//!     begin repeat info(q):=8-2*((ho(info(q))) mod 8)+info(q); q:=link(q);
//!     until q=sentinel;
//!     @<Put the list |sorted(p)| back into sort@>;
//!     end;
//!   p:=link(p);
//!   end;
//! last_window_time(h):=0;
//! end;
//!
//! @ \MF\ would work even if the code in this section were omitted, because
//! a list of edge-and-weight data that is sorted only by
//! |m| but not~|w| turns out to be good enough for correct operation.
//! However, the author decided not to make the program even trickier than
//! it is already, since |negate_edges| isn't needed very often.
//! The simpler-to-state condition, ``keep the |sorted| list fully sorted,''
//! is therefore being preserved at the cost of extra computation.
//!
//! @<Put the list |sorted(p)|...@>=
//! u:=sorted_loc(p); q:=link(u); r:=q; s:=link(r); {|q=sorted(p)|}
//! loop@+  if info(s)>info(r) then
//!     begin link(u):=q;
//!     if s=sentinel then goto done;
//!     u:=r; q:=s; r:=q; s:=link(r);
//!     end
//!   else  begin t:=s; s:=link(t); link(t):=q; q:=t;
//!     end;
//! done: link(r):=sentinel
//!
//! @ The |unsorted| edges of a row are merged into the |sorted| ones by
//! a subroutine called |sort_edges|. It uses simple insertion sort,
//! followed by a merge, because the unsorted list is supposedly quite short.
//! However, the unsorted list is assumed to be nonempty.
//!
//! @p procedure sort_edges(@!h:pointer); {|h| is a row header}
//! label done;
//! var @!k:halfword; {key register that we compare to |info(q)|}
//! @!p,@!q,@!r,@!s:pointer;
//! begin r:=unsorted(h); unsorted(h):=null;
//! p:=link(r); link(r):=sentinel; link(temp_head):=r;
//! while p>void do {sort node |p| into the list that starts at |temp_head|}
//!   begin k:=info(p); q:=temp_head;
//!   repeat r:=q; q:=link(r);
//!   until k<=info(q);
//!   link(r):=p; r:=link(p); link(p):=q; p:=r;
//!   end;
//! @<Merge the |temp_head| list into |sorted(h)|@>;
//! end;
//!
//! @ In this step we use the fact that |sorted(h)=link(sorted_loc(h))|.
//!
//! @<Merge the |temp_head| list into |sorted(h)|@>=
//! begin r:=sorted_loc(h); q:=link(r); p:=link(temp_head);
//! loop@+  begin k:=info(p);
//!   while k>info(q) do
//!     begin r:=q; q:=link(r);
//!     end;
//!   link(r):=p; s:=link(p); link(p):=q;
//!   if s=sentinel then goto done;
//!   r:=p; p:=s;
//!   end;
//! done:end
//!
//! @ The |cull_edges| procedure ``optimizes'' an edge structure by making all
//! the pixel weights either |w_out| or~|w_in|. The weight will be~|w_in| after the
//! operation if and only if it was in the closed interval |[w_lo,w_hi]|
//! before, where |w_lo<=w_hi|. Either |w_out| or |w_in| is zero, while the other is
//! $\pm1$, $\pm2$, or $\pm3$. The parameters will be such that zero-weight
//! pixels will remain of weight zero.  (This is fortunate,
//! because there are infinitely many of them.)
//!
//! The procedure also computes the tightest possible bounds on the resulting
//! data, by updating |m_min|, |m_max|, |n_min|, and~|n_max|.
//!
//! @p procedure cull_edges(@!w_lo,@!w_hi,@!w_out,@!w_in:integer);
//! label done;
//! var @!p,@!q,@!r,@!s:pointer; {for list manipulation}
//! @!w:integer; {new weight after culling}
//! @!d:integer; {data register for unpacking}
//! @!m:integer; {the previous column number, including |m_offset|}
//! @!mm:integer; {the next column number, including |m_offset|}
//! @!ww:integer; {accumulated weight before culling}
//! @!prev_w:integer; {value of |w| before column |m|}
//! @!n,@!min_n,@!max_n:pointer; {current and extreme row numbers}
//! @!min_d,@!max_d:pointer; {extremes of the new edge-and-weight data}
//! begin min_d:=max_halfword; max_d:=min_halfword;
//! min_n:=max_halfword; max_n:=min_halfword;@/
//! p:=link(cur_edges); n:=n_min(cur_edges);
//! while p<>cur_edges do
//!   begin if unsorted(p)>void then sort_edges(p);
//!   if sorted(p)<>sentinel then
//!     @<Cull superfluous edge-weight entries from |sorted(p)|@>;
//!   p:=link(p); incr(n);
//!   end;
//! @<Delete empty rows at the top and/or bottom;
//!   update the boundary values in the header@>;
//! last_window_time(cur_edges):=0;
//! end;
//!
//! @ The entire |sorted| list is returned to available memory in this step;
//! a new list is built starting (temporarily) at |temp_head|.
//! Since several edges can occur at the same column, we need to be looking
//! ahead of where the actual culling takes place. This means that it's
//! slightly tricky to get the iteration started and stopped.
//!
//! @<Cull superfluous...@>=
//! begin r:=temp_head; q:=sorted(p); ww:=0; m:=1000000; prev_w:=0;
//! loop@+  begin if q=sentinel then mm:=1000000
//!   else  begin d:=ho(info(q)); mm:=d div 8; ww:=ww+(d mod 8)-zero_w;
//!     end;
//!   if mm>m then
//!     begin @<Insert an edge-weight for edge |m|, if the new pixel
//!       weight has changed@>;
//!     if q=sentinel then goto done;
//!     end;
//!   m:=mm;
//!   if ww>=w_lo then if ww<=w_hi then w:=w_in
//!     else w:=w_out
//!   else w:=w_out;
//!   s:=link(q); free_avail(q); q:=s;
//!   end;
//! done: link(r):=sentinel; sorted(p):=link(temp_head);
//! if r<>temp_head then @<Update the max/min amounts@>;
//! end
//!
//! @ @<Insert an edge-weight for edge |m|, if...@>=
//! if w<>prev_w then
//!   begin s:=get_avail; link(r):=s;
//!   info(s):=8*m+min_halfword+zero_w+w-prev_w;
//!   r:=s; prev_w:=w;
//!   end
//!
//! @ @<Update the max/min amounts@>=
//! begin if min_n=max_halfword then min_n:=n;
//! max_n:=n;
//! if min_d>info(link(temp_head)) then min_d:=info(link(temp_head));
//! if max_d<info(r) then max_d:=info(r);
//! end
//!
//! @ @<Delete empty rows at the top and/or bottom...@>=
//! if min_n>max_n then @<Delete all the row headers@>
//! else  begin n:=n_min(cur_edges); n_min(cur_edges):=min_n;
//!   while min_n>n do
//!     begin p:=link(cur_edges); link(cur_edges):=link(p);
//!     knil(link(p)):=cur_edges;
//!     free_node(p,row_node_size); incr(n);
//!     end;
//!   n:=n_max(cur_edges); n_max(cur_edges):=max_n;
//!   n_pos(cur_edges):=max_n+1; n_rover(cur_edges):=cur_edges;
//!   while max_n<n do
//!     begin p:=knil(cur_edges); knil(cur_edges):=knil(p);
//!     link(knil(p)):=cur_edges;
//!     free_node(p,row_node_size); decr(n);
//!     end;
//!   m_min(cur_edges):=((ho(min_d)) div 8)-m_offset(cur_edges)+zero_field;
//!   m_max(cur_edges):=((ho(max_d)) div 8)-m_offset(cur_edges)+zero_field;
//!   end
//!
//! @ We get here if the edges have been entirely culled away.
//!
//! @<Delete all the row headers@>=
//! begin p:=link(cur_edges);
//! while p<>cur_edges do
//!   begin q:=link(p); free_node(p,row_node_size); p:=q;
//!   end;
//! init_edges(cur_edges);
//! end
//!
//!
//! @ The last and most difficult routine for transforming an edge structure---and
//! the most interesting one!---is |xy_swap_edges|, which interchanges the
//! r\^^Doles of rows and columns. Its task can be viewed as the job of
//! creating an edge structure that contains only horizontal edges, linked
//! together in columns, given an edge structure that contains only
//! vertical edges linked together in rows; we must do this without changing
//! the implied pixel weights.
//!
//! Given any two adjacent rows of an edge structure, it is not difficult to
//! determine the horizontal edges that lie ``between'' them: We simply look
//! for vertically adjacent pixels that have different weight, and insert
//! a horizontal edge containing the difference in weights. Every horizontal
//! edge determined in this way should be put into an appropriate linked
//! list. Since random access to these linked lists is desirable, we use
//! the |move| array to hold the list heads. If we work through the given
//! edge structure from top to bottom, the constructed lists will not need
//! to be sorted, since they will already be in order.
//!
//! The following algorithm makes use of some ideas suggested by John Hobby.
//! @^Hobby, John Douglas@>
//! It assumes that the edge structure is non-null, i.e., that |link(cur_edges)
//! <>cur_edges|, hence |m_max(cur_edges)>=m_min(cur_edges)|.
//!
//! @p procedure xy_swap_edges; {interchange |x| and |y| in |cur_edges|}
//! label done;
//! var @!m_magic,@!n_magic:integer; {special values that account for offsets}
//! @!p,@!q,@!r,@!s:pointer; {pointers that traverse the given structure}
//! @<Other local variables for |xy_swap_edges|@>@;
//! begin @<Initialize the array of new edge list heads@>;
//! @<Insert blank rows at the top and bottom, and set |p| to the new top row@>;
//! @<Compute the magic offset values@>;
//! repeat q:=knil(p);@+if unsorted(q)>void then sort_edges(q);
//! @<Insert the horizontal edges defined by adjacent rows |p,q|,
//!   and destroy row~|p|@>;
//! p:=q; n_magic:=n_magic-8;
//! until knil(p)=cur_edges;
//! free_node(p,row_node_size); {now all original rows have been recycled}
//! @<Adjust the header to reflect the new edges@>;
//! end;
//!
//! @ Here we don't bother to keep the |link| entries up to date, since the
//! procedure looks only at the |knil| fields as it destroys the former
//! edge structure.
//!
//! @<Insert blank rows at the top and bottom...@>=
//! p:=get_node(row_node_size); sorted(p):=sentinel; unsorted(p):=null;@/
//! knil(p):=cur_edges; knil(link(cur_edges)):=p; {the new bottom row}
//! p:=get_node(row_node_size); sorted(p):=sentinel;
//! knil(p):=knil(cur_edges); {the new top row}
//!
//! @ The new lists will become |sorted| lists later, so we initialize
//! empty lists to |sentinel|.
//!
//! @<Initialize the array of new edge list heads@>=
//! m_spread:=m_max(cur_edges)-m_min(cur_edges); {this is |>=0| by assumption}
//! if m_spread>move_size then overflow("move table size",move_size);
//! @:METAFONT capacity exceeded move table size}{\quad move table size@>
//! for j:=0 to m_spread do move[j]:=sentinel
//!
//! @ @<Other local variables for |xy_swap_edges|@>=
//! @!m_spread:integer; {the difference between |m_max| and |m_min|}
//! @!j,@!jj:0..move_size; {indices into |move|}
//! @!m,@!mm:integer; {|m| values at vertical edges}
//! @!pd,@!rd:integer; {data fields from edge-and-weight nodes}
//! @!pm,@!rm:integer; {|m| values from edge-and-weight nodes}
//! @!w:integer; {the difference in accumulated weight}
//! @!ww:integer; {as much of |w| that can be stored in a single node}
//! @!dw:integer; {an increment to be added to |w|}
//!
//! @ At the point where we test |w<>0|, variable |w| contains
//! the accumulated weight from edges already passed in
//! row~|p| minus the accumulated weight from edges already passed in row~|q|.
//!
//! @<Insert the horizontal edges defined by adjacent rows |p,q|...@>=
//! r:=sorted(p); free_node(p,row_node_size); p:=r;@/
//! pd:=ho(info(p)); pm:=pd div 8;@/
//! r:=sorted(q); rd:=ho(info(r)); rm:=rd div 8; w:=0;
//! loop@+  begin if pm<rm then mm:=pm@+else mm:=rm;
//!   if w<>0 then
//!     @<Insert horizontal edges of weight |w| between |m| and~|mm|@>;
//!   if pd<rd then
//!     begin dw:=(pd mod 8)-zero_w;
//!     @<Advance pointer |p| to the next vertical edge,
//!       after destroying the previous one@>;
//!     end
//!   else  begin if r=sentinel then goto done; {|rd=pd=ho(max_halfword)|}
//!     dw:=-((rd mod 8)-zero_w);
//!     @<Advance pointer |r| to the next vertical edge@>;
//!     end;
//!   m:=mm; w:=w+dw;
//!   end;
//! done:
//!
//! @ @<Advance pointer |r| to the next vertical edge@>=
//! r:=link(r); rd:=ho(info(r)); rm:=rd div 8
//!
//! @ @<Advance pointer |p| to the next vertical edge...@>=
//! s:=link(p); free_avail(p); p:=s; pd:=ho(info(p)); pm:=pd div 8
//!
//! @ Certain ``magic'' values are needed to make the following code work,
//! because of the various offsets in our data structure. For now, let's not
//! worry about their precise values; we shall compute |m_magic| and |n_magic|
//! later, after we see what the code looks like.
//!
//! @ @<Insert horizontal edges of weight |w| between |m| and~|mm|@>=
//! if m<>mm then
//!   begin if mm-m_magic>=move_size then confusion("xy");
//! @:this can't happen xy}{\quad xy@>
//!   extras:=(abs(w)-1) div 3;
//!   if extras>0 then
//!     begin if w>0 then xw:=+3@+else xw:=-3;
//!     ww:=w-extras*xw;
//!     end
//!   else ww:=w;
//!   repeat j:=m-m_magic;
//!   for k:=1 to extras do
//!     begin s:=get_avail; info(s):=n_magic+xw;
//!     link(s):=move[j]; move[j]:=s;
//!     end;
//!   s:=get_avail; info(s):=n_magic+ww;
//!   link(s):=move[j]; move[j]:=s;@/
//!   incr(m);
//!   until m=mm;
//!   end
//!
//! @ @<Other local variables for |xy...@>=
//! @!extras:integer; {the number of additional nodes to make weights |>3|}
//! @!xw:-3..3; {the additional weight in extra nodes}
//! @!k:integer; {loop counter for inserting extra nodes}
//!
//! @ At the beginning of this step, |move[m_spread]=sentinel|, because no
//! horizontal edges will extend to the right of column |m_max(cur_edges)|.
//!
//! @<Adjust the header to reflect the new edges@>=
//! move[m_spread]:=0; j:=0;
//! while move[j]=sentinel do incr(j);
//! if j=m_spread then init_edges(cur_edges) {all edge weights are zero}
//! else  begin mm:=m_min(cur_edges);
//!   m_min(cur_edges):=n_min(cur_edges);
//!   m_max(cur_edges):=n_max(cur_edges)+1;
//!   m_offset(cur_edges):=zero_field;
//!   jj:=m_spread-1;
//!   while move[jj]=sentinel do decr(jj);
//!   n_min(cur_edges):=j+mm; n_max(cur_edges):=jj+mm; q:=cur_edges;
//!   repeat p:=get_node(row_node_size); link(q):=p; knil(p):=q;
//!   sorted(p):=move[j]; unsorted(p):=null; incr(j); q:=p;
//!   until j>jj;
//!   link(q):=cur_edges; knil(cur_edges):=q;
//!   n_pos(cur_edges):=n_max(cur_edges)+1; n_rover(cur_edges):=cur_edges;
//!   last_window_time(cur_edges):=0;
//!   end;
//!
//! @ The values of |m_magic| and |n_magic| can be worked out by trying the
//! code above on a small example; if they work correctly in simple cases,
//! they should work in general.
//!
//! @<Compute the magic offset values@>=
//! m_magic:=m_min(cur_edges)+m_offset(cur_edges)-zero_field;
//! n_magic:=8*n_max(cur_edges)+8+zero_w+min_halfword
//!
//! @ Now let's look at the subroutine that merges the edges from a given
//! edge structure into |cur_edges|. The given edge structure loses all its
//! edges.
//!
//! @p procedure merge_edges(@!h:pointer);
//! label done;
//! var @!p,@!q,@!r,@!pp,@!qq,@!rr:pointer; {list manipulation registers}
//! @!n:integer; {row number}
//! @!k:halfword; {key register that we compare to |info(q)|}
//! @!delta:integer; {change to the edge/weight data}
//! begin if link(h)<>h then
//!   begin if (m_min(h)<m_min(cur_edges))or(m_max(h)>m_max(cur_edges))or@|
//!     (n_min(h)<n_min(cur_edges))or(n_max(h)>n_max(cur_edges)) then
//!     edge_prep(m_min(h)-zero_field,m_max(h)-zero_field,
//!       n_min(h)-zero_field,n_max(h)-zero_field+1);
//!   if m_offset(h)<>m_offset(cur_edges) then
//!     @<Adjust the data of |h| to account for a difference of offsets@>;
//!   n:=n_min(cur_edges); p:=link(cur_edges); pp:=link(h);
//!   while n<n_min(h) do
//!     begin incr(n); p:=link(p);
//!     end;
//!   repeat @<Merge row |pp| into row |p|@>;
//!   pp:=link(pp); p:=link(p);
//!   until pp=h;
//!   end;
//! end;
//!
//! @ @<Adjust the data of |h| to account for a difference of offsets@>=
//! begin pp:=link(h); delta:=8*(m_offset(cur_edges)-m_offset(h));
//! repeat qq:=sorted(pp);
//! while qq<>sentinel do
//!   begin info(qq):=info(qq)+delta; qq:=link(qq);
//!   end;
//! qq:=unsorted(pp);
//! while qq>void do
//!   begin info(qq):=info(qq)+delta; qq:=link(qq);
//!   end;
//! pp:=link(pp);
//! until pp=h;
//! end
//!
//! @ The |sorted| and |unsorted| lists are merged separately. After this
//! step, row~|pp| will have no edges remaining, since they will all have
//! been merged into row~|p|.
//!
//! @<Merge row |pp|...@>=
//! qq:=unsorted(pp);
//! if qq>void then
//!   if unsorted(p)<=void then unsorted(p):=qq
//!   else  begin while link(qq)>void do qq:=link(qq);
//!     link(qq):=unsorted(p); unsorted(p):=unsorted(pp);
//!     end;
//! unsorted(pp):=null; qq:=sorted(pp);
//! if qq<>sentinel then
//!   begin if unsorted(p)=void then unsorted(p):=null;
//!   sorted(pp):=sentinel; r:=sorted_loc(p); q:=link(r); {|q=sorted(p)|}
//!   if q=sentinel then sorted(p):=qq
//!   else loop@+begin k:=info(qq);
//!     while k>info(q) do
//!       begin r:=q; q:=link(r);
//!       end;
//!     link(r):=qq; rr:=link(qq); link(qq):=q;
//!     if rr=sentinel then goto done;
//!     r:=qq; qq:=rr;
//!     end;
//!   end;
//! done:
//!
//! @ The |total_weight| routine computes the total of all pixel weights
//! in a given edge structure. It's not difficult to prove that this is
//! the sum of $(-w)$ times $x$ taken over all edges,
//! where $w$ and~$x$ are the weight and $x$~coordinates stored in an edge.
//! It's not necessary to worry that this quantity will overflow the
//! size of an |integer| register, because it will be less than~$2^{31}$
//! unless the edge structure has more than 174,762 edges. However, we had
//! better not try to compute it as a |scaled| integer, because a total
//! weight of almost $12\times 2^{12}$ can be produced by only four edges.
//!
//! @p function total_weight(@!h:pointer):integer; {|h| is an edge header}
//! var @!p,@!q:pointer; {variables that traverse the given structure}
//! @!n:integer; {accumulated total so far}
//! @!m:0..65535; {packed $x$ and $w$ values, including offsets}
//! begin n:=0; p:=link(h);
//! while p<>h do
//!   begin q:=sorted(p);
//!   while q<>sentinel do
//!     @<Add the contribution of node |q| to the total weight,
//!       and set |q:=link(q)|@>;
//!   q:=unsorted(p);
//!   while q>void do
//!     @<Add the contribution of node |q| to the total weight,
//!       and set |q:=link(q)|@>;
//!   p:=link(p);
//!   end;
//! total_weight:=n;
//! end;
//!
//! @ It's not necessary to add the offsets to the $x$ coordinates, because
//! an entire edge structure can be shifted without affecting its total weight.
//! Similarly, we don't need to subtract |zero_field|.
//!
//! @<Add the contribution of node |q| to the total weight...@>=
//! begin m:=ho(info(q)); n:=n-((m mod 8)-zero_w)*(m div 8);
//! q:=link(q);
//! end
//!
//! @ So far we've done lots of things to edge structures assuming that
//! edges are actually present, but we haven't seen how edges get created
//! in the first place. Let's turn now to the problem of generating new edges.
//!
//! \MF\ will display new edges as they are being computed, if |tracing_edges|
//! is positive. In order to keep such data reasonably compact, only the
//! points at which the path makes a $90^\circ$ or $180^\circ$ turn are listed.
//!
//! The tracing algorithm must remember some past history in order to suppress
//! unnecessary data. Three variables |trace_x|, |trace_y|, and |trace_yy|
//! provide this history: The last coordinates printed were |(trace_x,trace_y)|,
//! and the previous edge traced ended at |(trace_x,trace_yy)|. Before anything
//! at all has been traced, |trace_x=-4096|.
//!
//! @<Glob...@>=
//! @!trace_x:integer; {$x$~coordinate most recently shown in a trace}
//! @!trace_y:integer; {$y$~coordinate most recently shown in a trace}
//! @!trace_yy:integer; {$y$~coordinate most recently encountered}
//!
//! @ Edge tracing is initiated by the |begin_edge_tracing| routine,
//! continued by the |trace_a_corner| routine, and terminated by the
//! |end_edge_tracing| routine.
//!
//! @p procedure begin_edge_tracing;
//! begin print_diagnostic("Tracing edges","",true);
//! print(" (weight "); print_int(cur_wt); print_char(")"); trace_x:=-4096;
//! end;
//! @#
//! procedure trace_a_corner;
//! begin if file_offset>max_print_line-13 then print_nl("");
//! print_char("("); print_int(trace_x); print_char(","); print_int(trace_yy);
//! print_char(")"); trace_y:=trace_yy;
//! end;
//! @#
//! procedure end_edge_tracing;
//! begin if trace_x=-4096 then print_nl("(No new edges added.)")
//! @.No new edges added@>
//! else  begin trace_a_corner; print_char(".");
//!   end;
//! end_diagnostic(true);
//! end;
//!
//! @ Just after a new edge weight has been put into the |info| field of
//! node~|r|, in row~|n|, the following routine continues an ongoing trace.
//!
//! @p procedure trace_new_edge(@!r:pointer;@!n:integer);
//! var @!d:integer; {temporary data register}
//! @!w:-3..3; {weight associated with an edge transition}
//! @!m,@!n0,@!n1:integer; {column and row numbers}
//! begin d:=ho(info(r)); w:=(d mod 8)-zero_w; m:=(d div 8)-m_offset(cur_edges);
//! if w=cur_wt then
//!   begin n0:=n+1; n1:=n;
//!   end
//! else  begin n0:=n; n1:=n+1;
//!   end; {the edges run from |(m,n0)| to |(m,n1)|}
//! if m<>trace_x then
//!   begin if trace_x=-4096 then
//!     begin print_nl(""); trace_yy:=n0;
//!     end
//!   else if trace_yy<>n0 then print_char("?") {shouldn't happen}
//!   else trace_a_corner;
//!   trace_x:=m; trace_a_corner;
//!   end
//! else  begin if n0<>trace_yy then print_char("!"); {shouldn't happen}
//!   if ((n0<n1)and(trace_y>trace_yy))or((n0>n1)and(trace_y<trace_yy)) then
//!     trace_a_corner;
//!   end;
//! trace_yy:=n1;
//! end;
//!
//! @ One way to put new edge weights into an edge structure is to use the
//! following routine, which simply draws a straight line from |(x0,y0)| to
//! |(x1,y1)|. More precisely, it introduces weights for the edges of the
//! discrete path $\bigl(\lfloor t[x_0,x_1]+{1\over2}+\epsilon\rfloor,
//! \lfloor t[y_0,y_1]+{1\over2}+\epsilon\delta\rfloor\bigr)$,
//! as $t$ varies from 0 to~1, where $\epsilon$ and $\delta$ are extremely small
//! positive numbers.
//!
//! The structure header is assumed to be |cur_edges|; downward edge weights
//! will be |cur_wt|, while upward ones will be |-cur_wt|.
//!
//! Of course, this subroutine will be called only in connection with others
//! that eventually draw a complete cycle, so that the sum of the edge weights
//! in each row will be zero whenever the row is displayed.
//!
//! @p procedure line_edges(@!x0,@!y0,@!x1,@!y1:scaled);
//! label done,done1;
//! var @!m0,@!n0,@!m1,@!n1:integer; {rounded and unscaled coordinates}
//! @!delx,@!dely:scaled; {the coordinate differences of the line}
//! @!yt:scaled; {smallest |y| coordinate that rounds the same as |y0|}
//! @!tx:scaled; {tentative change in |x|}
//! @!p,@!r:pointer; {list manipulation registers}
//! @!base:integer; {amount added to edge-and-weight data}
//! @!n:integer; {current row number}
//! begin n0:=round_unscaled(y0);
//! n1:=round_unscaled(y1);
//! if n0<>n1 then
//!   begin m0:=round_unscaled(x0); m1:=round_unscaled(x1);
//!   delx:=x1-x0; dely:=y1-y0;
//!   yt:=n0*unity-half_unit; y0:=y0-yt; y1:=y1-yt;
//!   if n0<n1 then @<Insert upward edges for a line@>
//!   else @<Insert downward edges for a line@>;
//!   n_rover(cur_edges):=p; n_pos(cur_edges):=n+zero_field;
//!   end;
//! end;
//!
//! @ Here we are careful to cancel any effect of rounding error.
//!
//! @<Insert upward edges for a line@>=
//! begin base:=8*m_offset(cur_edges)+min_halfword+zero_w-cur_wt;
//! if m0<=m1 then edge_prep(m0,m1,n0,n1)@+else edge_prep(m1,m0,n0,n1);
//! @<Move to row |n0|, pointed to by |p|@>;
//! y0:=unity-y0;
//! loop@+  begin r:=get_avail; link(r):=unsorted(p); unsorted(p):=r;@/
//!   tx:=take_fraction(delx,make_fraction(y0,dely));
//!   if ab_vs_cd(delx,y0,dely,tx)<0 then decr(tx);
//!     {now $|tx|=\lfloor|y0|\cdot|delx|/|dely|\rfloor$}
//!   info(r):=8*round_unscaled(x0+tx)+base;@/
//!   y1:=y1-unity;
//!   if internal[tracing_edges]>0 then trace_new_edge(r,n);
//!   if y1<unity then goto done;
//!   p:=link(p); y0:=y0+unity; incr(n);
//!   end;
//! done: end
//!
//! @ @<Insert downward edges for a line@>=
//! begin base:=8*m_offset(cur_edges)+min_halfword+zero_w+cur_wt;
//! if m0<=m1 then edge_prep(m0,m1,n1,n0)@+else edge_prep(m1,m0,n1,n0);
//! decr(n0); @<Move to row |n0|, pointed to by |p|@>;
//! loop@+  begin r:=get_avail; link(r):=unsorted(p); unsorted(p):=r;@/
//!   tx:=take_fraction(delx,make_fraction(y0,dely));
//!   if ab_vs_cd(delx,y0,dely,tx)<0 then incr(tx);
//!     {now $|tx|=\lceil|y0|\cdot|delx|/|dely|\rceil$, since |dely<0|}
//!   info(r):=8*round_unscaled(x0-tx)+base;@/
//!   y1:=y1+unity;
//!   if internal[tracing_edges]>0 then trace_new_edge(r,n);
//!   if y1>=0 then goto done1;
//!   p:=knil(p); y0:=y0+unity; decr(n);
//!   end;
//! done1: end
//!
//! @ @<Move to row |n0|, pointed to by |p|@>=
//! n:=n_pos(cur_edges)-zero_field; p:=n_rover(cur_edges);
//! if n<>n0 then
//!   if n<n0 then
//!     repeat incr(n); p:=link(p);
//!     until n=n0
//!   else  repeat decr(n); p:=knil(p);
//!     until n=n0
//!
//! @ \MF\ inserts most of its edges into edge structures via the
//! |move_to_edges| subroutine, which uses the data stored in the |move| array
//! to specify a sequence of ``rook moves.'' The starting point |(m0,n0)|
//! and finishing point |(m1,n1)| of these moves, as seen from the standpoint
//! of the first octant, are supplied as parameters; the moves should, however,
//! be rotated into a given octant.  (We're going to study octant
//! transformations in great detail later; the reader may wish to come back to
//! this part of the program after mastering the mysteries of octants.)
//!
//! The rook moves themselves are defined as follows, from a |first_octant|
//! point of view: ``Go right |move[k]| steps, then go up one, for |0<=k<n1-n0|;
//! then go right |move[n1-n0]| steps and stop.'' The sum of |move[k]|
//! for |0<=k<=n1-n0| will be equal to |m1-m0|.
//!
//! As in the |line_edges| routine, we use |+cur_wt| as the weight of
//! all downward edges and |-cur_wt| as the weight of all upward edges,
//! after the moves have been rotated to the proper octant direction.
//!
//! There are two main cases to consider: \\{fast\_case} is for moves that
//! travel in the direction of octants 1, 4, 5, and~8, while \\{slow\_case}
//! is for moves that travel toward octants 2, 3, 6, and~7. The latter directions
//! are comparatively cumbersome because they generate more upward or downward
//! edges; a curve that travels horizontally doesn't produce any edges at all,
//! but a curve that travels vertically touches lots of rows.
//!
//! @d fast_case_up=60 {for octants 1 and 4}
//! @d fast_case_down=61 {for octants 5 and 8}
//! @d slow_case_up=62 {for octants 2 and 3}
//! @d slow_case_down=63 {for octants 6 and 7}
//!
//! @p procedure move_to_edges(@!m0,@!n0,@!m1,@!n1:integer);
//! label fast_case_up,fast_case_down,slow_case_up,slow_case_down,done;
//! var @!delta:0..move_size; {extent of |move| data}
//! @!k:0..move_size; {index into |move|}
//! @!p,@!r:pointer; {list manipulation registers}
//! @!dx:integer; {change in edge-weight |info| when |x| changes by 1}
//! @!edge_and_weight:integer; {|info| to insert}
//! @!j:integer; {number of consecutive vertical moves}
//! @!n:integer; {the current row pointed to by |p|}
//! debug @!sum:integer;@+gubed@;@/
//! begin delta:=n1-n0;
//! debug sum:=move[0]; for k:=1 to delta do sum:=sum+abs(move[k]);
//! if sum<>m1-m0 then confusion("0");@+gubed@;@/
//! @:this can't happen 0}{\quad 0@>
//! @<Prepare for and switch to the appropriate case, based on |octant|@>;
//! fast_case_up:@<Add edges for first or fourth octants, then |goto done|@>;
//! fast_case_down:@<Add edges for fifth or eighth octants, then |goto done|@>;
//! slow_case_up:@<Add edges for second or third octants, then |goto done|@>;
//! slow_case_down:@<Add edges for sixth or seventh octants, then |goto done|@>;
//! done: n_pos(cur_edges):=n+zero_field; n_rover(cur_edges):=p;
//! end;
//!
//! @ The current octant code appears in a global variable. If, for example,
//! we have |octant=third_octant|, it means that a curve traveling in a north to
//! north-westerly direction has been rotated for the purposes of internal
//! calculations so that the |move| data travels in an east to north-easterly
//! direction. We want to unrotate as we update the edge structure.
//!
//! @<Glob...@>=
//! @!octant:first_octant..sixth_octant; {the current octant of interest}
//!
//! @ @<Prepare for and switch to the appropriate case, based on |octant|@>=
//! case octant of
//! first_octant:begin dx:=8; edge_prep(m0,m1,n0,n1); goto fast_case_up;
//!   end;
//! second_octant:begin dx:=8; edge_prep(n0,n1,m0,m1); goto slow_case_up;
//!   end;
//! third_octant:begin dx:=-8; edge_prep(-n1,-n0,m0,m1); negate(n0);
//!   goto slow_case_up;
//!   end;
//! fourth_octant:begin dx:=-8; edge_prep(-m1,-m0,n0,n1); negate(m0);
//!   goto fast_case_up;
//!   end;
//! fifth_octant:begin dx:=-8; edge_prep(-m1,-m0,-n1,-n0); negate(m0);
//!   goto fast_case_down;
//!   end;
//! sixth_octant:begin dx:=-8; edge_prep(-n1,-n0,-m1,-m0); negate(n0);
//!   goto slow_case_down;
//!   end;
//! seventh_octant:begin dx:=8; edge_prep(n0,n1,-m1,-m0); goto slow_case_down;
//!   end;
//! eighth_octant:begin dx:=8; edge_prep(m0,m1,-n1,-n0); goto fast_case_down;
//!   end;
//! end; {there are only eight octants}
//!
//! @ @<Add edges for first or fourth octants, then |goto done|@>=
//! @<Move to row |n0|, pointed to by |p|@>;
//! if delta>0 then
//!   begin k:=0;
//!   edge_and_weight:=8*(m0+m_offset(cur_edges))+min_halfword+zero_w-cur_wt;
//!   repeat edge_and_weight:=edge_and_weight+dx*move[k];
//!   fast_get_avail(r); link(r):=unsorted(p); info(r):=edge_and_weight;
//!   if internal[tracing_edges]>0 then trace_new_edge(r,n);
//!   unsorted(p):=r; p:=link(p); incr(k); incr(n);
//!   until k=delta;
//!   end;
//! goto done
//!
//! @ @<Add edges for fifth or eighth octants, then |goto done|@>=
//! n0:=-n0-1; @<Move to row |n0|, pointed to by |p|@>;
//! if delta>0 then
//!   begin k:=0;
//!   edge_and_weight:=8*(m0+m_offset(cur_edges))+min_halfword+zero_w+cur_wt;
//!   repeat edge_and_weight:=edge_and_weight+dx*move[k];
//!   fast_get_avail(r); link(r):=unsorted(p); info(r):=edge_and_weight;
//!   if internal[tracing_edges]>0 then trace_new_edge(r,n);
//!   unsorted(p):=r; p:=knil(p); incr(k); decr(n);
//!   until k=delta;
//!   end;
//! goto done
//!
//! @ @<Add edges for second or third octants, then |goto done|@>=
//! edge_and_weight:=8*(n0+m_offset(cur_edges))+min_halfword+zero_w-cur_wt;
//! n0:=m0; k:=0; @<Move to row |n0|, pointed to by |p|@>;
//! repeat j:=move[k];
//! while j>0 do
//!   begin fast_get_avail(r); link(r):=unsorted(p); info(r):=edge_and_weight;
//!   if internal[tracing_edges]>0 then trace_new_edge(r,n);
//!   unsorted(p):=r; p:=link(p); decr(j); incr(n);
//!   end;
//! edge_and_weight:=edge_and_weight+dx; incr(k);
//! until k>delta;
//! goto done
//!
//! @ @<Add edges for sixth or seventh octants, then |goto done|@>=
//! edge_and_weight:=8*(n0+m_offset(cur_edges))+min_halfword+zero_w+cur_wt;
//! n0:=-m0-1; k:=0; @<Move to row |n0|, pointed to by |p|@>;
//! repeat j:=move[k];
//! while j>0 do
//!   begin fast_get_avail(r); link(r):=unsorted(p); info(r):=edge_and_weight;
//!   if internal[tracing_edges]>0 then trace_new_edge(r,n);
//!   unsorted(p):=r; p:=knil(p); decr(j); decr(n);
//!   end;
//! edge_and_weight:=edge_and_weight+dx; incr(k);
//! until k>delta;
//! goto done
//!
//! @ All the hard work of building an edge structure is undone by the following
//! subroutine.
//!
//! @<Declare the recycling subroutines@>=
//! procedure toss_edges(@!h:pointer);
//! var @!p,@!q:pointer; {for list manipulation}
//! begin q:=link(h);
//! while q<>h do
//!   begin flush_list(sorted(q));
//!   if unsorted(q)>void then flush_list(unsorted(q));
//!   p:=q; q:=link(q); free_node(p,row_node_size);
//!   end;
//! free_node(h,edge_header_size);
//! end;
//!
//! @* \[21] Subdivision into octants.
//! When \MF\ digitizes a path, it reduces the problem to the special
//! case of paths that travel in ``first octant'' directions; i.e.,
//! each cubic $z(t)=\bigl(x(t),y(t)\bigr)$ being digitized will have the property
//! that $0\L y'(t)\L x'(t)$. This assumption makes digitizing simpler
//! and faster than if the direction of motion has to be tested repeatedly.
//!
//! When $z(t)$ is cubic, $x'(t)$ and $y'(t)$ are quadratic, hence the four
//! polynomials $x'(t)$, $y'(t)$, $x'(t)-y'(t)$, and $x'(t)+y'(t)$ cross
//! through~0 at most twice each. If we subdivide the given cubic at these
//! places, we get at most nine subintervals in each of which
//! $x'(t)$, $y'(t)$, $x'(t)-y'(t)$, and $x'(t)+y'(t)$ all have a constant
//! sign. The curve can be transformed in each of these subintervals so that
//! it travels entirely in first octant directions, if we reflect $x\swap-x$,
//! $y\swap-y$, and/or $x\swap y$ as necessary. (Incidentally, it can be
//! shown that a cubic such that $x'(t)=16(2t-1)^2+2(2t-1)-1$ and
//! $y'(t)=8(2t-1)^2+4(2t-1)$ does indeed split into nine subintervals.)
//!
//! @ The transformation that rotates coordinates, so that first octant motion
//! can be assumed, is defined by the |skew| subroutine, which sets global
//! variables |cur_x| and |cur_y| to the values that are appropriate in a
//! given octant.  (Octants are encoded as they were in the |n_arg| subroutine.)
//!
//! This transformation is ``skewed'' by replacing |(x,y)| by |(x-y,y)|,
//! once first octant motion has been established. It turns out that
//! skewed coordinates are somewhat better to work with when curves are
//! actually digitized.
//!
//! @d set_two_end(#)==cur_y:=#;@+end
//! @d set_two(#)==begin cur_x:=#; set_two_end
//!
//! @p procedure skew(@!x,@!y:scaled;@!octant:small_number);
//! begin case octant of
//! first_octant: set_two(x-y)(y);
//! second_octant: set_two(y-x)(x);
//! third_octant: set_two(y+x)(-x);
//! fourth_octant: set_two(-x-y)(y);
//! fifth_octant: set_two(-x+y)(-y);
//! sixth_octant: set_two(-y+x)(-x);
//! seventh_octant: set_two(-y-x)(x);
//! eighth_octant: set_two(x+y)(-y);
//! end; {there are no other cases}
//! end;
//!
//! @ Conversely, the following subroutine sets |cur_x| and
//! |cur_y| to the original coordinate values of a point, given an octant
//! code and the point's coordinates |(x,y)| after they have been mapped into
//! the first octant and skewed.
//!
//! @<Declare subroutines for printing expressions@>=
//! procedure unskew(@!x,@!y:scaled;@!octant:small_number);
//! begin case octant of
//! first_octant: set_two(x+y)(y);
//! second_octant: set_two(y)(x+y);
//! third_octant: set_two(-y)(x+y);
//! fourth_octant: set_two(-x-y)(y);
//! fifth_octant: set_two(-x-y)(-y);
//! sixth_octant: set_two(-y)(-x-y);
//! seventh_octant: set_two(y)(-x-y);
//! eighth_octant: set_two(x+y)(-y);
//! end; {there are no other cases}
//! end;
//!
//! @ @<Glob...@>=
//! @!cur_x,@!cur_y:scaled;
//!   {outputs of |skew|, |unskew|, and a few other routines}
//!
//! @ The conversion to skewed and rotated coordinates takes place in
//! stages, and at one point in the transformation we will have negated the
//! $x$ and/or $y$ coordinates so as to make curves travel in the first
//! {\sl quadrant}. At this point the relevant ``octant'' code will be
//! either |first_octant| (when no transformation has been done),
//! or |fourth_octant=first_octant+negate_x| (when $x$ has been negated),
//! or |fifth_octant=first_octant+negate_x+negate_y| (when both have been
//! negated), or |eighth_octant=first_octant+negate_y| (when $y$ has been
//! negated). The |abnegate| routine is sometimes needed to convert
//! from one of these transformations to another.
//!
//! @p procedure abnegate(@!x,@!y:scaled;
//!   @!octant_before,@!octant_after:small_number);
//! begin if odd(octant_before)=odd(octant_after) then cur_x:=x
//!   else cur_x:=-x;
//! if (octant_before>negate_y)=(octant_after>negate_y) then cur_y:=y
//!   else cur_y:=-y;
//! end;
//!
//! @ Now here's a subroutine that's handy for subdivision: Given a
//! quadratic polynomial $B(a,b,c;t)$, the |crossing_point| function
//! returns the unique |fraction| value |t| between 0 and~1 at which
//! $B(a,b,c;t)$ changes from positive to negative, or returns
//! |t=fraction_one+1| if no such value exists. If |a<0| (so that $B(a,b,c;t)$
//! is already negative at |t=0|), |crossing_point| returns the value zero.
//!
//! @d no_crossing==begin crossing_point:=fraction_one+1; return;
//!   end
//! @d one_crossing==begin crossing_point:=fraction_one; return;
//!   end
//! @d zero_crossing==begin crossing_point:=0; return;
//!   end
//!
//! @p function crossing_point(@!a,@!b,@!c:integer):fraction;
//! label exit;
//! var @!d:integer; {recursive counter}
//! @!x,@!xx,@!x0,@!x1,@!x2:integer; {temporary registers for bisection}
//! begin if a<0 then zero_crossing;
//! if c>=0 then
//!   begin if b>=0 then
//!     if c>0 then no_crossing
//!     else if (a=0)and(b=0) then no_crossing
//!     else one_crossing;
//!   if a=0 then zero_crossing;
//!   end
//! else if a=0 then if b<=0 then zero_crossing;
//! @<Use bisection to find the crossing point, if one exists@>;
//! exit:end;
//!
//! @ The general bisection method is quite simple when $n=2$, hence
//! |crossing_point| does not take much time. At each stage in the
//! recursion we have a subinterval defined by |l| and~|j| such that
//! $B(a,b,c;2^{-l}(j+t))=B(x_0,x_1,x_2;t)$, and we want to ``zero in'' on
//! the subinterval where $x_0\G0$ and $\min(x_1,x_2)<0$.
//!
//! It is convenient for purposes of calculation to combine the values
//! of |l| and~|j| in a single variable $d=2^l+j$, because the operation
//! of bisection then corresponds simply to doubling $d$ and possibly
//! adding~1. Furthermore it proves to be convenient to modify
//! our previous conventions for bisection slightly, maintaining the
//! variables $X_0=2^lx_0$, $X_1=2^l(x_0-x_1)$, and $X_2=2^l(x_1-x_2)$.
//! With these variables the conditions $x_0\ge0$ and $\min(x_1,x_2)<0$ are
//! equivalent to $\max(X_1,X_1+X_2)>X_0\ge0$.
//!
//! The following code maintains the invariant relations
//! $0\L|x0|<\max(|x1|,|x1|+|x2|)$,
//! $\vert|x1|\vert<2^{30}$, $\vert|x2|\vert<2^{30}$;
//! it has been constructed in such a way that no arithmetic overflow
//! will occur if the inputs satisfy
//! $a<2^{30}$, $\vert a-b\vert<2^{30}$, and $\vert b-c\vert<2^{30}$.
//!
//! @<Use bisection to find the crossing point...@>=
//! d:=1; x0:=a; x1:=a-b; x2:=b-c;
//! repeat x:=half(x1+x2);
//! if x1-x0>x0 then
//!   begin x2:=x; double(x0); double(d);
//!   end
//! else  begin xx:=x1+x-x0;
//!   if xx>x0 then
//!     begin x2:=x; double(x0); double(d);
//!     end
//!   else  begin x0:=x0-xx;
//!     if x<=x0 then if x+x2<=x0 then no_crossing;
//!     x1:=x; d:=d+d+1;
//!     end;
//!   end;
//! until d>=fraction_one;
//! crossing_point:=d-fraction_one
//!
//! @ Octant subdivision is applied only to cycles, i.e., to closed paths.
//! A ``cycle spec'' is a data structure that contains specifications of
//! @!@^cycle spec@>
//! cubic curves and octant mappings for the cycle that has been subdivided
//! into segments belonging to single octants. It is composed entirely of
//! knot nodes, similar to those in the representation of paths; but the
//! |explicit| type indications have been replaced by positive numbers
//! that give further information. Additional |endpoint| data is also
//! inserted at the octant boundaries.
//!
//! Recall that a cubic polynomial is represented by four control points
//! that appear in adjacent nodes |p| and~|q| of a knot list. The |x|~coordinates
//! are |x_coord(p)|, |right_x(p)|, |left_x(q)|, and |x_coord(q)|; the
//! |y|~coordinates are similar. We shall call this ``the cubic following~|p|''
//! or ``the cubic between |p| and~|q|'' or ``the cubic preceding~|q|.''
//!
//! Cycle specs are circular lists of cubic curves mixed with octant
//! boundaries. Like cubics, the octant boundaries are represented in
//! consecutive knot nodes |p| and~|q|. In such cases |right_type(p)=
//! left_type(q)=endpoint|, and the fields |right_x(p)|, |right_y(p)|,
//! |left_x(q)|, and |left_y(q)| are replaced by other fields called
//! |right_octant(p)|, |right_transition(p)|, |left_octant(q)|, and
//! |left_transition(q)|, respectively. For example, when the curve direction
//! moves from the third octant to the fourth octant, the boundary nodes say
//! |right_octant(p)=third_octant|, |left_octant(q)=fourth_octant|,
//! and |right_transition(p)=left_transition(q)=diagonal|. A |diagonal|
//! transition occurs when moving between octants 1~\AM~2, 3~\AM~4, 5~\AM~6, or
//! 7~\AM~8; an |axis| transition occurs when moving between octants 8~\AM~1,
//! 2~\AM~3, 4~\AM~5, 6~\AM~7. (Such transition information is redundant
//! but convenient.) Fields |x_coord(p)| and |y_coord(p)| will contain
//! coordinates of the transition point after rotation from third octant
//! to first octant; i.e., if the true coordinates are $(x,y)$, the
//! coordinates $(y,-x)$ will appear in node~|p|. Similarly, a fourth-octant
//! transformation will have been applied after the transition, so
//! we will have |x_coord(q)=@t$-x$@>| and |y_coord(q)=y|.
//!
//! The cubic between |p| and |q| will contain positive numbers in the
//! fields |right_type(p)| and |left_type(q)|; this makes cubics
//! distinguishable from octant boundaries, because |endpoint=0|.
//! The value of |right_type(p)| will be the current octant code,
//! during the time that cycle specs are being constructed; it will
//! refer later to a pen offset position, if the envelope of a cycle is
//! being computed. A cubic that comes from some subinterval of the $k$th
//! step in the original cyclic path will have |left_type(q)=k|.
//!
//! @d right_octant==right_x {the octant code before a transition}
//! @d left_octant==left_x {the octant after a transition}
//! @d right_transition==right_y {the type of transition}
//! @d left_transition==left_y {ditto, either |axis| or |diagonal|}
//! @d axis=0 {a transition across the $x'$- or $y'$-axis}
//! @d diagonal=1 {a transition where $y'=\pm x'$}
//!
//! @ Here's a routine that prints a cycle spec in symbolic form, so that it
//! is possible to see what subdivision has been made.  The point coordinates
//! are converted back from \MF's internal ``rotated'' form to the external
//! ``true'' form. The global variable~|cur_spec| should point to a knot just
//! after the beginning of an octant boundary, i.e., such that
//! |left_type(cur_spec)=endpoint|.
//!
//! @d print_two_true(#)==unskew(#,octant); print_two(cur_x,cur_y)
//!
//! @p procedure print_spec(@!s:str_number);
//! label not_found,done;
//! var @!p,@!q:pointer; {for list traversal}
//! @!octant:small_number; {the current octant code}
//! begin print_diagnostic("Cycle spec",s,true);
//! @.Cycle spec at line...@>
//! p:=cur_spec; octant:=left_octant(p); print_ln;
//! print_two_true(x_coord(cur_spec),y_coord(cur_spec));
//! print(" % beginning in octant `");
//! loop@+  begin print(octant_dir[octant]); print_char("'");
//!   loop@+  begin q:=link(p);
//!     if right_type(p)=endpoint then goto not_found;
//!     @<Print the cubic between |p| and |q|@>;
//!     p:=q;
//!     end;
//! not_found: if q=cur_spec then goto done;
//!   p:=q; octant:=left_octant(p); print_nl("% entering octant `");
//!   end;
//! @.entering the nth octant@>
//! done: print_nl(" & cycle"); end_diagnostic(true);
//! end;
//!
//! @ Symbolic octant direction names are kept in the |octant_dir| array.
//!
//! @<Glob...@>=
//! @!octant_dir:array[first_octant..sixth_octant] of str_number;
//!
//! @ @<Set init...@>=
//! octant_dir[first_octant]:="ENE";
//! octant_dir[second_octant]:="NNE";
//! octant_dir[third_octant]:="NNW";
//! octant_dir[fourth_octant]:="WNW";
//! octant_dir[fifth_octant]:="WSW";
//! octant_dir[sixth_octant]:="SSW";
//! octant_dir[seventh_octant]:="SSE";
//! octant_dir[eighth_octant]:="ESE";
//!
//! @ @<Print the cubic between...@>=
//! begin print_nl("   ..controls ");
//! print_two_true(right_x(p),right_y(p));
//! print(" and ");
//! print_two_true(left_x(q),left_y(q));
//! print_nl(" ..");
//! print_two_true(x_coord(q),y_coord(q));
//! print(" % segment "); print_int(left_type(q)-1);
//! end
//!
//! @ A much more compact version of a spec is printed to help users identify
//! ``strange paths.''
//!
//! @p procedure print_strange(@!s:str_number);
//! var @!p:pointer; {for list traversal}
//! @!f:pointer; {starting point in the cycle}
//! @!q:pointer; {octant boundary to be printed}
//! @!t:integer; {segment number, plus 1}
//! begin if interaction=error_stop_mode then wake_up_terminal;
//! print_nl(">");
//! @.>\relax@>
//! @<Find the starting point, |f|@>;
//! @<Determine the octant boundary |q| that precedes |f|@>;
//! t:=0;
//! repeat if left_type(p)<>endpoint then
//!   begin if left_type(p)<>t then
//!     begin t:=left_type(p); print_char(" "); print_int(t-1);
//!     end;
//!   if q<>null then
//!     begin @<Print the turns, if any, that start at |q|, and advance |q|@>;
//!     print_char(" "); print(octant_dir[left_octant(q)]); q:=null;
//!     end;
//!   end
//! else if q=null then q:=p;
//! p:=link(p);
//! until p=f;
//! print_char(" "); print_int(left_type(p)-1);
//! if q<>null then @<Print the turns...@>;
//! print_err(s);
//! end;
//!
//! @ If the segment numbers on the cycle are $t_1$, $t_2$, \dots, $t_m$,
//! and if |m<=max_quarterword|,
//! we have $t_{k-1}\L t_k$ except for at most one value of~$k$. If there are
//! no exceptions, $f$ will point to $t_1$; otherwise it will point to the
//! exceptional~$t_k$.
//!
//! There is at least one segment number (i.e., we always have $m>0$), because
//! |print_strange| is never called upon to display an entirely ``dead'' cycle.
//!
//! @<Find the starting point, |f|@>=
//! p:=cur_spec; t:=max_quarterword+1;
//! repeat p:=link(p);
//! if left_type(p)<>endpoint then
//!   begin if left_type(p)<t then f:=p;
//!   t:=left_type(p);
//!   end;
//! until p=cur_spec
//!
//! @ @<Determine the octant boundary...@>=
//! p:=cur_spec; q:=p;
//! repeat p:=link(p);
//! if left_type(p)=endpoint then q:=p;
//! until p=f
//!
//! @ When two octant boundaries are adjacent, the path is simply changing direction
//! without moving. Such octant directions are shown in parentheses.
//!
//! @<Print the turns...@>=
//! if left_type(link(q))=endpoint then
//!   begin print(" ("); print(octant_dir[left_octant(q)]); q:=link(q);
//!   while left_type(link(q))=endpoint do
//!     begin print_char(" "); print(octant_dir[left_octant(q)]); q:=link(q);
//!     end;
//!   print_char(")");
//!   end
//!
//! @ The |make_spec| routine is what subdivides paths into octants:
//! Given a pointer |cur_spec| to a cyclic path, |make_spec| mungs the path data
//! and returns a pointer to the corresponding cyclic spec.
//! All ``dead'' cubics (i.e., cubics that don't move at all from
//! their starting points) will have been removed from the result.
//! @!@^dead cubics@>
//!
//! The idea of |make_spec| is fairly simple: Each cubic is first
//! subdivided, if necessary, into pieces belonging to single octants;
//! then the octant boundaries are inserted. But some of the details of
//! this transformation are not quite obvious.
//!
//! If |autorounding>0|, the path will be adjusted so that critical tangent
//! directions occur at ``good'' points with respect to the pen called |cur_pen|.
//!
//! The resulting spec will have all |x| and |y| coordinates at most
//! $2^{28}-|half_unit|-1-|safety_margin|$ in absolute value.  The pointer
//! that is returned will start some octant, as required by |print_spec|.
//!
//! @p @t\4@>@<Declare subroutines needed by |make_spec|@>@;
//! function make_spec(@!h:pointer;
//!   @!safety_margin:scaled;@!tracing:integer):pointer;
//!   {converts a path to a cycle spec}
//! label continue,done;
//! var @!p,@!q,@!r,@!s:pointer; {for traversing the lists}
//! @!k:integer; {serial number of path segment, or octant code}
//! @!chopped:integer; {positive if data truncated,
//!           negative if data dangerously large}
//! @<Other local variables for |make_spec|@>@;
//! begin cur_spec:=h;
//! if tracing>0 then
//!   print_path(cur_spec,", before subdivision into octants",true);
//! max_allowed:=fraction_one-half_unit-1-safety_margin;
//! @<Truncate the values of all coordinates that exceed |max_allowed|, and stamp
//!   segment numbers in each |left_type| field@>;
//! quadrant_subdivide; {subdivide each cubic into pieces belonging to quadrants}
//! if (internal[autorounding]>0)and(chopped=0) then xy_round;
//! octant_subdivide; {complete the subdivision}
//! if (internal[autorounding]>unity)and(chopped=0) then diag_round;
//! @<Remove dead cubics@>;
//! @<Insert octant boundaries and compute the turning number@>;
//! while left_type(cur_spec)<>endpoint do cur_spec:=link(cur_spec);
//! if tracing>0 then
//!   if (internal[autorounding]<=0)or(chopped<>0) then
//!     print_spec(", after subdivision")
//!   else if internal[autorounding]>unity then
//!     print_spec(", after subdivision and double autorounding")
//!   else print_spec(", after subdivision and autorounding");
//! make_spec:=cur_spec;
//! end;
//!
//! @ The |make_spec| routine has an interesting side effect, namely to set
//! the global variable |turning_number| to the number of times the tangent
//! vector of the given cyclic path winds around the origin.
//!
//! Another global variable |cur_spec| points to the specification as it is
//! being made, since several subroutines must go to work on it.
//!
//! And there are two global variables that affect the rounding
//! decisions, as we'll see later; they are called |cur_pen| and |cur_path_type|.
//! The latter will be |double_path_code| if |make_spec| is being
//! applied to a double path.
//!
//! @d double_path_code=0 {command modifier for `\&{doublepath}'}
//! @d contour_code=1 {command modifier for `\&{contour}'}
//! @d also_code=2 {command modifier for `\&{also}'}
//!
//! @<Glob...@>=
//! @!cur_spec:pointer; {the principal output of |make_spec|}
//! @!turning_number:integer; {another output of |make_spec|}
//! @!cur_pen:pointer; {an implicit input of |make_spec|, used in autorounding}
//! @!cur_path_type:double_path_code..contour_code; {likewise}
//! @!max_allowed:scaled; {coordinates must be at most this big}
//!
//! @ First we do a simple preprocessing step. The segment numbers inserted
//! here will propagate to all descendants of cubics that are split into
//! subintervals. These numbers must be nonzero, but otherwise they are
//! present merely for diagnostic purposes. The cubic from |p| to~|q|
//! that represents ``time interval'' |(t-1)..t| usually has |left_type(q)=t|,
//! except when |t| is too large to be stored in a quarterword.
//!
//! @d procrustes(#)==@+if abs(#)>=dmax then
//!   if abs(#)>max_allowed then
//!     begin chopped:=1;
//!     if #>0 then #:=max_allowed@+else #:=-max_allowed;
//!     end
//!   else if chopped=0 then chopped:=-1
//!
//! @<Truncate the values of all coordinates that exceed...@>=
//! p:=cur_spec; k:=1; chopped:=0; dmax:=half(max_allowed);
//! repeat procrustes(left_x(p)); procrustes(left_y(p));
//! procrustes(x_coord(p)); procrustes(y_coord(p));
//! procrustes(right_x(p)); procrustes(right_y(p));@/
//! p:=link(p); left_type(p):=k;
//! if k<max_quarterword then incr(k)@+else k:=1;
//! until p=cur_spec;
//! if chopped>0 then
//!   begin print_err("Curve out of range");
//! @.Curve out of range@>
//!   help4("At least one of the coordinates in the path I'm about to")@/
//!     ("digitize was really huge (potentially bigger than 4095).")@/
//!     ("So I've cut it back to the maximum size.")@/
//!     ("The results will probably be pretty wild.");
//!   put_get_error;
//!   end
//!
//! @ We may need to get rid of constant ``dead'' cubics that clutter up
//! the data structure and interfere with autorounding.
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! procedure remove_cubic(@!p:pointer); {removes the cubic following~|p|}
//! var @!q:pointer; {the node that disappears}
//! begin q:=link(p); right_type(p):=right_type(q); link(p):=link(q);@/
//! x_coord(p):=x_coord(q); y_coord(p):=y_coord(q);@/
//! right_x(p):=right_x(q); right_y(p):=right_y(q);@/
//! free_node(q,knot_node_size);
//! end;
//!
//! @ The subdivision process proceeds by first swapping $x\swap-x$, if
//! necessary, to ensure that $x'\G0$; then swapping $y\swap-y$, if necessary,
//! to ensure that $y'\G0$; and finally swapping $x\swap y$, if necessary,
//! to ensure that $x'\G y'$.
//!
//! Recall that the octant codes have been defined in such a way that, for
//! example, |third_octant=first_octant+negate_x+switch_x_and_y|. The program
//! uses the fact that |negate_x<negate_y<switch_x_and_y| to handle ``double
//! negation'': If |c| is an octant code that possibly involves |negate_x|
//! and/or |negate_y|, but not |switch_x_and_y|, then negating~|y| changes~|c|
//! either to |c+negate_y| or |c-negate_y|, depending on whether
//! |c<=negate_y| or |c>negate_y|. Octant codes are always greater than zero.
//!
//! The first step is to subdivide on |x| and |y| only, so that horizontal
//! and vertical autorounding can be done before we compare $x'$ to $y'$.
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! @t\4@>@<Declare the procedure called |split_cubic|@>@;
//! procedure quadrant_subdivide;
//! label continue,exit;
//! var @!p,@!q,@!r,@!s,@!pp,@!qq:pointer; {for traversing the lists}
//! @!first_x,@!first_y:scaled; {unnegated coordinates of node |cur_spec|}
//! @!del1,@!del2,@!del3,@!del,@!dmax:scaled; {proportional to the control
//!   points of a quadratic derived from a cubic}
//! @!t:fraction; {where a quadratic crosses zero}
//! @!dest_x,@!dest_y:scaled; {final values of |x| and |y| in the current cubic}
//! @!constant_x:boolean; {is |x| constant between |p| and |q|?}
//! begin p:=cur_spec; first_x:=x_coord(cur_spec); first_y:=y_coord(cur_spec);
//! repeat continue: q:=link(p);
//! @<Subdivide the cubic between |p| and |q| so that the results travel
//!   toward the right halfplane@>;
//! @<Subdivide all cubics between |p| and |q| so that the results travel
//!   toward the first quadrant; but |return| or |goto continue| if the
//!   cubic from |p| to |q| was dead@>;
//! p:=q;
//! until p=cur_spec;
//! exit:end;
//!
//! @ All three subdivision processes are similar, so it's possible to
//! get the general idea by studying the first one (which is the simplest).
//! The calculation makes use of the fact that the derivatives of
//! Bernshte{\u\i}n polynomials satisfy
//! $B'(z_0,z_1,\ldots,z_n;t)=nB(z_1-z_0,\ldots,z_n-z_{n-1};t)$.
//!
//! When this routine begins, |right_type(p)| is |explicit|; we should
//! set |right_type(p):=first_octant|. However, no assignment is made,
//! because |explicit=first_octant|. The author apologizes for using
//! such trickery here; it is really hard to do redundant computations
//! just for the sake of purity.
//!
//! @<Subdivide the cubic between |p| and |q| so that the results travel
//!   toward the right halfplane...@>=
//! if q=cur_spec then
//!   begin dest_x:=first_x; dest_y:=first_y;
//!   end
//! else  begin dest_x:=x_coord(q); dest_y:=y_coord(q);
//!   end;
//! del1:=right_x(p)-x_coord(p); del2:=left_x(q)-right_x(p);
//! del3:=dest_x-left_x(q);
//! @<Scale up |del1|, |del2|, and |del3| for greater accuracy;
//!   also set |del| to the first nonzero element of |(del1,del2,del3)|@>;
//! if del=0 then constant_x:=true
//! else  begin constant_x:=false;
//!   if del<0 then @<Complement the |x| coordinates of the
//!     cubic between |p| and~|q|@>;
//!   t:=crossing_point(del1,del2,del3);
//!   if t<fraction_one then
//!     @<Subdivide the cubic with respect to $x'$, possibly twice@>;
//!   end
//!
//! @ If |del1=del2=del3=0|, it's impossible to obey the title of this
//! section. We just set |del=0| in that case.
//! @^inner loop@>
//!
//! @<Scale up |del1|, |del2|, and |del3| for greater accuracy...@>=
//! if del1<>0 then del:=del1
//! else if del2<>0 then del:=del2
//! else del:=del3;
//! if del<>0 then
//!   begin dmax:=abs(del1);
//!   if abs(del2)>dmax then dmax:=abs(del2);
//!   if abs(del3)>dmax then dmax:=abs(del3);
//!   while dmax<fraction_half do
//!     begin double(dmax); double(del1); double(del2); double(del3);
//!     end;
//!   end
//!
//! @ During the subdivision phases of |make_spec|, the |x_coord| and |y_coord|
//! fields of node~|q| are not transformed to agree with the octant
//! stated in |right_type(p)|; they remain consistent with |right_type(q)|.
//! But |left_x(q)| and |left_y(q)| are governed by |right_type(p)|.
//!
//! @<Complement the |x| coordinates...@>=
//! begin negate(x_coord(p)); negate(right_x(p));
//! negate(left_x(q));@/
//! negate(del1); negate(del2); negate(del3);@/
//! negate(dest_x);
//! right_type(p):=first_octant+negate_x;
//! end
//!
//! @ When a cubic is split at a |fraction| value |t|, we obtain two cubics
//! whose B\'ezier control points are obtained by a generalization of the
//! bisection process: The formula
//! `$z_k^{(j+1)}={1\over2}(z_k^{(j)}+z\k^{(j)})$' becomes
//! `$z_k^{(j+1)}=t[z_k^{(j)},z\k^{(j)}]$'.
//!
//! It is convenient to define a \.{WEB} macro |t_of_the_way| such that
//! |t_of_the_way(a)(b)| expands to |a-(a-b)*t|, i.e., to |t[a,b]|.
//!
//! If |0<=t<=1|, the quantity |t[a,b]| is always between |a| and~|b|, even in
//! the presence of rounding errors. Our subroutines
//! also obey the identity |t[a,b]+t[b,a]=a+b|.
//!
//! @d t_of_the_way_end(#)==#,t@=)@>
//! @d t_of_the_way(#)==#-take_fraction@=(@>#-t_of_the_way_end
//!
//! @<Declare the procedure called |split_cubic|@>=
//! procedure split_cubic(@!p:pointer;@!t:fraction;
//!   @!xq,@!yq:scaled); {splits the cubic after |p|}
//! var @!v:scaled; {an intermediate value}
//! @!q,@!r:pointer; {for list manipulation}
//! begin q:=link(p); r:=get_node(knot_node_size); link(p):=r; link(r):=q;@/
//! left_type(r):=left_type(q); right_type(r):=right_type(p);@#
//! v:=t_of_the_way(right_x(p))(left_x(q));
//! right_x(p):=t_of_the_way(x_coord(p))(right_x(p));
//! left_x(q):=t_of_the_way(left_x(q))(xq);
//! left_x(r):=t_of_the_way(right_x(p))(v);
//! right_x(r):=t_of_the_way(v)(left_x(q));
//! x_coord(r):=t_of_the_way(left_x(r))(right_x(r));@#
//! v:=t_of_the_way(right_y(p))(left_y(q));
//! right_y(p):=t_of_the_way(y_coord(p))(right_y(p));
//! left_y(q):=t_of_the_way(left_y(q))(yq);
//! left_y(r):=t_of_the_way(right_y(p))(v);
//! right_y(r):=t_of_the_way(v)(left_y(q));
//! y_coord(r):=t_of_the_way(left_y(r))(right_y(r));
//! end;
//!
//! @ Since $x'(t)$ is a quadratic equation, it can cross through zero
//! at~most twice. When it does cross zero, we make doubly sure that the
//! derivative is really zero at the splitting point, in case rounding errors
//! have caused the split cubic to have an apparently nonzero derivative.
//! We also make sure that the split cubic is monotonic.
//!
//! @<Subdivide the cubic with respect to $x'$, possibly twice@>=
//! begin split_cubic(p,t,dest_x,dest_y); r:=link(p);
//! if right_type(r)>negate_x then right_type(r):=first_octant
//! else right_type(r):=first_octant+negate_x;
//! if x_coord(r)<x_coord(p) then x_coord(r):=x_coord(p);
//! left_x(r):=x_coord(r);
//! if right_x(p)>x_coord(r) then right_x(p):=x_coord(r);
//!  {we always have |x_coord(p)<=right_x(p)|}
//! negate(x_coord(r)); right_x(r):=x_coord(r);
//! negate(left_x(q)); negate(dest_x);@/
//! del2:=t_of_the_way(del2)(del3);
//!   {now |0,del2,del3| represent $x'$ on the remaining interval}
//! if del2>0 then del2:=0;
//! t:=crossing_point(0,-del2,-del3);
//! if t<fraction_one then @<Subdivide the cubic a second time
//!   with respect to $x'$@>
//! else begin if x_coord(r)>dest_x then
//!     begin x_coord(r):=dest_x; left_x(r):=-x_coord(r); right_x(r):=x_coord(r);
//!     end;
//!   if left_x(q)>dest_x then left_x(q):=dest_x
//!   else if left_x(q)<x_coord(r) then left_x(q):=x_coord(r);
//!   end;
//! end
//!
//! @ @<Subdivide the cubic a second time with respect to $x'$@>=
//! begin split_cubic(r,t,dest_x,dest_y); s:=link(r);
//! if x_coord(s)<dest_x then x_coord(s):=dest_x;
//! if x_coord(s)<x_coord(r) then x_coord(s):=x_coord(r);
//! right_type(s):=right_type(p);
//! left_x(s):=x_coord(s); {now |x_coord(r)=right_x(r)<=left_x(s)|}
//! if left_x(q)<dest_x then left_x(q):=-dest_x
//! else if left_x(q)>x_coord(s) then left_x(q):=-x_coord(s)
//! else negate(left_x(q));
//! negate(x_coord(s)); right_x(s):=x_coord(s);
//! end
//!
//! @ The process of subdivision with respect to $y'$ is like that with respect
//! to~$x'$, with the slight additional complication that two or three cubics
//! might now appear between |p| and~|q|.
//!
//! @<Subdivide all cubics between |p| and |q| so that the results travel
//!   toward the first quadrant...@>=
//! pp:=p;
//! repeat qq:=link(pp);
//! abnegate(x_coord(qq),y_coord(qq),right_type(qq),right_type(pp));
//! dest_x:=cur_x; dest_y:=cur_y;@/
//! del1:=right_y(pp)-y_coord(pp); del2:=left_y(qq)-right_y(pp);
//! del3:=dest_y-left_y(qq);
//! @<Scale up |del1|, |del2|, and |del3| for greater accuracy;
//!   also set |del| to the first nonzero element of |(del1,del2,del3)|@>;
//! if del<>0 then {they weren't all zero}
//!   begin if del<0 then @<Complement the |y| coordinates of the
//!     cubic between |pp| and~|qq|@>;
//!   t:=crossing_point(del1,del2,del3);
//!   if t<fraction_one then
//!     @<Subdivide the cubic with respect to $y'$, possibly twice@>;
//!   end
//! else @<Do any special actions needed when |y| is constant;
//!   |return| or |goto continue| if a dead cubic from |p| to |q| is removed@>;
//! pp:=qq;
//! until pp=q;
//! if constant_x then @<Correct the octant code in segments with decreasing |y|@>
//!
//! @ @<Complement the |y| coordinates...@>=
//! begin negate(y_coord(pp)); negate(right_y(pp));
//! negate(left_y(qq));@/
//! negate(del1); negate(del2); negate(del3);@/
//! negate(dest_y);
//! right_type(pp):=right_type(pp)+negate_y;
//! end
//!
//! @ @<Subdivide the cubic with respect to $y'$, possibly twice@>=
//! begin split_cubic(pp,t,dest_x,dest_y); r:=link(pp);
//! if right_type(r)>negate_y then right_type(r):=right_type(r)-negate_y
//! else right_type(r):=right_type(r)+negate_y;
//! if y_coord(r)<y_coord(pp) then y_coord(r):=y_coord(pp);
//! left_y(r):=y_coord(r);
//! if right_y(pp)>y_coord(r) then right_y(pp):=y_coord(r);
//!  {we always have |y_coord(pp)<=right_y(pp)|}
//! negate(y_coord(r)); right_y(r):=y_coord(r);
//! negate(left_y(qq)); negate(dest_y);@/
//! if x_coord(r)<x_coord(pp) then x_coord(r):=x_coord(pp)
//! else if x_coord(r)>dest_x then x_coord(r):=dest_x;
//! if left_x(r)>x_coord(r) then
//!   begin left_x(r):=x_coord(r);
//!   if right_x(pp)>x_coord(r) then right_x(pp):=x_coord(r);
//!   end;
//! if right_x(r)<x_coord(r) then
//!   begin right_x(r):=x_coord(r);
//!   if left_x(qq)<x_coord(r) then left_x(qq):=x_coord(r);
//!   end;
//! del2:=t_of_the_way(del2)(del3);
//!   {now |0,del2,del3| represent $y'$ on the remaining interval}
//! if del2>0 then del2:=0;
//! t:=crossing_point(0,-del2,-del3);
//! if t<fraction_one then @<Subdivide the cubic a second time
//!   with respect to $y'$@>
//! else begin if y_coord(r)>dest_y then
//!     begin y_coord(r):=dest_y; left_y(r):=-y_coord(r); right_y(r):=y_coord(r);
//!     end;
//!   if left_y(qq)>dest_y then left_y(qq):=dest_y
//!   else if left_y(qq)<y_coord(r) then left_y(qq):=y_coord(r);
//!   end;
//! end
//!
//! @ @<Subdivide the cubic a second time with respect to $y'$@>=
//! begin split_cubic(r,t,dest_x,dest_y); s:=link(r);@/
//! if y_coord(s)<dest_y then y_coord(s):=dest_y;
//! if y_coord(s)<y_coord(r) then y_coord(s):=y_coord(r);
//! right_type(s):=right_type(pp);
//! left_y(s):=y_coord(s); {now |y_coord(r)=right_y(r)<=left_y(s)|}
//! if left_y(qq)<dest_y then left_y(qq):=-dest_y
//! else if left_y(qq)>y_coord(s) then left_y(qq):=-y_coord(s)
//! else negate(left_y(qq));
//! negate(y_coord(s)); right_y(s):=y_coord(s);
//! if x_coord(s)<x_coord(r) then x_coord(s):=x_coord(r)
//! else if x_coord(s)>dest_x then x_coord(s):=dest_x;
//! if left_x(s)>x_coord(s) then
//!   begin left_x(s):=x_coord(s);
//!   if right_x(r)>x_coord(s) then right_x(r):=x_coord(s);
//!   end;
//! if right_x(s)<x_coord(s) then
//!   begin right_x(s):=x_coord(s);
//!   if left_x(qq)<x_coord(s) then left_x(qq):=x_coord(s);
//!   end;
//! end
//!
//! @ If the cubic is constant in $y$ and increasing in $x$, we have classified
//! it as traveling in the first octant. If the cubic is constant
//! in~$y$ and decreasing in~$x$, it is desirable to classify it as traveling
//! in the fifth octant (not the fourth), because autorounding will be consistent
//! with respect to doublepaths only if the octant number changes by four when
//! the path is reversed. Therefore we negate the $y$~coordinates
//! when they are constant but the curve is decreasing in~$x$; this gives
//! the desired result except in pathological paths.
//!
//! If the cubic is ``dead,'' i.e., constant in both |x| and |y|, we remove
//! it unless it is the only cubic in the entire path. We |goto continue|
//! if it wasn't the final cubic, so that the test |p=cur_spec| does not
//! falsely imply that all cubics have been processed.
//!
//! @<Do any special actions needed when |y| is constant...@>=
//! if constant_x then {|p=pp|, |q=qq|, and the cubic is dead}
//!   begin if q<>p then
//!     begin remove_cubic(p); {remove the dead cycle and recycle node |q|}
//!     if cur_spec<>q then goto continue
//!     else  begin cur_spec:=p; return;
//!       end; {the final cubic was dead and is gone}
//!     end;
//!   end
//! else if not odd(right_type(pp)) then {the $x$ coordinates were negated}
//!   @<Complement the |y| coordinates...@>
//!
//! @ A similar correction to octant codes deserves to be made when |x| is
//! constant and |y| is decreasing.
//!
//! @<Correct the octant code in segments with decreasing |y|@>=
//! begin pp:=p;
//! repeat qq:=link(pp);
//! if right_type(pp)>negate_y then {the $y$ coordinates were negated}
//!   begin right_type(pp):=right_type(pp)+negate_x;
//!   negate(x_coord(pp)); negate(right_x(pp)); negate(left_x(qq));
//!   end;
//! pp:=qq;
//! until pp=q;
//! end
//!
//! @ Finally, the process of subdividing to make $x'\G y'$ is like the other
//! two subdivisions, with a few new twists. We skew the coordinates at this time.
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! procedure octant_subdivide;
//! var @!p,@!q,@!r,@!s:pointer; {for traversing the lists}
//! @!del1,@!del2,@!del3,@!del,@!dmax:scaled; {proportional to the control
//!   points of a quadratic derived from a cubic}
//! @!t:fraction; {where a quadratic crosses zero}
//! @!dest_x,@!dest_y:scaled; {final values of |x| and |y| in the current cubic}
//! begin p:=cur_spec;
//! repeat q:=link(p);@/
//! x_coord(p):=x_coord(p)-y_coord(p);
//! right_x(p):=right_x(p)-right_y(p);
//! left_x(q):=left_x(q)-left_y(q);@/
//! @<Subdivide the cubic between |p| and |q| so that the results travel
//!   toward the first octant@>;
//! p:=q;
//! until p=cur_spec;
//! end;
//!
//! @ @<Subdivide the cubic between |p| and |q| so that the results travel
//!   toward the first octant@>=
//! @<Set up the variables |(del1,del2,del3)| to represent $x'-y'$@>;
//! @<Scale up |del1|, |del2|, and |del3| for greater accuracy;
//!   also set |del| to the first nonzero element of |(del1,del2,del3)|@>;
//! if del<>0 then {they weren't all zero}
//!   begin if del<0 then @<Swap the |x| and |y| coordinates of the
//!     cubic between |p| and~|q|@>;
//!   t:=crossing_point(del1,del2,del3);
//!   if t<fraction_one then
//!     @<Subdivide the cubic with respect to $x'-y'$, possibly twice@>;
//!   end
//!
//! @ @<Set up the variables |(del1,del2,del3)| to represent $x'-y'$@>=
//! if q=cur_spec then
//!   begin unskew(x_coord(q),y_coord(q),right_type(q));
//!   skew(cur_x,cur_y,right_type(p)); dest_x:=cur_x; dest_y:=cur_y;
//!   end
//! else  begin abnegate(x_coord(q),y_coord(q),right_type(q),right_type(p));
//!   dest_x:=cur_x-cur_y; dest_y:=cur_y;
//!   end;
//! del1:=right_x(p)-x_coord(p); del2:=left_x(q)-right_x(p);
//! del3:=dest_x-left_x(q)
//!
//! @ The swapping here doesn't simply interchange |x| and |y| values,
//! because the coordinates are skewed. It turns out that this is easier
//! than ordinary swapping, because it can be done in two assignment statements
//! rather than three.
//!
//! @ @<Swap the |x| and |y| coordinates...@>=
//! begin y_coord(p):=x_coord(p)+y_coord(p); negate(x_coord(p));@/
//! right_y(p):=right_x(p)+right_y(p); negate(right_x(p));@/
//! left_y(q):=left_x(q)+left_y(q); negate(left_x(q));@/
//! negate(del1); negate(del2); negate(del3);@/
//! dest_y:=dest_x+dest_y; negate(dest_x);@/
//! right_type(p):=right_type(p)+switch_x_and_y;
//! end
//!
//! @ A somewhat tedious case analysis is carried out here to make sure that
//! nasty rounding errors don't destroy our assumptions of monotonicity.
//!
//! @<Subdivide the cubic with respect to $x'-y'$, possibly twice@>=
//! begin split_cubic(p,t,dest_x,dest_y); r:=link(p);
//! if right_type(r)>switch_x_and_y then right_type(r):=right_type(r)-switch_x_and_y
//! else right_type(r):=right_type(r)+switch_x_and_y;
//! if y_coord(r)<y_coord(p) then y_coord(r):=y_coord(p)
//! else if y_coord(r)>dest_y then y_coord(r):=dest_y;
//! if x_coord(p)+y_coord(r)>dest_x+dest_y then
//!   y_coord(r):=dest_x+dest_y-x_coord(p);
//! if left_y(r)>y_coord(r) then
//!   begin left_y(r):=y_coord(r);
//!   if right_y(p)>y_coord(r) then right_y(p):=y_coord(r);
//!   end;
//! if right_y(r)<y_coord(r) then
//!   begin right_y(r):=y_coord(r);
//!   if left_y(q)<y_coord(r) then left_y(q):=y_coord(r);
//!   end;
//! if x_coord(r)<x_coord(p) then x_coord(r):=x_coord(p)
//! else if x_coord(r)+y_coord(r)>dest_x+dest_y then
//!   x_coord(r):=dest_x+dest_y-y_coord(r);
//! left_x(r):=x_coord(r);
//! if right_x(p)>x_coord(r) then right_x(p):=x_coord(r);
//!  {we always have |x_coord(p)<=right_x(p)|}
//! y_coord(r):=y_coord(r)+x_coord(r); right_y(r):=right_y(r)+x_coord(r);@/
//! negate(x_coord(r)); right_x(r):=x_coord(r);@/
//! left_y(q):=left_y(q)+left_x(q); negate(left_x(q));@/
//! dest_y:=dest_y+dest_x; negate(dest_x);
//! if right_y(r)<y_coord(r) then
//!   begin right_y(r):=y_coord(r);
//!   if left_y(q)<y_coord(r) then left_y(q):=y_coord(r);
//!   end;
//! del2:=t_of_the_way(del2)(del3);
//!   {now |0,del2,del3| represent $x'-y'$ on the remaining interval}
//! if del2>0 then del2:=0;
//! t:=crossing_point(0,-del2,-del3);
//! if t<fraction_one then
//!   @<Subdivide the cubic a second time with respect to $x'-y'$@>
//! else begin if x_coord(r)>dest_x then
//!     begin x_coord(r):=dest_x; left_x(r):=-x_coord(r); right_x(r):=x_coord(r);
//!     end;
//!   if left_x(q)>dest_x then left_x(q):=dest_x
//!   else if left_x(q)<x_coord(r) then left_x(q):=x_coord(r);
//!   end;
//! end
//!
//! @ @<Subdivide the cubic a second time with respect to $x'-y'$@>=
//! begin split_cubic(r,t,dest_x,dest_y); s:=link(r);@/
//! if y_coord(s)<y_coord(r) then y_coord(s):=y_coord(r)
//! else if y_coord(s)>dest_y then y_coord(s):=dest_y;
//! if x_coord(r)+y_coord(s)>dest_x+dest_y then
//!   y_coord(s):=dest_x+dest_y-x_coord(r);
//! if left_y(s)>y_coord(s) then
//!   begin left_y(s):=y_coord(s);
//!   if right_y(r)>y_coord(s) then right_y(r):=y_coord(s);
//!   end;
//! if right_y(s)<y_coord(s) then
//!   begin right_y(s):=y_coord(s);
//!   if left_y(q)<y_coord(s) then left_y(q):=y_coord(s);
//!   end;
//! if x_coord(s)+y_coord(s)>dest_x+dest_y then x_coord(s):=dest_x+dest_y-y_coord(s)
//! else begin if x_coord(s)<dest_x then x_coord(s):=dest_x;
//!   if x_coord(s)<x_coord(r) then x_coord(s):=x_coord(r);
//!   end;
//! right_type(s):=right_type(p);
//! left_x(s):=x_coord(s); {now |x_coord(r)=right_x(r)<=left_x(s)|}
//! if left_x(q)<dest_x then
//!   begin left_y(q):=left_y(q)+dest_x; left_x(q):=-dest_x;@+end
//! else if left_x(q)>x_coord(s) then
//!   begin left_y(q):=left_y(q)+x_coord(s); left_x(q):=-x_coord(s);@+end
//! else begin left_y(q):=left_y(q)+left_x(q); negate(left_x(q));@+end;
//! y_coord(s):=y_coord(s)+x_coord(s); right_y(s):=right_y(s)+x_coord(s);@/
//! negate(x_coord(s)); right_x(s):=x_coord(s);@/
//! if right_y(s)<y_coord(s) then
//!   begin right_y(s):=y_coord(s);
//!   if left_y(q)<y_coord(s) then left_y(q):=y_coord(s);
//!   end;
//! end
//!
//! @ It's time now to consider ``autorounding,'' which tries to make horizontal,
//! vertical, and diagonal tangents occur at places that will produce appropriate
//! images after the curve is digitized.
//!
//! The first job is to fix things so that |x(t)| plus the horizontal pen offset
//! is an integer multiple of the
//! current ``granularity'' when the derivative $x'(t)$ crosses through zero.
//! The given cyclic path contains regions where $x'(t)\G0$ and regions
//! where $x'(t)\L0$. The |quadrant_subdivide| routine is called into action
//! before any of the path coordinates have been skewed, but some of them
//! may have been negated. In regions where $x'(t)\G0$ we have |right_type=
//! first_octant| or |right_type=eighth_octant|; in regions where $x'(t)\L0$,
//! we have |right_type=fifth_octant| or |right_type=fourth_octant|.
//!
//! Within any such region the transformed $x$ values increase monotonically
//! from, say, $x_0$ to~$x_1$. We want to modify things by applying a linear
//! transformation to all $x$ coordinates in the region, after which
//! the $x$ values will increase monotonically from round$(x_0)$ to round$(x_1)$.
//!
//! This rounding scheme sounds quite simple, and it usually is. But several
//! complications can arise that might make the task more difficult. In the
//! first place, autorounding is inappropriate at cusps where $x'$ jumps
//! discontinuously past zero without ever being zero. In the second place,
//! the current pen might be unsymmetric in such a way that $x$ coordinates
//! should round differently in different parts of the curve.
//! These considerations imply that round$(x_0)$ might be greater
//! than round$(x_1)$, even though $x_0\L x_1$; in such cases we do not want
//! to carry out the linear transformation. Furthermore, it's possible to have
//! round$(x_1)-\hbox{round} (x_0)$ positive but much greater than $x_1-x_0$;
//! then the transformation might distort the curve drastically, and again we
//! want to avoid it. Finally, the rounded points must be consistent between
//! adjacent regions, hence we can't transform one region without knowing
//! about its neighbors.
//!
//! To handle all these complications, we must first look at the whole
//! cycle and choose rounded $x$ values that are ``safe.'' The following
//! procedure does this: Given $m$~values $(b_0,b_1,\ldots,b_{m-1})$ before
//! rounding and $m$~corresponding values $(a_0,a_1,\ldots,a_{m-1})$ that would
//! be desirable after rounding, the |make_safe| routine sets $a$'s to $b$'s
//! if necessary so that $0\L(a\k-a_k)/(b\k-b_k)\L2$ afterwards. It is
//! symmetric under cyclic permutation, reversal, and/or negation of the inputs.
//! (Instead of |a|, |b|, and~|m|, the program uses the names |after|,
//! |before|, and |cur_rounding_ptr|.)
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! procedure make_safe;
//! var @!k:0..max_wiggle; {runs through the list of inputs}
//! @!all_safe:boolean; {does everything look OK so far?}
//! @!next_a:scaled; {|after[k]| before it might have changed}
//! @!delta_a,@!delta_b:scaled; {|after[k+1]-after[k]| and |before[k+1]-before[k]|}
//! begin before[cur_rounding_ptr]:=before[0]; {wrap around}
//! node_to_round[cur_rounding_ptr]:=node_to_round[0];
//! repeat after[cur_rounding_ptr]:=after[0]; all_safe:=true; next_a:=after[0];
//! for k:=0 to cur_rounding_ptr-1 do
//!   begin delta_b:=before[k+1]-before[k];
//!   if delta_b>=0 then delta_a:=after[k+1]-next_a
//!   else delta_a:=next_a-after[k+1];
//!   next_a:=after[k+1];
//!   if (delta_a<0)or(delta_a>abs(delta_b+delta_b)) then
//!     begin all_safe:=false; after[k]:=before[k];
//!     if k=cur_rounding_ptr-1 then after[0]:=before[0]
//!     else after[k+1]:=before[k+1];
//!     end;
//!   end;
//! until all_safe;
//! end;
//!
//! @ The global arrays used by |make_safe| are accompanied by an array of
//! pointers into the current knot list.
//!
//! @<Glob...@>=
//! @!before,@!after:array[0..max_wiggle] of scaled; {data for |make_safe|}
//! @!node_to_round:array[0..max_wiggle] of pointer; {reference back to the path}
//! @!cur_rounding_ptr:0..max_wiggle; {how many are being used}
//! @!max_rounding_ptr:0..max_wiggle; {how many have been used}
//!
//! @ @<Set init...@>=
//! max_rounding_ptr:=0;
//!
//! @ New entries go into the tables via the |before_and_after| routine:
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! procedure before_and_after(@!b,@!a:scaled;@!p:pointer);
//! begin if cur_rounding_ptr=max_rounding_ptr then
//!   if max_rounding_ptr<max_wiggle then incr(max_rounding_ptr)
//!   else overflow("rounding table size",max_wiggle);
//! @:METAFONT capacity exceeded rounding table size}{\quad rounding table size@>
//! after[cur_rounding_ptr]:=a; before[cur_rounding_ptr]:=b;
//! node_to_round[cur_rounding_ptr]:=p; incr(cur_rounding_ptr);
//! end;
//!
//! @ A global variable called |cur_gran| is used instead of |internal[
//! granularity]|, because we want to work with a number that's guaranteed to
//! be positive.
//!
//! @<Glob...@>=
//! @!cur_gran:scaled; {the current granularity (which normally is |unity|)}
//!
//! @ The |good_val| function computes a number |a| that's as close as
//! possible to~|b|, with the property that |a+o| is a multiple of
//! |cur_gran|.
//!
//! If we assume that |cur_gran| is even (since it will in fact be a multiple
//! of |unity| in all reasonable applications), we have the identity
//! |good_val(-b-1,-o)=-good_val(b,o)|.
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! function good_val(@!b,@!o:scaled):scaled;
//! var @!a:scaled; {accumulator}
//! begin a:=b+o;
//! if a>=0 then a:=a-(a mod cur_gran)-o
//! else a:=a+((-(a+1)) mod cur_gran)-cur_gran+1-o;
//! if b-a<a+cur_gran-b then good_val:=a
//! else good_val:=a+cur_gran;
//! end;
//!
//! @ When we're rounding a doublepath, we might need to compromise between
//! two opposing tendencies, if the pen thickness is not a multiple of the
//! granularity. The following ``compromise'' adjustment, suggested by
//! John Hobby, finds the best way out of the dilemma. (Only the value
//! @^Hobby, John Douglas@>
//! modulo |cur_gran| is relevant in our applications, so the result turns
//! out to be essentially symmetric in |u| and~|v|.)
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! function compromise(@!u,@!v:scaled):scaled;
//! begin compromise:=half(good_val(u+u,-u-v));
//! end;
//!
//! @ Here, then, is the procedure that rounds $x$ coordinates as described;
//! it does the same for $y$ coordinates too, independently.
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! procedure xy_round;
//! var @!p,@!q:pointer; {list manipulation registers}
//! @!b,@!a:scaled; {before and after values}
//! @!pen_edge:scaled; {offset that governs rounding}
//! @!alpha:fraction; {coefficient of linear transformation}
//! begin cur_gran:=abs(internal[granularity]);
//! if cur_gran=0 then cur_gran:=unity;
//! p:=cur_spec; cur_rounding_ptr:=0;
//! repeat q:=link(p);
//! @<If node |q| is a transition point for |x| coordinates,
//!   compute and save its before-and-after coordinates@>;
//! p:=q;
//! until p=cur_spec;
//! if cur_rounding_ptr>0 then @<Transform the |x| coordinates@>;
//! p:=cur_spec; cur_rounding_ptr:=0;
//! repeat q:=link(p);
//! @<If node |q| is a transition point for |y| coordinates,
//!   compute and save its before-and-after coordinates@>;
//! p:=q;
//! until p=cur_spec;
//! if cur_rounding_ptr>0 then @<Transform the |y| coordinates@>;
//! end;
//!
//! @ When |x| has been negated, the |octant| codes are even. We allow
//! for an error of up to .01 pixel (i.e., 655 |scaled| units) in the
//! derivative calculations at transition nodes.
//!
//! @<If node |q| is a transition point for |x| coordinates...@>=
//! if odd(right_type(p))<>odd(right_type(q)) then
//!   begin if odd(right_type(q)) then b:=x_coord(q)@+else b:=-x_coord(q);
//!   if (abs(x_coord(q)-right_x(q))<655)or@|
//!     (abs(x_coord(q)+left_x(q))<655) then
//!     @<Compute before-and-after |x| values based on the current pen@>
//!   else a:=b;
//!   if abs(a)>max_allowed then
//!     if a>0 then a:=max_allowed@+else a:=-max_allowed;
//!   before_and_after(b,a,q);
//!   end
//!
//! @ When we study the data representation for pens, we'll learn that the
//! |x|~coordinate of the current pen's west edge is
//! $$\hbox{|y_coord(link(cur_pen+seventh_octant))|},$$
//! and that there are similar ways to address other important offsets.
//!
//! @d north_edge(#)==y_coord(link(#+fourth_octant))
//! @d south_edge(#)==y_coord(link(#+first_octant))
//! @d east_edge(#)==y_coord(link(#+second_octant))
//! @d west_edge(#)==y_coord(link(#+seventh_octant))
//!
//! @<Compute before-and-after |x| values based on the current pen@>=
//! begin if cur_pen=null_pen then pen_edge:=0
//! else if cur_path_type=double_path_code then
//!   pen_edge:=compromise(east_edge(cur_pen),west_edge(cur_pen))
//! else if odd(right_type(q)) then pen_edge:=west_edge(cur_pen)
//! else pen_edge:=east_edge(cur_pen);
//! a:=good_val(b,pen_edge);
//! end
//!
//! @  The monotone transformation computed here with fixed-point arithmetic is
//! guaranteed to take consecutive |before| values $(b,b')$ into consecutive
//! |after| values $(a,a')$, even in the presence of rounding errors,
//! as long as $\vert b-b'\vert<2^{28}$.
//!
//! @<Transform the |x| coordinates@>=
//! begin make_safe;
//! repeat decr(cur_rounding_ptr);
//! if (after[cur_rounding_ptr]<>before[cur_rounding_ptr])or@|
//!  (after[cur_rounding_ptr+1]<>before[cur_rounding_ptr+1]) then
//!   begin p:=node_to_round[cur_rounding_ptr];
//!   if odd(right_type(p)) then
//!     begin b:=before[cur_rounding_ptr]; a:=after[cur_rounding_ptr];
//!     end
//!   else  begin b:=-before[cur_rounding_ptr]; a:=-after[cur_rounding_ptr];
//!     end;
//!   if before[cur_rounding_ptr]=before[cur_rounding_ptr+1] then
//!     alpha:=fraction_one
//!   else alpha:=make_fraction(after[cur_rounding_ptr+1]-after[cur_rounding_ptr],@|
//!     before[cur_rounding_ptr+1]-before[cur_rounding_ptr]);
//!   repeat x_coord(p):=take_fraction(alpha,x_coord(p)-b)+a;
//!   right_x(p):=take_fraction(alpha,right_x(p)-b)+a;
//!   p:=link(p); left_x(p):=take_fraction(alpha,left_x(p)-b)+a;
//!   until p=node_to_round[cur_rounding_ptr+1];
//!   end;
//! until cur_rounding_ptr=0;
//! end
//!
//! @ When |y| has been negated, the |octant| codes are |>negate_y|. Otherwise
//! these routines are essentially identical to the routines for |x| coordinates
//! that we have just seen.
//!
//! @<If node |q| is a transition point for |y| coordinates...@>=
//! if (right_type(p)>negate_y)<>(right_type(q)>negate_y) then
//!   begin if right_type(q)<=negate_y then b:=y_coord(q)@+else b:=-y_coord(q);
//!   if (abs(y_coord(q)-right_y(q))<655)or@|
//!     (abs(y_coord(q)+left_y(q))<655) then
//!     @<Compute before-and-after |y| values based on the current pen@>
//!   else a:=b;
//!   if abs(a)>max_allowed then
//!     if a>0 then a:=max_allowed@+else a:=-max_allowed;
//!   before_and_after(b,a,q);
//!   end
//!
//! @ @<Compute before-and-after |y| values based on the current pen@>=
//! begin if cur_pen=null_pen then pen_edge:=0
//! else if cur_path_type=double_path_code then
//!   pen_edge:=compromise(north_edge(cur_pen),south_edge(cur_pen))
//! else if right_type(q)<=negate_y then pen_edge:=south_edge(cur_pen)
//! else pen_edge:=north_edge(cur_pen);
//! a:=good_val(b,pen_edge);
//! end
//!
//! @ @<Transform the |y| coordinates@>=
//! begin make_safe;
//! repeat decr(cur_rounding_ptr);
//! if (after[cur_rounding_ptr]<>before[cur_rounding_ptr])or@|
//!  (after[cur_rounding_ptr+1]<>before[cur_rounding_ptr+1]) then
//!   begin p:=node_to_round[cur_rounding_ptr];
//!   if right_type(p)<=negate_y then
//!     begin b:=before[cur_rounding_ptr]; a:=after[cur_rounding_ptr];
//!     end
//!   else  begin b:=-before[cur_rounding_ptr]; a:=-after[cur_rounding_ptr];
//!     end;
//!   if before[cur_rounding_ptr]=before[cur_rounding_ptr+1] then
//!     alpha:=fraction_one
//!   else alpha:=make_fraction(after[cur_rounding_ptr+1]-after[cur_rounding_ptr],@|
//!     before[cur_rounding_ptr+1]-before[cur_rounding_ptr]);
//!   repeat y_coord(p):=take_fraction(alpha,y_coord(p)-b)+a;
//!   right_y(p):=take_fraction(alpha,right_y(p)-b)+a;
//!   p:=link(p); left_y(p):=take_fraction(alpha,left_y(p)-b)+a;
//!   until p=node_to_round[cur_rounding_ptr+1];
//!   end;
//! until cur_rounding_ptr=0;
//! end
//!
//! @ Rounding at diagonal tangents takes place after the subdivision into
//! octants is complete, hence after the coordinates have been skewed.
//! The details are somewhat tricky, because we want to round to points
//! whose skewed coordinates are halfway between integer multiples of
//! the granularity. Furthermore, both coordinates change when they are
//! rounded; this means we need a generalization of the |make_safe| routine,
//! ensuring safety in both |x| and |y|.
//!
//! In spite of these extra complications, we can take comfort in the fact
//! that the basic structure of the routine is the same as before.
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! procedure diag_round;
//! var @!p,@!q,@!pp:pointer; {list manipulation registers}
//! @!b,@!a,@!bb,@!aa,@!d,@!c,@!dd,@!cc:scaled; {before and after values}
//! @!pen_edge:scaled; {offset that governs rounding}
//! @!alpha,@!beta:fraction; {coefficients of linear transformation}
//! @!next_a:scaled; {|after[k]| before it might have changed}
//! @!all_safe:boolean; {does everything look OK so far?}
//! @!k:0..max_wiggle; {runs through before-and-after values}
//! @!first_x,@!first_y:scaled; {coordinates before rounding}
//! begin p:=cur_spec; cur_rounding_ptr:=0;
//! repeat q:=link(p);
//! @<If node |q| is a transition point between octants,
//!   compute and save its before-and-after coordinates@>;
//! p:=q;
//! until p=cur_spec;
//! if cur_rounding_ptr>0 then @<Transform the skewed coordinates@>;
//! end;
//!
//! @ We negate the skewed |x| coordinates in the before-and-after table when
//! the octant code is greater than |switch_x_and_y|.
//!
//! @<If node |q| is a transition point between octants...@>=
//! if right_type(p)<>right_type(q) then
//!   begin if right_type(q)>switch_x_and_y then b:=-x_coord(q)
//!   else b:=x_coord(q);
//!   if abs(right_type(q)-right_type(p))=switch_x_and_y then
//!     if (abs(x_coord(q)-right_x(q))<655)or(abs(x_coord(q)+left_x(q))<655) then
//!       @<Compute a good coordinate at a diagonal transition@>
//!     else a:=b
//!   else a:=b;
//!   before_and_after(b,a,q);
//!   end
//!
//! @ In octants whose code number is even, $x$~has been
//! negated; we want to round ambiguous cases downward instead of upward,
//! so that the rounding will be consistent with octants whose code
//! number is odd. This downward bias can be achieved by
//! subtracting~1 from the first argument of |good_val|.
//!
//! @d diag_offset(#)==x_coord(knil(link(cur_pen+#)))
//!
//! @<Compute a good coordinate at a diagonal transition@>=
//! begin if cur_pen=null_pen then pen_edge:=0
//! else if cur_path_type=double_path_code then @<Compute a compromise |pen_edge|@>
//! else if right_type(q)<=switch_x_and_y then pen_edge:=diag_offset(right_type(q))
//! else pen_edge:=-diag_offset(right_type(q));
//! if odd(right_type(q)) then a:=good_val(b,pen_edge+half(cur_gran))
//! else a:=good_val(b-1,pen_edge+half(cur_gran));
//! end
//!
//! @ (It seems a shame to compute these compromise offsets repeatedly. The
//! author would have stored them directly in the pen data structure, if the
//! granularity had been constant.)
//!
//! @<Compute a compromise...@>=
//! case right_type(q) of
//! first_octant,second_octant:pen_edge:=compromise(diag_offset(first_octant),@|
//!     -diag_offset(fifth_octant));
//! fifth_octant,sixth_octant:pen_edge:=-compromise(diag_offset(first_octant),@|
//!     -diag_offset(fifth_octant));
//! third_octant,fourth_octant:pen_edge:=compromise(diag_offset(fourth_octant),@|
//!     -diag_offset(eighth_octant));
//! seventh_octant,eighth_octant:pen_edge:=-compromise(diag_offset(fourth_octant),@|
//!     -diag_offset(eighth_octant));
//! end {there are no other cases}
//!
//! @ @<Transform the skewed coordinates@>=
//! begin p:=node_to_round[0]; first_x:=x_coord(p); first_y:=y_coord(p);
//! @<Make sure that all the diagonal roundings are safe@>;
//! for k:=0 to cur_rounding_ptr-1 do
//!   begin a:=after[k]; b:=before[k];
//!   aa:=after[k+1]; bb:=before[k+1];
//!   if (a<>b)or(aa<>bb) then
//!     begin p:=node_to_round[k]; pp:=node_to_round[k+1];
//!     @<Determine the before-and-after values of both coordinates@>;
//!     if b=bb then alpha:=fraction_one
//!     else alpha:=make_fraction(aa-a,bb-b);
//!     if d=dd then beta:=fraction_one
//!     else beta:=make_fraction(cc-c,dd-d);
//!     repeat x_coord(p):=take_fraction(alpha,x_coord(p)-b)+a;
//!     y_coord(p):=take_fraction(beta,y_coord(p)-d)+c;
//!     right_x(p):=take_fraction(alpha,right_x(p)-b)+a;
//!     right_y(p):=take_fraction(beta,right_y(p)-d)+c;
//!     p:=link(p); left_x(p):=take_fraction(alpha,left_x(p)-b)+a;
//!     left_y(p):=take_fraction(beta,left_y(p)-d)+c;
//!     until p=pp;
//!     end;
//!   end;
//! end
//!
//! @ In node |p|, the coordinates |(b,d)| will be rounded to |(a,c)|;
//! in node |pp|, the coordinates |(bb,dd)| will be rounded to |(aa,cc)|.
//! (We transform the values from node |pp| so that they agree with the
//! conventions of node |p|.)
//!
//! If |aa<>bb|, we know that |abs(right_type(p)-right_type(pp))=switch_x_and_y|.
//!
//! @<Determine the before-and-after values of both coordinates@>=
//! if aa=bb then
//!   begin if pp=node_to_round[0] then
//!     unskew(first_x,first_y,right_type(pp))
//!   else unskew(x_coord(pp),y_coord(pp),right_type(pp));
//!   skew(cur_x,cur_y,right_type(p));
//!   bb:=cur_x; aa:=bb; dd:=cur_y; cc:=dd;
//!   if right_type(p)>switch_x_and_y then
//!     begin b:=-b; a:=-a;
//!     end;
//!   end
//! else  begin if right_type(p)>switch_x_and_y then
//!     begin bb:=-bb; aa:=-aa; b:=-b; a:=-a;
//!     end;
//!   if pp=node_to_round[0] then dd:=first_y-bb@+else dd:=y_coord(pp)-bb;
//!   if odd(aa-bb) then
//!     if right_type(p)>switch_x_and_y then cc:=dd-half(aa-bb+1)
//!     else cc:=dd-half(aa-bb-1)
//!   else cc:=dd-half(aa-bb);
//!   end;
//! d:=y_coord(p);
//! if odd(a-b) then
//!   if right_type(p)>switch_x_and_y then c:=d-half(a-b-1)
//!   else c:=d-half(a-b+1)
//! else c:=d-half(a-b)
//!
//! @ @<Make sure that all the diagonal roundings are safe@>=
//! before[cur_rounding_ptr]:=before[0]; {cf.~|make_safe|}
//! node_to_round[cur_rounding_ptr]:=node_to_round[0];
//! repeat after[cur_rounding_ptr]:=after[0]; all_safe:=true; next_a:=after[0];
//! for k:=0 to cur_rounding_ptr-1 do
//!   begin a:=next_a; b:=before[k]; next_a:=after[k+1];
//!   aa:=next_a; bb:=before[k+1];
//!   if (a<>b)or(aa<>bb) then
//!     begin p:=node_to_round[k]; pp:=node_to_round[k+1];
//!     @<Determine the before-and-after values of both coordinates@>;
//!     if (aa<a)or(cc<c)or(aa-a>2*(bb-b))or(cc-c>2*(dd-d)) then
//!       begin all_safe:=false; after[k]:=before[k];
//!       if k=cur_rounding_ptr-1 then after[0]:=before[0]
//!       else after[k+1]:=before[k+1];
//!       end;
//!     end;
//!   end;
//! until all_safe
//!
//! @ Here we get rid of ``dead'' cubics, i.e., polynomials that don't move at
//! all when |t|~changes, since the subdivision process might have introduced
//! such things.  If the cycle reduces to a single point, however, we are left
//! with a single dead cubic that will not be removed until later.
//!
//! @<Remove dead cubics@>=
//! p:=cur_spec;
//! repeat continue: q:=link(p);
//! if p<>q then
//!   begin if x_coord(p)=right_x(p) then
//!    if y_coord(p)=right_y(p) then
//!     if x_coord(p)=left_x(q) then
//!      if y_coord(p)=left_y(q) then
//!     begin unskew(x_coord(q),y_coord(q),right_type(q));
//!     skew(cur_x,cur_y,right_type(p));
//!     if x_coord(p)=cur_x then if y_coord(p)=cur_y then
//!       begin remove_cubic(p); {remove the cubic following |p|}
//!       if q<>cur_spec then goto continue;
//!       cur_spec:=p; q:=p;
//!       end;
//!     end;
//!   end;
//! p:=q;
//! until p=cur_spec;
//!
//! @ Finally we come to the last steps of |make_spec|, when boundary nodes
//! are inserted between cubics that move in different octants. The main
//! complication remaining arises from consecutive cubics whose octants
//! are not adjacent; we should insert more than one octant boundary
//! at such sharp turns, so that the envelope-forming routine will work.
//!
//! For this purpose, conversion tables between numeric and Gray codes for
//! octants are desirable.
//!
//! @<Glob...@>=
//! @!octant_number:array[first_octant..sixth_octant] of 1..8;
//! @!octant_code:array[1..8] of first_octant..sixth_octant;
//!
//! @ @<Set init...@>=
//! octant_code[1]:=first_octant;
//! octant_code[2]:=second_octant;
//! octant_code[3]:=third_octant;
//! octant_code[4]:=fourth_octant;
//! octant_code[5]:=fifth_octant;
//! octant_code[6]:=sixth_octant;
//! octant_code[7]:=seventh_octant;
//! octant_code[8]:=eighth_octant;
//! for k:=1 to 8 do octant_number[octant_code[k]]:=k;
//!
//! @ The main loop for boundary insertion deals with three consecutive
//! nodes |p,q,r|.
//!
//! @<Insert octant boundaries and compute the turning number@>=
//! turning_number:=0;
//! p:=cur_spec; q:=link(p);
//! repeat r:=link(q);
//! if (right_type(p)<>right_type(q))or(q=r) then
//!   @<Insert one or more octant boundary nodes just before~|q|@>;
//! p:=q; q:=r;
//! until p=cur_spec;
//!
//! @ The |new_boundary| subroutine comes in handy at this point. It inserts
//! a new boundary node just after a given node |p|, using a given octant code
//! to transform the new node's coordinates. The ``transition'' fields are
//! not computed here.
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! procedure new_boundary(@!p:pointer;@!octant:small_number);
//! var @!q,@!r:pointer; {for list manipulation}
//! begin q:=link(p); {we assume that |right_type(q)<>endpoint|}
//! r:=get_node(knot_node_size); link(r):=q; link(p):=r;
//! left_type(r):=left_type(q); {but possibly |left_type(q)=endpoint|}
//! left_x(r):=left_x(q); left_y(r):=left_y(q);
//! right_type(r):=endpoint; left_type(q):=endpoint;
//! right_octant(r):=octant; left_octant(q):=right_type(q);
//! unskew(x_coord(q),y_coord(q),right_type(q));
//! skew(cur_x,cur_y,octant); x_coord(r):=cur_x; y_coord(r):=cur_y;
//! end;
//!
//! @ The case |q=r| occurs if and only if |p=q=r=cur_spec|, when we want to turn
//! $360^\circ$ in eight steps and then remove a solitary dead cubic.
//! The program below happens to work in that case, but the reader isn't
//! expected to understand why.
//!
//! @<Insert one or more octant boundary nodes just before~|q|@>=
//! begin new_boundary(p,right_type(p)); s:=link(p);
//! o1:=octant_number[right_type(p)]; o2:=octant_number[right_type(q)];
//! case o2-o1 of
//! 1,-7,7,-1: goto done;
//! 2,-6: clockwise:=false;
//! 3,-5,4,-4,5,-3: @<Decide whether or not to go clockwise@>;
//! 6,-2: clockwise:=true;
//! 0:clockwise:=rev_turns;
//! end; {there are no other cases}
//! @<Insert additional boundary nodes, then |goto done|@>;
//! done: if q=r then
//!   begin q:=link(q); r:=q; p:=s; link(s):=q; left_octant(q):=right_octant(q);
//!   left_type(q):=endpoint; free_node(cur_spec,knot_node_size); cur_spec:=q;
//!   end;
//! @<Fix up the transition fields and adjust the turning number@>;
//! end
//!
//! @ @<Other local variables for |make_spec|@>=
//! @!o1,@!o2:small_number; {octant numbers}
//! @!clockwise:boolean; {should we turn clockwise?}
//! @!dx1,@!dy1,@!dx2,@!dy2:integer; {directions of travel at a cusp}
//! @!dmax,@!del:integer; {temporary registers}
//!
//! @ A tricky question arises when a path jumps four octants. We want the
//! direction of turning to be counterclockwise if the curve has changed
//! direction by $180^\circ$, or by something so close to $180^\circ$ that
//! the difference is probably due to rounding errors; otherwise we want to
//! turn through an angle of less than $180^\circ$. This decision needs to
//! be made even when a curve seems to have jumped only three octants, since
//! a curve may approach direction $(-1,0)$ from the fourth octant, then
//! it might leave from direction $(+1,0)$ into the first.
//!
//! The following code solves the problem by analyzing the incoming
//! direction |(dx1,dy1)| and the outgoing direction |(dx2,dy2)|.
//!
//! @<Decide whether or not to go clockwise@>=
//! begin @<Compute the incoming and outgoing directions@>;
//! unskew(dx1,dy1,right_type(p)); del:=pyth_add(cur_x,cur_y);@/
//! dx1:=make_fraction(cur_x,del); dy1:=make_fraction(cur_y,del);
//!   {$\cos\theta_1$ and $\sin\theta_1$}
//! unskew(dx2,dy2,right_type(q)); del:=pyth_add(cur_x,cur_y);@/
//! dx2:=make_fraction(cur_x,del); dy2:=make_fraction(cur_y,del);
//!   {$\cos\theta_2$ and $\sin\theta_2$}
//! del:=take_fraction(dx1,dy2)-take_fraction(dx2,dy1); {$\sin(\theta_2-\theta_1)$}
//! if del>4684844 then clockwise:=false
//! else if del<-4684844 then clockwise:=true
//!   {$2^{28}\cdot\sin 1^\circ\approx4684844.68$}
//! else clockwise:=rev_turns;
//! end
//!
//! @ Actually the turnarounds just computed will be clockwise,
//! not counterclockwise, if
//! the global variable |rev_turns| is |true|; it is usually |false|.
//!
//! @<Glob...@>=
//! @!rev_turns:boolean; {should we make U-turns in the English manner?}
//!
//! @ @<Set init...@>=
//! rev_turns:=false;
//!
//! @ @<Compute the incoming and outgoing directions@>=
//! dx1:=x_coord(s)-left_x(s); dy1:=y_coord(s)-left_y(s);
//! if dx1=0 then if dy1=0 then
//!   begin dx1:=x_coord(s)-right_x(p); dy1:=y_coord(s)-right_y(p);
//!   if dx1=0 then if dy1=0 then
//!     begin dx1:=x_coord(s)-x_coord(p); dy1:=y_coord(s)-y_coord(p);
//!     end;  {and they {\sl can't} both be zero}
//!   end;
//! dmax:=abs(dx1);@+if abs(dy1)>dmax then dmax:=abs(dy1);
//! while dmax<fraction_one do
//!   begin double(dmax); double(dx1); double(dy1);
//!   end;
//! dx2:=right_x(q)-x_coord(q); dy2:=right_y(q)-y_coord(q);
//! if dx2=0 then if dy2=0 then
//!   begin dx2:=left_x(r)-x_coord(q); dy2:=left_y(r)-y_coord(q);
//!   if dx2=0 then if dy2=0 then
//!     begin if right_type(r)=endpoint then
//!       begin cur_x:=x_coord(r); cur_y:=y_coord(r);
//!       end
//!     else  begin unskew(x_coord(r),y_coord(r),right_type(r));
//!       skew(cur_x,cur_y,right_type(q));
//!       end;
//!     dx2:=cur_x-x_coord(q); dy2:=cur_y-y_coord(q);
//!     end;  {and they {\sl can't} both be zero}
//!   end;
//! dmax:=abs(dx2);@+if abs(dy2)>dmax then dmax:=abs(dy2);
//! while dmax<fraction_one do
//!   begin double(dmax); double(dx2); double(dy2);
//!   end
//!
//! @ @<Insert additional boundary nodes...@>=
//! loop@+  begin if clockwise then
//!     if o1=1 then o1:=8@+else decr(o1)
//!   else if o1=8 then o1:=1@+else incr(o1);
//!   if o1=o2 then goto done;
//!   new_boundary(s,octant_code[o1]);
//!   s:=link(s); left_octant(s):=right_octant(s);
//!   end
//!
//! @ Now it remains to insert the redundant
//! transition information into the |left_transition|
//! and |right_transition| fields between adjacent octants, in the octant
//! boundary nodes that have just been inserted between |link(p)| and~|q|.
//! The turning number is easily computed from these transitions.
//!
//! @<Fix up the transition fields and adjust the turning number@>=
//! p:=link(p);
//! repeat s:=link(p);
//! o1:=octant_number[right_octant(p)]; o2:=octant_number[left_octant(s)];
//! if abs(o1-o2)=1 then
//!   begin if o2<o1 then o2:=o1;
//!   if odd(o2) then right_transition(p):=axis
//!   else right_transition(p):=diagonal;
//!   end
//! else  begin if o1=8 then incr(turning_number)@+else decr(turning_number);
//!   right_transition(p):=axis;
//!   end;
//! left_transition(s):=right_transition(p);
//! p:=s;
//! until p=q
//!
//! @* \[22] Filling a contour.
//! Given the low-level machinery for making moves and for transforming a
//! cyclic path into a cycle spec, we're almost able to fill a digitized path.
//! All we need is a high-level routine that walks through the cycle spec and
//! controls the overall process.
//!
//! Our overall goal is to plot the integer points $\bigl(\round(x(t)),
//! \round(y(t))\bigr)$ and to connect them by rook moves, assuming that
//! $\round(x(t))$ and $\round(y(t))$ don't both jump simultaneously from
//! one integer to another as $t$~varies; these rook moves will be the edge
//! of the contour that will be filled. We have reduced this problem to the
//! case of curves that travel in first octant directions, i.e., curves
//! such that $0\L y'(t)\L x'(t)$, by transforming the original coordinates.
//!
//! \def\xtilde{{\tilde x}} \def\ytilde{{\tilde y}}
//! Another transformation makes the problem still simpler. We shall say that
//! we are working with {\sl biased coordinates\/} when $(x,y)$ has been
//! replaced by $(\xtilde,\ytilde)=(x-y,y+{1\over2})$. When a curve travels
//! in first octant directions, the corresponding curve with biased
//! coordinates travels in first {\sl quadrant\/} directions; the latter
//! condition is symmetric in $x$ and~$y$, so it has advantages for the
//! design of algorithms. The |make_spec| routine gives us skewed coordinates
//! $(x-y,y)$, hence we obtain biased coordinates by simply adding $1\over2$
//! to the second component.
//!
//! The most important fact about biased coordinates is that we can determine the
//! rounded unbiased path $\bigl(\round(x(t)),\round(y(t))\bigr)$ from the
//! truncated biased path $\bigl(\lfloor\xtilde(t)\rfloor,\lfloor\ytilde(t)\rfloor
//! \bigr)$ and information about the initial and final endpoints. If the
//! unrounded and unbiased
//! path begins at $(x_0,y_0)$ and ends at $(x_1,y_1)$, it's possible to
//! prove (by induction on the length of the truncated biased path) that the
//! rounded unbiased path is obtained by the following construction:
//!
//! \yskip\textindent{1)} Start at $\bigl(\round(x_0),\round(y_0)\bigr)$.
//!
//! \yskip\textindent{2)} If $(x_0+{1\over2})\bmod1\G(y_0+{1\over2})\bmod1$,
//! move one step right.
//!
//! \yskip\textindent{3)} Whenever the path
//! $\bigl(\lfloor\xtilde(t)\rfloor,\lfloor\ytilde(t)\rfloor\bigr)$
//! takes an upward step (i.e., when
//! $\lfloor\xtilde(t+\epsilon)\rfloor=\lfloor\xtilde(t)\rfloor$ and
//! $\lfloor\ytilde(t+\epsilon)\rfloor=\lfloor\ytilde(t)\rfloor+1$),
//! move one step up and then one step right.
//!
//! \yskip\textindent{4)} Whenever the path
//! $\bigl(\lfloor\xtilde(t)\rfloor,\lfloor\ytilde(t)\rfloor\bigr)$
//! takes a rightward step (i.e., when
//! $\lfloor\xtilde(t+\epsilon)\rfloor=\lfloor\xtilde(t)\rfloor+1$ and
//! $\lfloor\ytilde(t+\epsilon)\rfloor=\lfloor\ytilde(t)\rfloor$),
//! move one step right.
//!
//! \yskip\textindent{5)} Finally, if
//! $(x_1+{1\over2})\bmod1\G(y_1+{1\over2})\bmod1$, move one step left (thereby
//! cancelling the previous move, which was one step right). You will now be
//! at the point $\bigl(\round(x_1),\round(y_1)\bigr)$.
//!
//! @ In order to validate the assumption that $\round(x(t))$ and $\round(y(t))$
//! don't both jump simultaneously, we shall consider that a coordinate pair
//! $(x,y)$ actually represents $(x+\epsilon,y+\epsilon\delta)$, where
//! $\epsilon$ and $\delta$ are extremely small positive numbers---so small
//! that their precise values never matter.  This convention makes rounding
//! unambiguous, since there is always a unique integer point nearest to any
//! given scaled numbers~$(x,y)$.
//!
//! When coordinates are transformed so that \MF\ needs to work only in ``first
//! octant'' directions, the transformations involve negating~$x$, negating~$y$,
//! and/or interchanging $x$ with~$y$. Corresponding adjustments to the
//! rounding conventions must be made so that consistent values will be
//! obtained. For example, suppose that we're working with coordinates that
//! have been transformed so that a third-octant curve travels in first-octant
//! directions. The skewed coordinates $(x,y)$ in our data structure represent
//! unskewed coordinates $(-y,x+y)$, which are actually $(-y+\epsilon,
//! x+y+\epsilon\delta)$. We should therefore round as if our skewed coordinates
//! were $(x+\epsilon+\epsilon\delta,y-\epsilon)$ instead of $(x,y)$. The following
//! table shows how the skewed coordinates should be perturbed when rounding
//! decisions are made:
//! $$\vcenter{\halign{#\hfil&&\quad$#$\hfil&\hskip4em#\hfil\cr
//! |first_octant|&(x+\epsilon-\epsilon\delta,y+\epsilon\delta)&
//!  |fifth_octant|&(x-\epsilon+\epsilon\delta,y-\epsilon\delta)\cr
//! |second_octant|&(x-\epsilon+\epsilon\delta,y+\epsilon)&
//!  |sixth_octant|&(x+\epsilon-\epsilon\delta,y-\epsilon)\cr
//! |third_octant|&(x+\epsilon+\epsilon\delta,y-\epsilon)&
//!  |seventh_octant|&(x-\epsilon-\epsilon\delta,y+\epsilon)\cr
//! |fourth_octant|&(x-\epsilon-\epsilon\delta,y+\epsilon\delta)&
//!  |eighth_octant|&(x+\epsilon+\epsilon\delta,y-\epsilon\delta)\cr}}$$
//!
//! Four small arrays are set up so that the rounding operations will be
//! fairly easy in any given octant.
//!
//! @<Glob...@>=
//! @!y_corr,@!xy_corr,@!z_corr:array[first_octant..sixth_octant] of 0..1;
//! @!x_corr:array[first_octant..sixth_octant] of -1..1;
//!
//! @ Here |xy_corr| is 1 if and only if the $x$ component of a skewed coordinate
//! is to be decreased by an infinitesimal amount; |y_corr| is similar, but for
//! the $y$ components. The other tables are set up so that the condition
//! $$(x+y+|half_unit|)\bmod|unity|\G(y+|half_unit|)\bmod|unity|$$
//! is properly perturbed to the condition
//! $$(x+y+|half_unit|-|x_corr|-|y_corr|)\bmod|unity|\G
//!   (y+|half_unit|-|y_corr|)\bmod|unity|+|z_corr|.$$
//!
//! @<Set init...@>=
//! x_corr[first_octant]:=0; y_corr[first_octant]:=0;
//! xy_corr[first_octant]:=0;@/
//! x_corr[second_octant]:=0; y_corr[second_octant]:=0;
//! xy_corr[second_octant]:=1;@/
//! x_corr[third_octant]:=-1; y_corr[third_octant]:=1;
//! xy_corr[third_octant]:=0;@/
//! x_corr[fourth_octant]:=1; y_corr[fourth_octant]:=0;
//! xy_corr[fourth_octant]:=1;@/
//! x_corr[fifth_octant]:=0; y_corr[fifth_octant]:=1;
//! xy_corr[fifth_octant]:=1;@/
//! x_corr[sixth_octant]:=0; y_corr[sixth_octant]:=1;
//! xy_corr[sixth_octant]:=0;@/
//! x_corr[seventh_octant]:=1; y_corr[seventh_octant]:=0;
//! xy_corr[seventh_octant]:=1;@/
//! x_corr[eighth_octant]:=-1; y_corr[eighth_octant]:=1;
//! xy_corr[eighth_octant]:=0;@/
//! for k:=1 to 8 do z_corr[k]:=xy_corr[k]-x_corr[k];
//!
//! @ Here's a procedure that handles the details of rounding at the
//! endpoints: Given skewed coordinates |(x,y)|, it sets |(m1,n1)|
//! to the corresponding rounded lattice points, taking the current
//! |octant| into account. Global variable |d1| is also set to 1 if
//! $(x+y+{1\over2})\bmod1\G(y+{1\over2})\bmod1$.
//!
//! @p procedure end_round(@!x,@!y:scaled);
//! begin y:=y+half_unit-y_corr[octant];
//! x:=x+y-x_corr[octant];
//! m1:=floor_unscaled(x); n1:=floor_unscaled(y);
//! if x-unity*m1>=y-unity*n1+z_corr[octant] then d1:=1@+else d1:=0;
//! end;
//!
//! @ The outputs |(m1,n1,d1)| of |end_round| will sometimes be moved
//! to |(m0,n0,d0)|.
//!
//! @<Glob...@>=
//! @!m0,@!n0,@!m1,@!n1:integer; {lattice point coordinates}
//! @!d0,@!d1:0..1; {displacement corrections}
//!
//! @ We're ready now to fill the pixels enclosed by a given cycle spec~|h|;
//! the knot list that represents the cycle is destroyed in the process.
//! The edge structure that gets all the resulting data is |cur_edges|,
//! and the edges are weighted by |cur_wt|.
//!
//! @p procedure fill_spec(@!h:pointer);
//! var @!p,@!q,@!r,@!s:pointer; {for list traversal}
//! begin if internal[tracing_edges]>0 then begin_edge_tracing;
//! p:=h; {we assume that |left_type(h)=endpoint|}
//! repeat octant:=left_octant(p);
//! @<Set variable |q| to the node at the end of the current octant@>;
//! if q<>p then
//!   begin @<Determine the starting and ending
//!     lattice points |(m0,n0)| and |(m1,n1)|@>;
//!   @<Make the moves for the current octant@>;
//!   move_to_edges(m0,n0,m1,n1);
//!   end;
//! p:=link(q);
//! until p=h;
//! toss_knot_list(h);
//! if internal[tracing_edges]>0 then end_edge_tracing;
//! end;
//!
//! @ @<Set variable |q| to the node at the end of the current octant@>=
//! q:=p;
//! while right_type(q)<>endpoint do q:=link(q)
//!
//! @ @<Determine the starting and ending lattice points |(m0,n0)| and |(m1,n1)|@>=
//! end_round(x_coord(p),y_coord(p)); m0:=m1; n0:=n1; d0:=d1;@/
//! end_round(x_coord(q),y_coord(q))
//!
//! @ Finally we perform the five-step process that was explained at
//! the very beginning of this part of the program.
//!
//! @<Make the moves for the current octant@>=
//! if n1-n0>=move_size then overflow("move table size",move_size);
//! @:METAFONT capacity exceeded move table size}{\quad move table size@>
//! move[0]:=d0; move_ptr:=0; r:=p;
//! repeat s:=link(r);@/
//! make_moves(x_coord(r),right_x(r),left_x(s),x_coord(s),@|
//!   y_coord(r)+half_unit,right_y(r)+half_unit,left_y(s)+half_unit,
//!   y_coord(s)+half_unit,@| xy_corr[octant],y_corr[octant]);
//! r:=s;
//! until r=q;
//! move[move_ptr]:=move[move_ptr]-d1;
//! if internal[smoothing]>0 then smooth_moves(0,move_ptr)
//!
//! @* \[23] Polygonal pens.
//! The next few parts of the program deal with the additional complications
//! associated with ``envelopes,'' leading up to an algorithm that fills a
//! contour with respect to a pen whose boundary is a convex polygon. The
//! mathematics underlying this algorithm is based on simple aspects of the
//! theory of tracings developed by Leo Guibas, Lyle Ramshaw, and Jorge
//! Stolfi [``A kinetic framework for computational geometry,''
//! {\sl Proc.\ IEEE Symp.\ Foundations of Computer Science\/ \bf24} (1983),
//! 100--111].
//! @^Guibas, Leonidas Ioannis@>
//! @^Ramshaw, Lyle Harold@>
//! @^Stolfi, Jorge@>
//!
//! If the vertices of the polygon are $w_0$, $w_1$, \dots, $w_{n-1}$, $w_n=w_0$,
//! in counterclockwise order, the convexity condition requires that ``left
//! turns'' are made at each vertex when a person proceeds from $w_0$ to
//! $w_1$ to $\cdots$ to~$w_n$. The envelope is obtained if we offset a given
//! curve $z(t)$ by $w_k$ when that curve is traveling in a direction
//! $z'(t)$ lying between the directions $w_k-w_{k-1}$ and $w\k-w_k$.
//! At times~$t$ when the curve direction $z'(t)$ increases past
//! $w\k-w_k$, we temporarily stop plotting the offset curve and we insert
//! a straight line from $z(t)+w_k$ to $z(t)+w\k$; notice that this straight
//! line is tangent to the offset curve. Similarly, when the curve direction
//! decreases past $w_k-w_{k-1}$, we stop plotting and insert a straight
//! line from $z(t)+w_k$ to $z(t)+w_{k-1}$; the latter line is actually a
//! ``retrograde'' step, which won't be part of the final envelope under
//! \MF's assumptions. The result of this construction is a continuous path
//! that consists of alternating curves and straight line segments. The
//! segments are usually so short, in practice, that they blend with the
//! curves; after all, it's possible to represent any digitized path as
//! a sequence of digitized straight lines.
//!
//! The nicest feature of this approach to envelopes is that it blends
//! perfectly with the octant subdivision process we have already developed.
//! The envelope travels in the same direction as the curve itself, as we
//! plot it, and we need merely be careful what offset is being added.
//! Retrograde motion presents a problem, but we will see that there is
//! a decent way to handle it.
//!
//! @ We shall represent pens by maintaining eight lists of offsets,
//! one for each octant direction. The offsets at the boundary points
//! where a curve turns into a new octant will appear in the lists for
//! both octants. This means that we can restrict consideration to
//! segments of the original polygon whose directions aim in the first
//! octant, as we have done in the simpler case when envelopes were not
//! required.
//!
//! An example should help to clarify this situation: Consider the
//! quadrilateral whose vertices are $w_0=(0,-1)$, $w_1=(3,-1)$,
//! $w_2=(6,1)$, and $w_3=(1,2)$. A curve that travels in the first octant
//! will be offset by $w_1$ or $w_2$, unless its slope drops to zero
//! en route to the eighth octant; in the latter case we should switch to $w_0$ as
//! we cross the octant boundary. Our list for the first octant will
//! contain the three offsets $w_0$, $w_1$,~$w_2$. By convention we will
//! duplicate a boundary offset if the angle between octants doesn't
//! explicitly appear; in this case there is no explicit line of slope~1
//! at the end of the list, so the full list is
//! $$w_0\;w_1\;w_2\;w_2\;=\;(0,-1)\;(3,-1)\;(6,1)\;(6,1).$$
//! With skewed coordinates $(u-v,v)$ instead of $(u,v)$ we obtain the list
//! $$w_0\;w_1\;w_2\;w_2\;\mapsto\;(1,-1)\;(4,-1)\;(5,1)\;(5,1),$$
//! which is what actually appears in the data structure. In the second
//! octant there's only one offset; we list it twice (with coordinates
//! interchanged, so as to make the second octant look like the first),
//! and skew those coordinates, obtaining
//! $$\tabskip\centering
//! \halign to\hsize{$\hfil#\;\mapsto\;{}$\tabskip=0pt&
//!   $#\hfil$&\quad in the #\hfil\tabskip\centering\cr
//! w_2\;w_2&(-5,6)\;(-5,6)\cr
//! \noalign{\vskip\belowdisplayskip
//! \vbox{\noindent\strut as the list of transformed and skewed offsets to use
//! when curves travel in the second octant. Similarly, we will have\strut}
//! \vskip\abovedisplayskip}
//! w_2\;w_2&(7,-6)\;(7,-6)&third;\cr
//! w_2\;w_2\;w_3\;w_3&(-7,1)\;(-7,1)\;(-3,2)\;(-3,2)&fourth;\cr
//! w_3\;w_3&(1,-2)\;(1,-2)&fifth;\cr
//! w_3\;w_3\;w_0\;w_0&(-1,1)\;(-1,1)\;(1,0)\;(1,0)&sixth;\cr
//! w_0\;w_0&(1,0)\;(1,0)&seventh;\cr
//! w_0\;w_0&(-1,1)\;(-1,1)&eighth.\cr}$$
//! Notice that $w_1$ is considered here to be internal to the first octant;
//! it's not part of the eighth. We could equally well have taken $w_0$ out
//! of the first octant list and put it into the eighth; then the first octant
//! list would have been
//! $$w_1\;w_1\;w_2\;w_2\;\mapsto\;(4,-1)\;(4,-1)\;(5,1)\;(5,1)$$
//! and the eighth octant list would have been
//! $$w_0\;w_0\;w_1\;\mapsto\;(-1,1)\;(-1,1)\;(2,1).$$
//!
//! Actually, there's one more complication: The order of offsets is reversed
//! in even-numbered octants, because the transformation of coordinates has
//! reversed counterclockwise and clockwise orientations in those octants.
//! The offsets in the fourth octant, for example, are really $w_3$, $w_3$,
//! $w_2$,~$w_2$, not $w_2$, $w_2$, $w_3$,~$w_3$.
//!
//! @ In general, the list of offsets for an octant will have the form
//! $$w_0\;\;w_1\;\;\ldots\;\;w_n\;\;w_{n+1}$$
//! (if we renumber the subscripts in each list), where $w_0$ and $w_{n+1}$
//! are offsets common to the neighboring lists. We'll often have $w_0=w_1$
//! and/or $w_n=w_{n+1}$, but the other $w$'s will be distinct. Curves
//! that travel between slope~0 and direction $w_2-w_1$ will use offset~$w_1$;
//! curves that travel between directions $w_k-w_{k-1}$ and $w\k-w_k$ will
//! use offset~$w_k$, for $1<k<n$; curves between direction $w_n-w_{n-1}$
//! and slope~1 (actually slope~$\infty$ after skewing) will use offset~$w_n$.
//! In even-numbered octants, the directions are actually $w_k-w\k$ instead
//! of $w\k-w_k$, because the offsets have been listed in reverse order.
//!
//! Each offset $w_k$ is represented by skewed coordinates $(u_k-v_k,v_k)$,
//! where $(u_k,v_k)$ is the representation of $w_k$ after it has been rotated
//! into a first-octant disguise.
//!
//! @ The top-level data structure of a pen polygon is a 10-word node containing
//! a reference count followed by pointers to the eight offset lists, followed
//! by an indication of the pen's range of values.
//! @^reference counts@>
//!
//! If |p|~points to such a node, and if the
//! offset list for, say, the fourth octant has entries $w_0$, $w_1$, \dots,
//! $w_n$,~$w_{n+1}$, then |info(p+fourth_octant)| will equal~$n$, and
//! |link(p+fourth_octant)| will point to the offset node containing~$w_0$.
//! Memory location |p+fourth_octant| is said to be the {\sl header\/} of
//! the pen-offset list for the fourth octant. Since this is an even-numbered
//! octant, $w_0$ is the offset that goes with the fifth octant, and
//! $w_{n+1}$ goes with the third.
//!
//! The elements of the offset list themselves are doubly linked 3-word nodes,
//! containing coordinates in their |x_coord| and |y_coord| fields.
//! The two link fields are called |link| and |knil|; if |w|~points to
//! the node for~$w_k$, then |link(w)| and |knil(w)| point respectively
//! to the nodes for $w\k$ and~$w_{k-1}$. If |h| is the list header,
//! |link(h)| points to the node for~$w_0$ and |knil(link(h))| to the
//! node for~$w_{n+1}$.
//!
//! The tenth word of a pen header node contains the maximum absolute value of
//! an $x$ or $y$ coordinate among all of the unskewed pen offsets.
//!
//! The |link| field of a pen header node should be |null| if and only if
//! the pen is a single point.
//!
//! @d pen_node_size=10
//! @d coord_node_size=3
//! @d max_offset(#)==mem[#+9].sc
//!
//! @ The |print_pen| subroutine illustrates these conventions by
//! reconstructing the vertices of a polygon from \MF's complicated
//! internal offset representation.
//!
//! @<Declare subroutines for printing expressions@>=
//! procedure print_pen(@!p:pointer;@!s:str_number;@!nuline:boolean);
//! var @!nothing_printed:boolean; {has there been any action yet?}
//! @!k:1..8; {octant number}
//! @!h:pointer; {offset list head}
//! @!m,@!n:integer; {offset indices}
//! @!w,@!ww:pointer; {pointers that traverse the offset list}
//! begin print_diagnostic("Pen polygon",s,nuline);
//! nothing_printed:=true; print_ln;
//! for k:=1 to 8 do
//!   begin octant:=octant_code[k]; h:=p+octant; n:=info(h); w:=link(h);
//!   if not odd(k) then w:=knil(w); {in even octants, start at $w_{n+1}$}
//!   for m:=1 to n+1 do
//!     begin if odd(k) then ww:=link(w)@+else ww:=knil(w);
//!     if (x_coord(ww)<>x_coord(w))or(y_coord(ww)<>y_coord(w)) then
//!       @<Print the unskewed and unrotated coordinates of node |ww|@>;
//!     w:=ww;
//!     end;
//!   end;
//! if nothing_printed then
//!   begin w:=link(p+first_octant); print_two(x_coord(w)+y_coord(w),y_coord(w));
//!   end;
//! print_nl(" .. cycle"); end_diagnostic(true);
//! end;
//!
//! @ @<Print the unskewed and unrotated coordinates of node |ww|@>=
//! begin if nothing_printed then nothing_printed:=false
//! else print_nl(" .. ");
//! print_two_true(x_coord(ww),y_coord(ww));
//! end
//!
//! @ A null pen polygon, which has just one vertex $(0,0)$, is
//! predeclared for error recovery. It doesn't need a proper
//! reference count, because the |toss_pen| procedure below
//! will never delete it from memory.
//! @^reference counts@>
//!
//! @<Initialize table entries...@>=
//! ref_count(null_pen):=null; link(null_pen):=null;@/
//! info(null_pen+1):=1; link(null_pen+1):=null_coords;
//! for k:=null_pen+2 to null_pen+8 do mem[k]:=mem[null_pen+1];
//! max_offset(null_pen):=0;@/
//! link(null_coords):=null_coords;
//! knil(null_coords):=null_coords;@/
//! x_coord(null_coords):=0;
//! y_coord(null_coords):=0;
//!
//! @ Here's a trivial subroutine that inserts a copy of an offset
//! on the |link| side of its clone in the doubly linked list.
//!
//! @p procedure dup_offset(@!w:pointer);
//! var @!r:pointer; {the new node}
//! begin r:=get_node(coord_node_size);
//! x_coord(r):=x_coord(w);
//! y_coord(r):=y_coord(w);
//! link(r):=link(w); knil(link(w)):=r;
//! knil(r):=w; link(w):=r;
//! end;
//!
//! @ The following algorithm is somewhat more interesting: It converts a
//! knot list for a cyclic path into a pen polygon, ignoring everything
//! but the |x_coord|, |y_coord|, and |link| fields. If the given path
//! vertices do not define a convex polygon, an error message is issued
//! and the null pen is returned.
//!
//! @p function make_pen(@!h:pointer):pointer;
//! label done,done1,not_found,found;
//! var @!o,@!oo,@!k:small_number; {octant numbers---old, new, and current}
//! @!p:pointer; {top-level node for the new pen}
//! @!q,@!r,@!s,@!w,@!hh:pointer; {for list manipulation}
//! @!n:integer; {offset counter}
//! @!dx,@!dy:scaled; {polygon direction}
//! @!mc:scaled; {the largest coordinate}
//! begin @<Stamp all nodes with an octant code, compute the maximum offset,
//!   and set |hh| to the node that begins the first octant;
//!   |goto not_found| if there's a problem@>;
//! if mc>=fraction_one-half_unit then goto not_found;
//! p:=get_node(pen_node_size); q:=hh; max_offset(p):=mc; ref_count(p):=null;
//! if link(q)<>q then link(p):=null+1;
//! for k:=1 to 8 do @<Construct the offset list for the |k|th octant@>;
//! goto found;
//! not_found:p:=null_pen; @<Complain about a bad pen path@>;
//! found: if internal[tracing_pens]>0 then print_pen(p," (newly created)",true);
//! make_pen:=p;
//! end;
//!
//! @ @<Complain about a bad pen path@>=
//! if mc>=fraction_one-half_unit then
//!   begin print_err("Pen too large");
//! @.Pen too large@>
//!   help2("The cycle you specified has a coordinate of 4095.5 or more.")@/
//!   ("So I've replaced it by the trivial path `(0,0)..cycle'.");@/
//!   end
//! else  begin print_err("Pen cycle must be convex");
//! @.Pen cycle must be convex@>
//!   help3("The cycle you specified either has consecutive equal points")@/
//!     ("or turns right or turns through more than 360 degrees.")@/
//!   ("So I've replaced it by the trivial path `(0,0)..cycle'.");@/
//!   end;
//! put_get_error
//!
//! @ There should be exactly one node whose octant number is less than its
//! predecessor in the cycle; that is node~|hh|.
//!
//! The loop here will terminate in all cases, but the proof is somewhat tricky:
//! If there are at least two distinct $y$~coordinates in the cycle, we will have
//! |o>4| and |o<=4| at different points of the cycle. Otherwise there are
//! at least two distinct $x$~coordinates, and we will have |o>2| somewhere,
//! |o<=2| somewhere.
//!
//! @<Stamp all nodes...@>=
//! q:=h; r:=link(q); mc:=abs(x_coord(h));
//! if q=r then
//!   begin hh:=h; right_type(h):=0; {this trick is explained below}
//!   if mc<abs(y_coord(h)) then mc:=abs(y_coord(h));
//!   end
//! else  begin o:=0; hh:=null;
//!   loop@+  begin s:=link(r);
//!     if mc<abs(x_coord(r)) then mc:=abs(x_coord(r));
//!     if mc<abs(y_coord(r)) then mc:=abs(y_coord(r));
//!     dx:=x_coord(r)-x_coord(q); dy:=y_coord(r)-y_coord(q);
//!     if dx=0 then if dy=0 then goto not_found; {double point}
//!     if ab_vs_cd(dx,y_coord(s)-y_coord(r),dy,x_coord(s)-x_coord(r))<0 then
//!       goto not_found; {right turn}
//!     @<Determine the octant code for direction |(dx,dy)|@>;
//!     right_type(q):=octant; oo:=octant_number[octant];
//!     if o>oo then
//!       begin if hh<>null then goto not_found; {$>360^\circ$}
//!       hh:=q;
//!       end;
//!     o:=oo;
//!     if (q=h)and(hh<>null) then goto done;
//!     q:=r; r:=s;
//!     end;
//!   done:end
//!
//!
//! @ We want the octant for |(-dx,-dy)| to be
//! exactly opposite the octant for |(dx,dy)|.
//!
//! @<Determine the octant code for direction |(dx,dy)|@>=
//! if dx>0 then octant:=first_octant
//! else if dx=0 then
//!   if dy>0 then octant:=first_octant@+else octant:=first_octant+negate_x
//! else  begin negate(dx); octant:=first_octant+negate_x;
//!   end;
//! if dy<0 then
//!   begin negate(dy); octant:=octant+negate_y;
//!   end
//! else if dy=0 then
//!   if octant>first_octant then octant:=first_octant+negate_x+negate_y;
//! if dx<dy then octant:=octant+switch_x_and_y
//!
//! @ Now |q| points to the node that the present octant shares with the previous
//! octant, and |right_type(q)| is the octant code during which |q|~should advance.
//! We have set |right_type(q)=0| in the special case that |q| should never advance
//! (because the pen is degenerate).
//!
//! The number of offsets |n| must be smaller than |max_quarterword|, because
//! the |fill_envelope| routine stores |n+1| in the |right_type| field
//! of a knot node.
//!
//! @<Construct the offset list...@>=
//! begin octant:=octant_code[k]; n:=0; h:=p+octant;
//! loop@+  begin r:=get_node(coord_node_size);
//!   skew(x_coord(q),y_coord(q),octant); x_coord(r):=cur_x; y_coord(r):=cur_y;
//!   if n=0 then link(h):=r
//!   else  @<Link node |r| to the previous node@>;
//!   w:=r;
//!   if right_type(q)<>octant then goto done1;
//!   q:=link(q); incr(n);
//!   end;
//! done1: @<Finish linking the offset nodes, and duplicate the
//!   borderline offset nodes if necessary@>;
//! if n>=max_quarterword then overflow("pen polygon size",max_quarterword);
//! @:METAFONT capacity exceeded pen polygon size}{\quad pen polygon size@>
//! info(h):=n;
//! end
//!
//! @ Now |w| points to the node that was inserted most recently, and
//! |k| is the current octant number.
//!
//! @<Link node |r| to the previous node@>=
//! if odd(k) then
//!   begin link(w):=r; knil(r):=w;
//!   end
//! else  begin knil(w):=r; link(r):=w;
//!   end
//!
//! @ We have inserted |n+1| nodes; it remains to duplicate the nodes at the
//! ends, if slopes 0 and~$\infty$ aren't already represented. At the end of
//! this section the total number of offset nodes should be |n+2|
//! (since we call them $w_0$, $w_1$, \dots,~$w_{n+1}$).
//!
//! @<Finish linking the offset nodes, and duplicate...@>=
//! r:=link(h);
//! if odd(k) then
//!   begin link(w):=r; knil(r):=w;
//!   end
//! else  begin knil(w):=r; link(r):=w; link(h):=w; r:=w;
//!   end;
//! if (y_coord(r)<>y_coord(link(r)))or(n=0) then
//!   begin dup_offset(r); incr(n);
//!   end;
//! r:=knil(r);
//! if x_coord(r)<>x_coord(knil(r)) then dup_offset(r)
//! else decr(n)
//!
//! @ Conversely, |make_path| goes back from a pen to a cyclic path that
//! might have generated it. The structure of this subroutine is essentially
//! the same as |print_pen|.
//!
//! @p @t\4@>@<Declare the function called |trivial_knot|@>@;
//! function make_path(@!pen_head:pointer):pointer;
//! var @!p:pointer; {the most recently copied knot}
//! @!k:1..8; {octant number}
//! @!h:pointer; {offset list head}
//! @!m,@!n:integer; {offset indices}
//! @!w,@!ww:pointer; {pointers that traverse the offset list}
//! begin p:=temp_head;
//! for k:=1 to 8 do
//!   begin octant:=octant_code[k]; h:=pen_head+octant; n:=info(h); w:=link(h);
//!   if not odd(k) then w:=knil(w); {in even octants, start at $w_{n+1}$}
//!   for m:=1 to n+1 do
//!     begin if odd(k) then ww:=link(w)@+else ww:=knil(w);
//!     if (x_coord(ww)<>x_coord(w))or(y_coord(ww)<>y_coord(w)) then
//!       @<Copy the unskewed and unrotated coordinates of node |ww|@>;
//!     w:=ww;
//!     end;
//!   end;
//! if p=temp_head then
//!   begin w:=link(pen_head+first_octant);
//!   p:=trivial_knot(x_coord(w)+y_coord(w),y_coord(w)); link(temp_head):=p;
//!   end;
//! link(p):=link(temp_head); make_path:=link(temp_head);
//! end;
//!
//! @ @<Copy the unskewed and unrotated coordinates of node |ww|@>=
//! begin unskew(x_coord(ww),y_coord(ww),octant);
//! link(p):=trivial_knot(cur_x,cur_y); p:=link(p);
//! end
//!
//! @ @<Declare the function called |trivial_knot|@>=
//! function trivial_knot(@!x,@!y:scaled):pointer;
//! var @!p:pointer; {a new knot for explicit coordinates |x| and |y|}
//! begin p:=get_node(knot_node_size);
//! left_type(p):=explicit; right_type(p):=explicit;@/
//! x_coord(p):=x; left_x(p):=x; right_x(p):=x;@/
//! y_coord(p):=y; left_y(p):=y; right_y(p):=y;@/
//! trivial_knot:=p;
//! end;
//!
//! @ That which can be created can be destroyed.
//!
//! @d add_pen_ref(#)==incr(ref_count(#))
//! @d delete_pen_ref(#)==if ref_count(#)=null then toss_pen(#)
//!   else decr(ref_count(#))
//!
//! @<Declare the recycling subroutines@>=
//! procedure toss_pen(@!p:pointer);
//! var @!k:1..8; {relative header locations}
//! @!w,@!ww:pointer; {pointers to offset nodes}
//! begin if p<>null_pen then
//!   begin for k:=1 to 8 do
//!     begin w:=link(p+k);
//!     repeat ww:=link(w); free_node(w,coord_node_size); w:=ww;
//!     until w=link(p+k);
//!     end;
//!   free_node(p,pen_node_size);
//!   end;
//! end;
//!
//! @ The |find_offset| procedure sets |(cur_x,cur_y)| to the offset associated
//! with a given direction~|(x,y)| and a given pen~|p|. If |x=y=0|, the
//! result is |(0,0)|. If two different offsets apply, one of them is
//! chosen arbitrarily.
//!
//! @p procedure find_offset(@!x,@!y:scaled; @!p:pointer);
//! label done,exit;
//! var @!octant:first_octant..sixth_octant; {octant code for |(x,y)|}
//! @!s:-1..+1; {sign of the octant}
//! @!n:integer; {number of offsets remaining}
//! @!h,@!w,@!ww:pointer; {list traversal registers}
//! begin @<Compute the octant code; skew and rotate the coordinates |(x,y)|@>;
//! if odd(octant_number[octant]) then s:=-1@+else s:=+1;
//! h:=p+octant; w:=link(link(h)); ww:=link(w); n:=info(h);
//! while n>1 do
//!   begin if ab_vs_cd(x,y_coord(ww)-y_coord(w),@|
//!     y,x_coord(ww)-x_coord(w))<>s then goto done;
//!   w:=ww; ww:=link(w); decr(n);
//!   end;
//! done:unskew(x_coord(w),y_coord(w),octant);
//! exit:end;
//!
//! @ @<Compute the octant code; skew and rotate the coordinates |(x,y)|@>=
//! if x>0 then octant:=first_octant
//! else if x=0 then
//!   if y<=0 then
//!     if y=0 then
//!       begin cur_x:=0; cur_y:=0; return;
//!       end
//!     else octant:=first_octant+negate_x
//!   else octant:=first_octant
//! else  begin x:=-x;
//!   if y=0 then octant:=first_octant+negate_x+negate_y
//!   else octant:=first_octant+negate_x;
//!   end;
//! if y<0 then
//!   begin octant:=octant+negate_y; y:=-y;
//!   end;
//! if x>=y then x:=x-y
//! else  begin octant:=octant+switch_x_and_y; x:=y-x; y:=y-x;
//!   end
//!
//! @* \[24] Filling an envelope.
//! We are about to reach the culmination of \MF's digital plotting routines:
//! Almost all of the previous algorithms will be brought to bear on \MF's
//! most difficult task, which is to fill the envelope of a given cyclic path
//! with respect to a given pen polygon.
//!
//! But we still must complete some of the preparatory work before taking such
//! a big plunge.
//!
//! @ Given a pointer |c| to a nonempty list of cubics,
//! and a pointer~|h| to the header information of a pen polygon segment,
//! the |offset_prep| routine changes the list into cubics that are
//! associated with particular pen offsets. Namely, the cubic between |p|
//! and~|q| should be associated with the |k|th offset when |right_type(p)=k|.
//!
//! List |c| is actually part of a cycle spec, so it terminates at the
//! first node whose |right_type| is |endpoint|. The cubics all have
//! monotone-nondecreasing $x(t)$ and $y(t)$.
//!
//! @p @t\4@>@<Declare subroutines needed by |offset_prep|@>@;
//! procedure offset_prep(@!c,@!h:pointer);
//! label done,not_found;
//! var @!n:halfword; {the number of pen offsets}
//! @!p,@!q,@!r,@!lh,@!ww:pointer; {for list manipulation}
//! @!k:halfword; {the current offset index}
//! @!w:pointer; {a pointer to offset $w_k$}
//! @<Other local variables for |offset_prep|@>@;
//! begin p:=c; n:=info(h); lh:=link(h); {now |lh| points to $w_0$}
//! while right_type(p)<>endpoint do
//!   begin q:=link(p);
//!   @<Split the cubic between |p| and |q|, if necessary, into cubics
//!     associated with single offsets, after which |q| should
//!     point to the end of the final such cubic@>;
//!   @<Advance |p| to node |q|, removing any ``dead'' cubics that
//!     might have been introduced by the splitting process@>;
//!   end;
//! end;
//!
//! @ @<Advance |p| to node |q|, removing any ``dead'' cubics...@>=
//! repeat r:=link(p);
//! if x_coord(p)=right_x(p) then if y_coord(p)=right_y(p) then
//!  if x_coord(p)=left_x(r) then if y_coord(p)=left_y(r) then
//!   if x_coord(p)=x_coord(r) then if y_coord(p)=y_coord(r) then
//!   begin remove_cubic(p);
//!   if r=q then q:=p;
//!   r:=p;
//!   end;
//! p:=r;
//! until p=q
//!
//! @ The splitting process uses a subroutine like |split_cubic|, but
//! (for ``bulletproof'' operation) we check to make sure that the
//! resulting (skewed) coordinates satisfy $\Delta x\G0$ and $\Delta y\G0$
//! after splitting; |make_spec| has made sure that these relations hold
//! before splitting. (This precaution is surely unnecessary, now that
//! |make_spec| is so much more careful than it used to be. But who
//! wants to take a chance? Maybe the hardware will fail or something.)
//!
//! @<Declare subroutines needed by |offset_prep|@>=
//! procedure split_for_offset(@!p:pointer;@!t:fraction);
//! var @!q:pointer; {the successor of |p|}
//! @!r:pointer; {the new node}
//! begin q:=link(p); split_cubic(p,t,x_coord(q),y_coord(q)); r:=link(p);
//! if y_coord(r)<y_coord(p) then y_coord(r):=y_coord(p)
//! else if y_coord(r)>y_coord(q) then y_coord(r):=y_coord(q);
//! if x_coord(r)<x_coord(p) then x_coord(r):=x_coord(p)
//! else if x_coord(r)>x_coord(q) then x_coord(r):=x_coord(q);
//! end;
//!
//! @ If the pen polygon has |n| offsets, and if $w_k=(u_k,v_k)$ is the $k$th
//! of these, the $k$th pen slope is defined by the formula
//! $$s_k={v\k-v_k\over u\k-u_k},\qquad\hbox{for $0<k<n$}.$$
//! In odd-numbered octants, the numerator and denominator of this fraction
//! will be nonnegative; in even-numbered octants they will both be nonpositive.
//! Furthermore we always have $0=s_0\le s_1\le\cdots\le s_n=\infty$. The goal of
//! |offset_prep| is to find an offset index~|k| to associate with
//! each cubic, such that the slope $s(t)$ of the cubic satisfies
//! $$s_{k-1}\le s(t)\le s_k\qquad\hbox{for $0\le t\le 1$.}\eqno(*)$$
//! We may have to split a cubic into as many as $2n-1$ pieces before each
//! piece corresponds to a unique offset.
//!
//! @<Split the cubic between |p| and |q|, if necessary, into cubics...@>=
//! if n<=1 then right_type(p):=1 {this case is easy}
//! else  begin @<Prepare for derivative computations;
//!     |goto not_found| if the current cubic is dead@>;
//!   @<Find the initial slope, |dy/dx|@>;
//!   if dx=0 then @<Handle the special case of infinite slope@>
//!   else  begin @<Find the index |k| such that $s_{k-1}\L\\{dy}/\\{dx}<s_k$@>;
//!     @<Complete the offset splitting process@>;
//!     end;
//! not_found: end
//!
//! @ The slope of a cubic $B(z_0,z_1,z_2,z_3;t)=\bigl(x(t),y(t)\bigr)$ can be
//! calculated from the quadratic polynomials
//! ${1\over3}x'(t)=B(x_1-x_0,x_2-x_1,x_3-x_2;t)$ and
//! ${1\over3}y'(t)=B(y_1-y_0,y_2-y_1,y_3-y_2;t)$.
//! Since we may be calculating slopes from several cubics
//! split from the current one, it is desirable to do these calculations
//! without losing too much precision. ``Scaled up'' values of the
//! derivatives, which will be less tainted by accumulated errors than
//! derivatives found from the cubics themselves, are maintained in
//! local variables |x0|, |x1|, and |x2|, representing $X_0=2^l(x_1-x_0)$,
//! $X_1=2^l(x_2-x_1)$, and $X_2=2^l(x_3-x_2)$; similarly |y0|, |y1|, and~|y2|
//! represent $Y_0=2^l(y_1-y_0)$, $Y_1=2^l(y_2-y_1)$, and $Y_2=2^l(y_3-y_2)$.
//! To test whether the slope of the cubic is $\ge s$ or $\le s$, we will test
//! the sign of the quadratic ${1\over3}2^l\bigl(y'(t)-sx'(t)\bigr)$ if $s\le1$,
//! or ${1\over3}2^l\bigl(y'(t)/s-x'(t)\bigr)$ if $s>1$.
//!
//! @<Other local variables for |offset_prep|@>=
//! @!x0,@!x1,@!x2,@!y0,@!y1,@!y2:integer; {representatives of derivatives}
//! @!t0,@!t1,@!t2:integer; {coefficients of polynomial for slope testing}
//! @!du,@!dv,@!dx,@!dy:integer; {for slopes of the pen and the curve}
//! @!max_coef:integer; {used while scaling}
//! @!x0a,@!x1a,@!x2a,@!y0a,@!y1a,@!y2a:integer; {intermediate values}
//! @!t:fraction; {where the derivative passes through zero}
//! @!s:fraction; {slope or reciprocal slope}
//!
//! @ @<Prepare for derivative computations...@>=
//! x0:=right_x(p)-x_coord(p); {should be |>=0|}
//! x2:=x_coord(q)-left_x(q); {likewise}
//! x1:=left_x(q)-right_x(p); {but this might be negative}
//! y0:=right_y(p)-y_coord(p); y2:=y_coord(q)-left_y(q);
//! y1:=left_y(q)-right_y(p);
//! max_coef:=abs(x0); {we take |abs| just to make sure}
//! if abs(x1)>max_coef then max_coef:=abs(x1);
//! if abs(x2)>max_coef then max_coef:=abs(x2);
//! if abs(y0)>max_coef then max_coef:=abs(y0);
//! if abs(y1)>max_coef then max_coef:=abs(y1);
//! if abs(y2)>max_coef then max_coef:=abs(y2);
//! if max_coef=0 then goto not_found;
//! while max_coef<fraction_half do
//!   begin double(max_coef);
//!   double(x0); double(x1); double(x2);
//!   double(y0); double(y1); double(y2);
//!   end
//!
//! @ Let us first solve a special case of the problem: Suppose we
//! know an index~$k$ such that either (i)~$s(t)\G s_{k-1}$ for all~$t$
//! and $s(0)<s_k$, or (ii)~$s(t)\L s_k$ for all~$t$ and $s(0)>s_{k-1}$.
//! Then, in a sense, we're halfway done, since one of the two inequalities
//! in $(*)$ is satisfied, and the other couldn't be satisfied for
//! any other value of~|k|.
//!
//! The |fin_offset_prep| subroutine solves the stated subproblem.
//! It has a boolean parameter called |rising| that is |true| in
//! case~(i), |false| in case~(ii). When |rising=false|, parameters
//! |x0| through |y2| represent the negative of the derivative of
//! the cubic following |p|; otherwise they represent the actual derivative.
//! The |w| parameter should point to offset~$w_k$.
//!
//! @<Declare subroutines needed by |offset_prep|@>=
//! procedure fin_offset_prep(@!p:pointer;@!k:halfword;@!w:pointer;
//!   @!x0,@!x1,@!x2,@!y0,@!y1,@!y2:integer;@!rising:boolean;@!n:integer);
//! label exit;
//! var @!ww:pointer; {for list manipulation}
//! @!du,@!dv:scaled; {for slope calculation}
//! @!t0,@!t1,@!t2:integer; {test coefficients}
//! @!t:fraction; {place where the derivative passes a critical slope}
//! @!s:fraction; {slope or reciprocal slope}
//! @!v:integer; {intermediate value for updating |x0..y2|}
//! begin loop
//!   begin right_type(p):=k;
//!   if rising then
//!     if k=n then return
//!     else ww:=link(w) {a pointer to $w\k$}
//!   else  if k=1 then return
//!     else ww:=knil(w); {a pointer to $w_{k-1}$}
//!   @<Compute test coefficients |(t0,t1,t2)|
//!     for $s(t)$ versus $s_k$ or $s_{k-1}$@>;
//!   t:=crossing_point(t0,t1,t2);
//!   if t>=fraction_one then return;
//!   @<Split the cubic at $t$,
//!     and split off another cubic if the derivative crosses back@>;
//!   if rising then incr(k)@+else decr(k);
//!   w:=ww;
//!   end;
//! exit:end;
//!
//! @ @<Compute test coefficients |(t0,t1,t2)| for $s(t)$ versus...@>=
//! du:=x_coord(ww)-x_coord(w); dv:=y_coord(ww)-y_coord(w);
//! if abs(du)>=abs(dv) then {$s_{k-1}\le1$ or $s_k\le1$}
//!   begin s:=make_fraction(dv,du);
//!   t0:=take_fraction(x0,s)-y0;
//!   t1:=take_fraction(x1,s)-y1;
//!   t2:=take_fraction(x2,s)-y2;
//!   end
//! else  begin s:=make_fraction(du,dv);
//!   t0:=x0-take_fraction(y0,s);
//!   t1:=x1-take_fraction(y1,s);
//!   t2:=x2-take_fraction(y2,s);
//!   end
//!
//! @ The curve has crossed $s_k$ or $s_{k-1}$; its initial segment satisfies
//! $(*)$, and it might cross again and return towards $s_{k-1}$ or $s_k$,
//! respectively, yielding another solution of $(*)$.
//!
//! @<Split the cubic at $t$, and split off another...@>=
//! begin split_for_offset(p,t); right_type(p):=k; p:=link(p);@/
//! v:=t_of_the_way(x0)(x1); x1:=t_of_the_way(x1)(x2);
//! x0:=t_of_the_way(v)(x1);@/
//! v:=t_of_the_way(y0)(y1); y1:=t_of_the_way(y1)(y2);
//! y0:=t_of_the_way(v)(y1);@/
//! t1:=t_of_the_way(t1)(t2);
//! if t1>0 then t1:=0; {without rounding error, |t1| would be |<=0|}
//! t:=crossing_point(0,-t1,-t2);
//! if t<fraction_one then
//!   begin split_for_offset(p,t); right_type(link(p)):=k;@/
//!   v:=t_of_the_way(x1)(x2); x1:=t_of_the_way(x0)(x1);
//!   x2:=t_of_the_way(x1)(v);@/
//!   v:=t_of_the_way(y1)(y2); y1:=t_of_the_way(y0)(y1);
//!   y2:=t_of_the_way(y1)(v);
//!   end;
//! end
//!
//! @ Now we must consider the general problem of |offset_prep|, when
//! nothing is known about a given cubic. We start by finding its
//! slope $s(0)$ in the vicinity of |t=0|.
//!
//! If $z'(t)=0$, the given cubic is numerically unstable, since the
//! slope direction is probably being influenced primarily by rounding
//! errors. A user who specifies such cuspy curves should expect to generate
//! rather wild results. The present code tries its best to believe the
//! existing data, as if no rounding errors were present.
//!
//! @ @<Find the initial slope, |dy/dx|@>=
//! dx:=x0; dy:=y0;
//! if dx=0 then if dy=0 then
//!   begin dx:=x1; dy:=y1;
//!   if dx=0 then if dy=0 then
//!     begin dx:=x2; dy:=y2;
//!     end;
//!   end
//!
//! @ The next step is to bracket the initial slope between consecutive
//! slopes of the pen polygon. The most important invariant relation in the
//! following loop is that |dy/dx>=@t$s_{k-1}$@>|.
//!
//! @<Find the index |k| such that $s_{k-1}\L\\{dy}/\\{dx}<s_k$@>=
//! k:=1; w:=link(lh);
//! loop@+  begin if k=n then goto done;
//!   ww:=link(w);
//!   if ab_vs_cd(dy,abs(x_coord(ww)-x_coord(w)),@|
//!    dx,abs(y_coord(ww)-y_coord(w)))>=0 then
//!     begin incr(k); w:=ww;
//!     end
//!   else goto done;
//!   end;
//! done:
//!
//! @ Finally we want to reduce the general problem to situations that
//! |fin_offset_prep| can handle. If |k=1|, we already are in the desired
//! situation. Otherwise we can split the cubic into at most three parts
//! with respect to $s_{k-1}$, and apply |fin_offset_prep| to each part.
//!
//! @<Complete the offset splitting process@>=
//! if k=1 then t:=fraction_one+1
//! else  begin ww:=knil(w); @<Compute test coeff...@>;
//!   t:=crossing_point(-t0,-t1,-t2);
//!   end;
//! if t>=fraction_one then fin_offset_prep(p,k,w,x0,x1,x2,y0,y1,y2,true,n)
//! else  begin split_for_offset(p,t); r:=link(p);@/
//!   x1a:=t_of_the_way(x0)(x1); x1:=t_of_the_way(x1)(x2);
//!   x2a:=t_of_the_way(x1a)(x1);@/
//!   y1a:=t_of_the_way(y0)(y1); y1:=t_of_the_way(y1)(y2);
//!   y2a:=t_of_the_way(y1a)(y1);@/
//!   fin_offset_prep(p,k,w,x0,x1a,x2a,y0,y1a,y2a,true,n); x0:=x2a; y0:=y2a;
//!   t1:=t_of_the_way(t1)(t2);
//!   if t1<0 then t1:=0;
//!   t:=crossing_point(0,t1,t2);
//!   if t<fraction_one then
//!     @<Split off another |rising| cubic for |fin_offset_prep|@>;
//!   fin_offset_prep(r,k-1,ww,-x0,-x1,-x2,-y0,-y1,-y2,false,n);
//!   end
//!
//! @ @<Split off another |rising| cubic for |fin_offset_prep|@>=
//! begin split_for_offset(r,t);@/
//! x1a:=t_of_the_way(x1)(x2); x1:=t_of_the_way(x0)(x1);
//! x0a:=t_of_the_way(x1)(x1a);@/
//! y1a:=t_of_the_way(y1)(y2); y1:=t_of_the_way(y0)(y1);
//! y0a:=t_of_the_way(y1)(y1a);@/
//! fin_offset_prep(link(r),k,w,x0a,x1a,x2,y0a,y1a,y2,true,n);
//! x2:=x0a; y2:=y0a;
//! end
//!
//! @ @<Handle the special case of infinite slope@>=
//! fin_offset_prep(p,n,knil(knil(lh)),-x0,-x1,-x2,-y0,-y1,-y2,false,n)
//!
//! @ OK, it's time now for the biggie. The |fill_envelope| routine generalizes
//! |fill_spec| to polygonal envelopes. Its outer structure is essentially the
//! same as before, except that octants with no cubics do contribute to
//! the envelope.
//!
//! @p @t\4@>@<Declare the procedure called |skew_line_edges|@>@;
//! @t\4@>@<Declare the procedure called |dual_moves|@>@;
//! procedure fill_envelope(@!spec_head:pointer);
//! label done, done1;
//! var @!p,@!q,@!r,@!s:pointer; {for list traversal}
//! @!h:pointer; {head of pen offset list for current octant}
//! @!www:pointer; {a pen offset of temporary interest}
//! @<Other local variables for |fill_envelope|@>@;
//! begin if internal[tracing_edges]>0 then begin_edge_tracing;
//! p:=spec_head; {we assume that |left_type(spec_head)=endpoint|}
//! repeat octant:=left_octant(p); h:=cur_pen+octant;
//! @<Set variable |q| to the node at the end of the current octant@>;
//! @<Determine the envelope's starting and ending
//!     lattice points |(m0,n0)| and |(m1,n1)|@>;
//! offset_prep(p,h); {this may clobber node~|q|, if it becomes ``dead''}
//! @<Set variable |q| to the node at the end of the current octant@>;
//! @<Make the envelope moves for the current octant and insert them
//!   in the pixel data@>;
//! p:=link(q);
//! until p=spec_head;
//! if internal[tracing_edges]>0 then end_edge_tracing;
//! toss_knot_list(spec_head);
//! end;
//!
//! @ In even-numbered octants we have reflected the coordinates an odd number
//! of times, hence clockwise and counterclockwise are reversed; this means that
//! the envelope is being formed in a ``dual'' manner. For the time being, let's
//! concentrate on odd-numbered octants, since they're easier to understand.
//! After we have coded the program for odd-numbered octants, the changes needed
//! to dualize it will not be so mysterious.
//!
//! It is convenient to assume that we enter an odd-numbered octant with
//! an |axis| transition (where the skewed slope is zero) and leave at a
//! |diagonal| one (where the skewed slope is infinite). Then all of the
//! offset points $z(t)+w(t)$ will lie in a rectangle whose lower left and
//! upper right corners are the initial and final offset points. If this
//! assumption doesn't hold we can implicitly change the curve so that it does.
//! For example, if the entering transition is diagonal, we can draw a
//! straight line from $z_0+w_{n+1}$ to $z_0+w_0$ and continue as if the
//! curve were moving rightward. The effect of this on the envelope is simply
//! to ``doubly color'' the region enveloped by a section of the pen that
//! goes from $w_0$ to $w_1$ to $\cdots$ to $w_{n+1}$ to~$w_0$. The additional
//! straight line at the beginning (and a similar one at the end, where it
//! may be necessary to go from $z_1+w_{n+1}$ to $z_1+w_0$) can be drawn by
//! the |line_edges| routine; we are thereby saved from the embarrassment that
//! these lines travel backwards from the current octant direction.
//!
//! Once we have established the assumption that the curve goes from
//! $z_0+w_0$ to $z_1+w_{n+1}$, any further retrograde moves that might
//! occur within the octant can be essentially ignored; we merely need to
//! keep track of the rightmost edge in each row, in order to compute
//! the envelope.
//!
//! Envelope moves consist of offset cubics intermixed with straight line
//! segments. We record them in a separate |env_move| array, which is
//! something like |move| but it keeps track of the rightmost position of the
//! envelope in each row.
//!
//! @<Glob...@>=
//! @!env_move:array[0..move_size] of integer;
//!
//! @ @<Determine the envelope's starting and ending...@>=
//! w:=link(h);@+if left_transition(p)=diagonal then w:=knil(w);
//! @!stat if internal[tracing_edges]>unity then
//!   @<Print a line of diagnostic info to introduce this octant@>;
//! tats@;@/
//! ww:=link(h); www:=ww; {starting and ending offsets}
//! if odd(octant_number[octant]) then www:=knil(www)@+else ww:=knil(ww);
//! if w<>ww then skew_line_edges(p,w,ww);
//! end_round(x_coord(p)+x_coord(ww),y_coord(p)+y_coord(ww));
//! m0:=m1; n0:=n1; d0:=d1;@/
//! end_round(x_coord(q)+x_coord(www),y_coord(q)+y_coord(www));
//! if n1-n0>=move_size then overflow("move table size",move_size)
//! @:METAFONT capacity exceeded move table size}{\quad move table size@>
//!
//! @ @<Print a line of diagnostic info to introduce this octant@>=
//! begin print_nl("@@ Octant "); print(octant_dir[octant]);
//! @:]]]\AT!_Octant}{\.{\AT! Octant...}@>
//! print(" ("); print_int(info(h)); print(" offset");
//! if info(h)<>1 then print_char("s");
//! print("), from ");
//! print_two_true(x_coord(p)+x_coord(w),y_coord(p)+y_coord(w));@/
//! ww:=link(h);@+if right_transition(q)=diagonal then ww:=knil(ww);
//! print(" to ");
//! print_two_true(x_coord(q)+x_coord(ww),y_coord(q)+y_coord(ww));
//! end
//!
//! @ A slight variation of the |line_edges| procedure comes in handy
//! when we must draw the retrograde lines for nonstandard entry and exit
//! conditions.
//!
//! @<Declare the procedure called |skew_line_edges|@>=
//! procedure skew_line_edges(@!p,@!w,@!ww:pointer);
//! var @!x0,@!y0,@!x1,@!y1:scaled; {from and to}
//! begin if (x_coord(w)<>x_coord(ww))or(y_coord(w)<>y_coord(ww)) then
//!   begin x0:=x_coord(p)+x_coord(w); y0:=y_coord(p)+y_coord(w);@/
//!   x1:=x_coord(p)+x_coord(ww); y1:=y_coord(p)+y_coord(ww);@/
//!   unskew(x0,y0,octant); {unskew and unrotate the coordinates}
//!   x0:=cur_x; y0:=cur_y;@/
//!   unskew(x1,y1,octant);@/
//!   @!stat if internal[tracing_edges]>unity then
//!     begin print_nl("@@ retrograde line from ");
//! @:]]]\AT!_retro_}{\.{\AT! retrograde line...}@>
//!   @.retrograde line...@>
//!     print_two(x0,y0); print(" to "); print_two(cur_x,cur_y); print_nl("");
//!     end;@+tats@;@/
//!   line_edges(x0,y0,cur_x,cur_y); {then draw a straight line}
//!   end;
//! end;
//!
//! @ The envelope calculations require more local variables than we needed
//! in the simpler case of |fill_spec|. At critical points in the computation,
//! |w| will point to offset $w_k$; |m| and |n| will record the current
//! lattice positions.  The values of |move_ptr| after the initial and before
//! the final offset adjustments are stored in |smooth_bot| and |smooth_top|,
//! respectively.
//!
//! @<Other local variables for |fill_envelope|@>=
//! @!m,@!n:integer; {current lattice position}
//! @!mm0,@!mm1:integer; {skewed equivalents of |m0| and |m1|}
//! @!k:integer; {current offset number}
//! @!w,@!ww:pointer; {pointers to the current offset and its neighbor}
//! @!smooth_bot,@!smooth_top:0..move_size; {boundaries of smoothing}
//! @!xx,@!yy,@!xp,@!yp,@!delx,@!dely,@!tx,@!ty:scaled;
//!   {registers for coordinate calculations}
//!
//! @ @<Make the envelope moves for the current octant...@>=
//! if odd(octant_number[octant]) then
//!   begin @<Initialize for ordinary envelope moves@>;
//!   r:=p; right_type(q):=info(h)+1;
//!   loop@+  begin if r=q then smooth_top:=move_ptr;
//!     while right_type(r)<>k do
//!       @<Insert a line segment to approach the correct offset@>;
//!     if r=p then smooth_bot:=move_ptr;
//!     if r=q then goto done;
//!     move[move_ptr]:=1; n:=move_ptr; s:=link(r);@/
//!     make_moves(x_coord(r)+x_coord(w),right_x(r)+x_coord(w),
//!       left_x(s)+x_coord(w),x_coord(s)+x_coord(w),@|
//!       y_coord(r)+y_coord(w)+half_unit,right_y(r)+y_coord(w)+half_unit,
//!       left_y(s)+y_coord(w)+half_unit,y_coord(s)+y_coord(w)+half_unit,@|
//!       xy_corr[octant],y_corr[octant]);@/
//!     @<Transfer moves from the |move| array to |env_move|@>;
//!     r:=s;
//!     end;
//! done:  @<Insert the new envelope moves in the pixel data@>;
//!   end
//! else dual_moves(h,p,q);
//! right_type(q):=endpoint
//!
//! @ @<Initialize for ordinary envelope moves@>=
//! k:=0; w:=link(h); ww:=knil(w);
//! mm0:=floor_unscaled(x_coord(p)+x_coord(w)-xy_corr[octant]);
//! mm1:=floor_unscaled(x_coord(q)+x_coord(ww)-xy_corr[octant]);
//! for n:=0 to n1-n0-1 do env_move[n]:=mm0;
//! env_move[n1-n0]:=mm1; move_ptr:=0; m:=mm0
//!
//! @ At this point |n| holds the value of |move_ptr| that was current
//! when |make_moves| began to record its moves.
//!
//! @<Transfer moves from the |move| array to |env_move|@>=
//! repeat m:=m+move[n]-1;
//! if m>env_move[n] then env_move[n]:=m;
//! incr(n);
//! until n>move_ptr
//!
//! @ Retrograde lines (when |k| decreases) do not need to be recorded in
//! |env_move| because their edges are not the furthest right in any row.
//!
//! @<Insert a line segment to approach the correct offset@>=
//! begin xx:=x_coord(r)+x_coord(w); yy:=y_coord(r)+y_coord(w)+half_unit;
//! @!stat if internal[tracing_edges]>unity then
//!   begin print_nl("@@ transition line "); print_int(k); print(", from ");
//! @:]]]\AT!_trans_}{\.{\AT! transition line...}@>
//! @.transition line...@>
//!   print_two_true(xx,yy-half_unit);
//!   end;@+tats@;@/
//! if right_type(r)>k then
//!   begin incr(k); w:=link(w);
//!   xp:=x_coord(r)+x_coord(w); yp:=y_coord(r)+y_coord(w)+half_unit;
//!   if yp<>yy then
//!     @<Record a line segment from |(xx,yy)| to |(xp,yp)| in |env_move|@>;
//!   end
//! else  begin decr(k); w:=knil(w);
//!   xp:=x_coord(r)+x_coord(w); yp:=y_coord(r)+y_coord(w)+half_unit;
//!   end;
//! stat if internal[tracing_edges]>unity then
//!   begin print(" to ");
//!   print_two_true(xp,yp-half_unit);
//!   print_nl("");
//!   end;@+tats@;@/
//! m:=floor_unscaled(xp-xy_corr[octant]);
//! move_ptr:=floor_unscaled(yp-y_corr[octant])-n0;
//! if m>env_move[move_ptr] then env_move[move_ptr]:=m;
//! end
//!
//! @ In this step we have |xp>=xx| and |yp>=yy|.
//!
//! @<Record a line segment from |(xx,yy)| to |(xp,yp)| in |env_move|@>=
//! begin ty:=floor_scaled(yy-y_corr[octant]); dely:=yp-yy; yy:=yy-ty;
//! ty:=yp-y_corr[octant]-ty;
//! if ty>=unity then
//!   begin delx:=xp-xx; yy:=unity-yy;
//!   loop@+  begin tx:=take_fraction(delx,make_fraction(yy,dely));
//!     if ab_vs_cd(tx,dely,delx,yy)+xy_corr[octant]>0 then decr(tx);
//!     m:=floor_unscaled(xx+tx);
//!     if m>env_move[move_ptr] then env_move[move_ptr]:=m;
//!     ty:=ty-unity;
//!     if ty<unity then goto done1;
//!     yy:=yy+unity; incr(move_ptr);
//!     end;
//!   done1:end;
//! end
//!
//! @ @<Insert the new envelope moves in the pixel data@>=
//! debug if (m<>mm1)or(move_ptr<>n1-n0) then confusion("1");@+gubed@;@/
//! @:this can't happen /}{\quad 1@>
//! move[0]:=d0+env_move[0]-mm0;
//! for n:=1 to move_ptr do
//!   move[n]:=env_move[n]-env_move[n-1]+1;
//! move[move_ptr]:=move[move_ptr]-d1;
//! if internal[smoothing]>0 then smooth_moves(smooth_bot,smooth_top);
//! move_to_edges(m0,n0,m1,n1);
//! if right_transition(q)=axis then
//!   begin w:=link(h); skew_line_edges(q,knil(w),w);
//!   end
//!
//! @ We've done it all in the odd-octant case; the only thing remaining
//! is to repeat the same ideas, upside down and/or backwards.
//!
//! The following code has been split off as a subprocedure of |fill_envelope|,
//! because some \PASCAL\ compilers cannot handle procedures as large as
//! |fill_envelope| would otherwise be.
//!
//! @<Declare the procedure called |dual_moves|@>=
//! procedure dual_moves(@!h,@!p,@!q:pointer);
//! label done,done1;
//! var @!r,@!s:pointer; {for list traversal}
//! @<Other local variables for |fill_envelope|@>@;
//! begin @<Initialize for dual envelope moves@>;
//! r:=p; {recall that |right_type(q)=endpoint=0| now}
//! loop@+  begin if r=q then smooth_top:=move_ptr;
//!   while right_type(r)<>k do
//!     @<Insert a line segment dually to approach the correct offset@>;
//!   if r=p then smooth_bot:=move_ptr;
//!   if r=q then goto done;
//!   move[move_ptr]:=1; n:=move_ptr; s:=link(r);@/
//!   make_moves(x_coord(r)+x_coord(w),right_x(r)+x_coord(w),
//!     left_x(s)+x_coord(w),x_coord(s)+x_coord(w),@|
//!     y_coord(r)+y_coord(w)+half_unit,right_y(r)+y_coord(w)+half_unit,
//!     left_y(s)+y_coord(w)+half_unit,y_coord(s)+y_coord(w)+half_unit,@|
//!     xy_corr[octant],y_corr[octant]);
//!   @<Transfer moves dually from the |move| array to |env_move|@>;
//!   r:=s;
//!   end;
//! done:@<Insert the new envelope moves dually in the pixel data@>;
//! end;
//!
//! @ In the dual case the normal situation is to arrive with a |diagonal|
//! transition and to leave at the |axis|. The leftmost edge in each row
//! is relevant instead of the rightmost one.
//!
//! @<Initialize for dual envelope moves@>=
//! k:=info(h)+1; ww:=link(h); w:=knil(ww);@/
//! mm0:=floor_unscaled(x_coord(p)+x_coord(w)-xy_corr[octant]);
//! mm1:=floor_unscaled(x_coord(q)+x_coord(ww)-xy_corr[octant]);
//! for n:=1 to n1-n0+1 do env_move[n]:=mm1;
//! env_move[0]:=mm0; move_ptr:=0; m:=mm0
//!
//! @ @<Transfer moves dually from the |move| array to |env_move|@>=
//! repeat if m<env_move[n] then env_move[n]:=m;
//! m:=m+move[n]-1;
//! incr(n);
//! until n>move_ptr
//!
//! @ Dual retrograde lines occur when |k| increases; the edges of such lines
//! are not the furthest left in any row.
//!
//! @<Insert a line segment dually to approach the correct offset@>=
//! begin xx:=x_coord(r)+x_coord(w); yy:=y_coord(r)+y_coord(w)+half_unit;
//! @!stat if internal[tracing_edges]>unity then
//!   begin print_nl("@@ transition line "); print_int(k); print(", from ");
//! @:]]]\AT!_trans_}{\.{\AT! transition line...}@>
//! @.transition line...@>
//!   print_two_true(xx,yy-half_unit);
//!   end;@+tats@;@/
//! if right_type(r)<k then
//!   begin decr(k); w:=knil(w);
//!   xp:=x_coord(r)+x_coord(w); yp:=y_coord(r)+y_coord(w)+half_unit;
//!   if yp<>yy then
//!     @<Record a line segment from |(xx,yy)| to |(xp,yp)| dually in |env_move|@>;
//!   end
//! else  begin incr(k); w:=link(w);
//!   xp:=x_coord(r)+x_coord(w); yp:=y_coord(r)+y_coord(w)+half_unit;
//!   end;
//! stat if internal[tracing_edges]>unity then
//!   begin print(" to ");
//!   print_two_true(xp,yp-half_unit);
//!   print_nl("");
//!   end;@+tats@;@/
//! m:=floor_unscaled(xp-xy_corr[octant]);
//! move_ptr:=floor_unscaled(yp-y_corr[octant])-n0;
//! if m<env_move[move_ptr] then env_move[move_ptr]:=m;
//! end
//!
//! @ Again, |xp>=xx| and |yp>=yy|; but this time we are interested in the {\sl
//! smallest\/} |m| that belongs to a given |move_ptr| position, instead of
//! the largest~|m|.
//!
//! @<Record a line segment from |(xx,yy)| to |(xp,yp)| dually in |env_move|@>=
//! begin ty:=floor_scaled(yy-y_corr[octant]); dely:=yp-yy; yy:=yy-ty;
//! ty:=yp-y_corr[octant]-ty;
//! if ty>=unity then
//!   begin delx:=xp-xx; yy:=unity-yy;
//!   loop@+  begin if m<env_move[move_ptr] then env_move[move_ptr]:=m;
//!     tx:=take_fraction(delx,make_fraction(yy,dely));
//!     if ab_vs_cd(tx,dely,delx,yy)+xy_corr[octant]>0 then decr(tx);
//!     m:=floor_unscaled(xx+tx);
//!     ty:=ty-unity; incr(move_ptr);
//!     if ty<unity then goto done1;
//!     yy:=yy+unity;
//!     end;
//! done1:  if m<env_move[move_ptr] then env_move[move_ptr]:=m;
//!   end;
//! end
//!
//! @ Since |env_move| contains minimum values instead of maximum values, the
//! finishing-up process is slightly different in the dual case.
//!
//! @<Insert the new envelope moves dually in the pixel data@>=
//! debug if (m<>mm1)or(move_ptr<>n1-n0) then confusion("2");@+gubed@;@/
//! @:this can't happen /}{\quad 2@>
//! move[0]:=d0+env_move[1]-mm0;
//! for n:=1 to move_ptr do
//!   move[n]:=env_move[n+1]-env_move[n]+1;
//! move[move_ptr]:=move[move_ptr]-d1;
//! if internal[smoothing]>0 then smooth_moves(smooth_bot,smooth_top);
//! move_to_edges(m0,n0,m1,n1);
//! if right_transition(q)=diagonal then
//!   begin w:=link(h); skew_line_edges(q,w,knil(w));
//!   end
//!
//! @* \[25] Elliptical pens.
//! To get the envelope of a cyclic path with respect to an ellipse, \MF\
//! calculates the envelope with respect to a polygonal approximation to
//! the ellipse, using an approach due to John Hobby (Ph.D. thesis,
//! Stanford University, 1985).
//! @^Hobby, John Douglas@>
//! This has two important advantages over trying to obtain the ``exact''
//! envelope:
//!
//! \yskip\textindent{1)}It gives better results, because the polygon has been
//! designed to counteract problems that arise from digitization; the
//! polygon includes sub-pixel corrections to an exact ellipse that make
//! the results essentially independent of where the path falls on the raster.
//! For example, the exact envelope with respect to a pen of diameter~1
//! blackens a pixel if and only if the path intersects a circle of diameter~1
//! inscribed in that pixel; the resulting pattern has ``blots'' when the path
//! is traveling diagonally in unfortunate raster positions. A much better
//! result is obtained when pixels are blackened only when the path intersects
//! an inscribed {\sl diamond\/} of diameter~1. Such a diamond is precisely
//! the polygon that \MF\ uses in the special case of a circle whose diameter is~1.
//!
//! \yskip\textindent{2)}Polygonal envelopes of cubic splines are cubic
//! splines, hence it isn't necessary to introduce completely different
//! routines. By contrast, exact envelopes of cubic splines with respect
//! to circles are complicated curves, more difficult to plot than cubics.
//!
//! @ Hobby's construction involves some interesting number theory.
//! If $u$ and~$v$ are relatively prime integers, we divide the
//! set of integer points $(m,n)$ into equivalence classes by saying
//! that $(m,n)$ belongs to class $um+vn$. Then any two integer points
//! that lie on a line of slope $-u/v$ belong to the same class, because
//! such points have the form $(m+tv,n-tu)$. Neighboring lines of slope $-u/v$
//! that go through integer points are separated by distance $1/\psqrt{u^2+v^2}$
//! from each other, and these lines are perpendicular to lines of slope~$v/u$.
//! If we start at the origin and travel a distance $k/\psqrt{u^2+v^2}$ in
//! direction $(u,v)$, we reach the line of slope~$-u/v$ whose points
//! belong to class~$k$.
//!
//! For example, let $u=2$ and $v=3$. Then the points $(0,0)$, $(3,-2)$,
//! $\ldots$ belong to class~0; the points $(-1,1)$, $(2,-1)$, $\ldots$ belong
//! to class~1; and the distance between these two lines is $1/\sqrt{13}$.
//! The point $(2,3)$ itself belongs to class~13, hence its distance from
//! the origin is $13/\sqrt{13}=\sqrt{13}$ (which we already knew).
//!
//! Suppose we wish to plot envelopes with respect to polygons with
//! integer vertices. Then the best polygon for curves that travel in
//! direction $(v,-u)$ will contain the points of class~$k$ such that
//! $k/\psqrt{u^2+v^2}$ is as close as possible to~$d$, where $d$ is the
//! maximum distance of the given ellipse from the line $ux+vy=0$.
//!
//! The |fillin| correction assumes that a diagonal line has an
//! apparent thickness $$2f\cdot\min(\vert u\vert,\vert v\vert)/\psqrt{u^2+v^2}$$
//! greater than would be obtained with truly square pixels. (If a
//! white pixel at an exterior corner is assumed to have apparent
//! darkness $f_1$ and a black pixel at an interior corner is assumed
//! to have apparent darkness $1-f_2$, then $f=f_1-f_2$ is the |fillin|
//! parameter.) Under this assumption we want to choose $k$ so that
//! $\bigl(k+2f\cdot\min(\vert u\vert,\vert v\vert)\bigr)\big/\psqrt{u^2+v^2}$
//! is as close as possible to $d$.
//!
//! Integer coordinates for the vertices work nicely because the thickness of
//! the envelope at any given slope is independent of the position of the
//! path with respect to the raster. It turns out, in fact, that the same
//! property holds for polygons whose vertices have coordinates that are
//! integer multiples of~$1\over2$, because ellipses are symmetric about
//! the origin. It's convenient to double all dimensions and require the
//! resulting polygon to have vertices with integer coordinates. For example,
//! to get a circle of {\sl diameter}~$r$, we shall compute integer
//! coordinates for a circle of {\sl radius}~$r$. The circle of radius~$r$
//! will want to be represented by a polygon that contains the boundary
//! points $(0,\pm r)$ and~$(\pm r,0)$; later we will divide everything
//! by~2 and get a polygon with $(0,\pm{1\over2}r)$ and $(\pm{1\over2}r,0)$
//! on its boundary.
//!
//! @ In practice the important slopes are those having small values of
//! $u$ and~$v$; these make regular patterns in which our eyes quickly
//! spot irregularities. For example, horizontal and vertical lines
//! (when $u=0$ and $\vert v\vert=1$, or $\vert u\vert=1$ and $v=0$)
//! are the most important; diagonal lines (when $\vert u\vert=\vert v\vert=1$)
//! are next; and then come lines with slope $\pm2$ or $\pm1/2$.
//!
//! The nicest way to generate all rational directions having small
//! numerators and denominators is to generalize the Stern--Brocot tree
//! [cf.~{\sl Concrete Mathematics}, section 4.5]
//! @^Brocot, Achille@>
//! @^Stern, Moritz Abraham@>
//! to a ``Stern--Brocot wreath'' as follows: Begin with four nodes
//! arranged in a circle, containing the respective directions
//! $(u,v)=(1,0)$, $(0,1)$, $(-1,0)$, and~$(0,-1)$. Then between pairs of
//! consecutive terms $(u,v)$ and $(u',v')$ of the wreath, insert the
//! direction $(u+u',v+v')$; continue doing this until some stopping
//! criterion is fulfilled.
//!
//! It is not difficult to verify that, regardless of the stopping
//! criterion, consecutive directions $(u,v)$ and $(u',v')$ of this
//! wreath will always satisfy the relation $uv'-u'v=1$. Such pairs
//! of directions have a nice property with respect to the equivalence
//! classes described above. Let $l$ be a line of equivalent integer points
//! $(m+tv,n-tu)$ with respect to~$(u,v)$, and let $l'$ be a line of
//! equivalent integer points $(m'+tv',n'-tu')$ with respect to~$(u',v')$.
//! Then $l$ and~$l'$ intersect in an integer point $(m'',n'')$, because
//! the determinant of the linear equations for intersection is $uv'-u'v=1$.
//! Notice that the class number of $(m'',n'')$ with respect to $(u+u',v+v')$
//! is the sum of its class numbers with respect to $(u,v)$ and~$(u',v')$.
//! Moreover, consecutive points on~$l$ and~$l'$ belong to classes that
//! differ by exactly~1 with respect to $(u+u',v+v')$.
//!
//! This leads to a nice algorithm in which we construct a polygon having
//! ``correct'' class numbers for as many small-integer directions $(u,v)$
//! as possible: Assuming that lines $l$ and~$l'$ contain points of the
//! correct class for $(u,v)$ and~$(u',v')$, respectively, we determine
//! the intersection $(m'',n'')$ and compute its class with respect to
//! $(u+u',v+v')$. If the class is too large to be the best approximation,
//! we move back the proper number of steps from $(m'',n'')$ toward smaller
//! class numbers on both $l$ and~$l'$, unless this requires moving to points
//! that are no longer in the polygon; in this way we arrive at two points that
//! determine a line~$l''$ having the appropriate class. The process continues
//! recursively, until it cannot proceed without removing the last remaining
//! point from the class for $(u,v)$ or the class for $(u',v')$.
//!
//! @ The |make_ellipse| subroutine produces a pointer to a cyclic path
//! whose vertices define a polygon suitable for envelopes. The control
//! points on this path will be ignored; in fact, the fields in knot nodes
//! that are usually reserved for control points are occupied by other
//! data that helps |make_ellipse| compute the desired polygon.
//!
//! Parameters |major_axis| and |minor_axis| define the axes of the ellipse;
//! and parameter |theta| is an angle by which the ellipse is rotated
//! counterclockwise. If |theta=0|, the ellipse has the equation
//! $(x/a)^2+(y/b)^2=1$, where |a=major_axis/2| and |b=minor_axis/2|.
//! In general, the points of the ellipse are generated in the complex plane
//! by the formula $e^{i\theta}(a\cos t+ib\sin t)$, as $t$~ranges over all
//! angles. Notice that if |major_axis=minor_axis=d|, we obtain a circle
//! of diameter~|d|, regardless of the value of |theta|.
//!
//! The method sketched above is used to produce the elliptical polygon,
//! except that the main work is done only in the halfplane obtained from
//! the three starting directions $(0,-1)$, $(1,0)$,~$(0,1)$. Since the ellipse
//! has circular symmetry, we use the fact that the last half of the polygon
//! is simply the negative of the first half. Furthermore, we need to compute only
//! one quarter of the polygon if the ellipse has axis symmetry.
//!
//! @p function make_ellipse(@!major_axis,@!minor_axis:scaled;
//!   @!theta:angle):pointer;
//! label done,done1,found;
//! var @!p,@!q,@!r,@!s:pointer; {for list manipulation}
//! @!h:pointer; {head of the constructed knot list}
//! @!alpha,@!beta,@!gamma,@!delta:integer; {special points}
//! @!c,@!d:integer; {class numbers}
//! @!u,@!v:integer; {directions}
//! @!symmetric:boolean; {should the result be symmetric about the axes?}
//! begin @<Initialize the ellipse data structure by beginning with
//!   directions $(0,-1)$, $(1,0)$, $(0,1)$@>;
//! @<Interpolate new vertices in the ellipse data structure until
//!   improvement is impossible@>;
//! if symmetric then
//!   @<Complete the half ellipse by reflecting the quarter already computed@>;
//! @<Complete the ellipse by copying the negative of the half already computed@>;
//! make_ellipse:=h;
//! end;
//!
//! @ A special data structure is used only with |make_ellipse|: The
//! |right_x|, |left_x|, |right_y|, and |left_y| fields of knot nodes
//! are renamed |right_u|, |left_v|, |right_class|, and |left_length|,
//! in order to store information that simplifies the necessary computations.
//!
//! If |p| and |q| are consecutive knots in this data structure, the
//! |x_coord| and |y_coord| fields of |p| and~|q| contain current vertices
//! of the polygon; their values are integer multiples
//! of |half_unit|. Both of these vertices belong to equivalence class
//! |right_class(p)| with respect to the direction
//! $\bigl($|right_u(p),left_v(q)|$\bigr)$. The number of points of this class
//! on the line from vertex~|p| to vertex~|q| is |1+left_length(q)|.
//! In particular, |left_length(q)=0| means that |x_coord(p)=x_coord(q)|
//! and |y_coord(p)=y_coord(q)|; such duplicate vertices will be
//! discarded during the course of the algorithm.
//!
//! The contents of |right_u(p)| and |left_v(q)| are integer multiples
//! of |half_unit|, just like the coordinate fields. Hence, for example,
//! the point $\bigl($|x_coord(p)-left_v(q),y_coord(p)+right_u(p)|$\bigr)$
//! also belongs to class number |right_class(p)|. This point is one
//! step closer to the vertex in node~|q|; it equals that vertex
//! if and only if |left_length(q)=1|.
//!
//! The |left_type| and |right_type| fields are not used, but |link|
//! has its normal meaning.
//!
//! To start the process, we create four nodes for the three directions
//! $(0,-1)$, $(1,0)$, and $(0,1)$. The corresponding vertices are
//! $(-\alpha,-\beta)$, $(\gamma,-\beta)$, $(\gamma,\beta)$, and
//! $(\alpha,\beta)$, where $(\alpha,\beta)$ is a half-integer approximation
//! to where the ellipse rises highest above the $x$-axis, and where
//! $\gamma$ is a half-integer approximation to the maximum $x$~coordinate
//! of the ellipse. The fourth of these nodes is not actually calculated
//! if the ellipse has axis symmetry.
//!
//! @d right_u==right_x {|u| value for a pen edge}
//! @d left_v==left_x {|v| value for a pen edge}
//! @d right_class==right_y {equivalence class number of a pen edge}
//! @d left_length==left_y {length of a pen edge}
//!
//! @<Initialize the ellipse data structure...@>=
//! @<Calculate integers $\alpha$, $\beta$, $\gamma$ for the vertex
//!   coordinates@>;
//! p:=get_node(knot_node_size); q:=get_node(knot_node_size);
//! r:=get_node(knot_node_size);
//! if symmetric then s:=null@+else s:=get_node(knot_node_size);
//! h:=p; link(p):=q; link(q):=r; link(r):=s; {|s=null| or |link(s)=null|}
//! @<Revise the values of $\alpha$, $\beta$, $\gamma$, if necessary,
//!   so that degenerate lines of length zero will not be obtained@>;
//! x_coord(p):=-alpha*half_unit;
//! y_coord(p):=-beta*half_unit;
//! x_coord(q):=gamma*half_unit;@/
//! y_coord(q):=y_coord(p); x_coord(r):=x_coord(q);@/
//! right_u(p):=0; left_v(q):=-half_unit;@/
//! right_u(q):=half_unit; left_v(r):=0;@/
//! right_u(r):=0;
//! right_class(p):=beta; right_class(q):=gamma; right_class(r):=beta;@/
//! left_length(q):=gamma+alpha;
//! if symmetric then
//!   begin y_coord(r):=0; left_length(r):=beta;
//!   end
//! else  begin y_coord(r):=-y_coord(p); left_length(r):=beta+beta;@/
//!   x_coord(s):=-x_coord(p); y_coord(s):=y_coord(r);@/
//!   left_v(s):=half_unit; left_length(s):=gamma-alpha;
//!   end
//!
//! @ One of the important invariants of the pen data structure is that
//! the points are distinct. We may need to correct the pen specification
//! in order to avoid this. (The result of \&{pencircle} will always be at
//! least one pixel wide and one pixel tall, although \&{makepen} is
//! capable of producing smaller pens.)
//!
//! @<Revise the values of $\alpha$, $\beta$, $\gamma$, if necessary...@>=
//! if beta=0 then beta:=1;
//! if gamma=0 then gamma:=1;
//! if gamma<=abs(alpha) then
//!   if alpha>0 then alpha:=gamma-1
//!   else alpha:=1-gamma
//!
//! @ If $a$ and $b$ are the semi-major and semi-minor axes,
//! the given ellipse rises highest above the $x$-axis at the point
//! $\bigl((a^2-b^2)\sin\theta\cos\theta/\rho\bigr)+i\rho$, where
//! $\rho=\sqrt{(a\sin\theta)^2+(b\cos\theta)^2}$. It reaches
//! furthest to the right of~the $y$-axis at the point
//! $\sigma+i(a^2-b^2)\sin\theta\cos\theta/\sigma$, where
//! $\sigma=\sqrt{(a\cos\theta)^2+(b\sin\theta)^2}$.
//!
//! @<Calculate integers $\alpha$, $\beta$, $\gamma$...@>=
//! if (major_axis=minor_axis)or(theta mod ninety_deg=0) then
//!   begin symmetric:=true; alpha:=0;
//!   if odd(theta div ninety_deg) then
//!     begin beta:=major_axis; gamma:=minor_axis;
//!     n_sin:=fraction_one; n_cos:=0; {|n_sin| and |n_cos| are used later}
//!     end
//!   else  begin beta:=minor_axis; gamma:=major_axis; theta:=0;
//!     end; {|n_sin| and |n_cos| aren't needed in this case}
//!   end
//! else  begin symmetric:=false;
//!   n_sin_cos(theta); {set up $|n_sin|=\sin\theta$ and $|n_cos|=\cos\theta$}
//!   gamma:=take_fraction(major_axis,n_sin);
//!   delta:=take_fraction(minor_axis,n_cos);
//!   beta:=pyth_add(gamma,delta);
//!   alpha:=take_fraction(take_fraction(major_axis,
//!       make_fraction(gamma,beta)),n_cos)@|
//!     -take_fraction(take_fraction(minor_axis,
//!       make_fraction(delta,beta)),n_sin);
//!   alpha:=(alpha+half_unit) div unity;
//!   gamma:=pyth_add(take_fraction(major_axis,n_cos),
//!     take_fraction(minor_axis,n_sin));
//!   end;
//! beta:=(beta+half_unit) div unity;
//! gamma:=(gamma+half_unit) div unity
//!
//! @ Now |p|, |q|, and |r| march through the list, always representing
//! three consecutive vertices and two consecutive slope directions.
//! When a new slope is interpolated, we back up slightly, until
//! further refinement is impossible; then we march forward again.
//! The somewhat magical operations performed in this part of the
//! algorithm are justified by the theory sketched earlier.
//! Complications arise only from the need to keep zero-length lines
//! out of the final data structure.
//!
//! @<Interpolate new vertices in the ellipse data structure...@>=
//! loop@+  begin u:=right_u(p)+right_u(q); v:=left_v(q)+left_v(r);
//!   c:=right_class(p)+right_class(q);@/
//!   @<Compute the distance |d| from class~0 to the edge of the ellipse
//!     in direction |(u,v)|, times $\psqrt{u^2+v^2}$,
//!     rounded to the nearest integer@>;
//!   delta:=c-d; {we want to move |delta| steps back
//!       from the intersection vertex~|q|}
//!   if delta>0 then
//!     begin if delta>left_length(r) then delta:=left_length(r);
//!     if delta>=left_length(q) then
//!       @<Remove the line from |p| to |q|,
//!         and adjust vertex~|q| to introduce a new line@>
//!     else @<Insert a new line for direction |(u,v)| between |p| and~|q|@>;
//!     end
//!   else p:=q;
//!   @<Move to the next remaining triple |(p,q,r)|, removing and skipping past
//!     zero-length lines that might be present; |goto done| if all
//!     triples have been processed@>;
//!   end;
//! done:
//!
//! @ The appearance of a zero-length line means that we should advance |p|
//! past it. We must not try to straddle a missing direction, because the
//! algorithm works only on consecutive pairs of directions.
//!
//! @<Move to the next remaining triple |(p,q,r)|...@>=
//! loop@+  begin q:=link(p);
//!   if q=null then goto done;
//!   if left_length(q)=0 then
//!     begin link(p):=link(q); right_class(p):=right_class(q);
//!     right_u(p):=right_u(q); free_node(q,knot_node_size);
//!     end
//!   else  begin r:=link(q);
//!     if r=null then goto done;
//!     if left_length(r)=0 then
//!       begin link(p):=r; free_node(q,knot_node_size); p:=r;
//!       end
//!     else goto found;
//!     end;
//!   end;
//! found:
//!
//! @ The `\&{div} 8' near the end of this step comes from
//! the fact that |delta| is scaled by~$2^{15}$ and $d$~by~$2^{16}$,
//! while |take_fraction| removes a scale factor of~$2^{28}$.
//! We also make sure that $d\G\max(\vert u\vert,\vert v\vert)$, so that
//! the pen will always include a circular pen of diameter~1 as a subset;
//! then it won't be possible to get disconnected path envelopes.
//!
//! @<Compute the distance |d| from class~0 to the edge of the ellipse...@>=
//! delta:=pyth_add(u,v);
//! if major_axis=minor_axis then d:=major_axis {circles are easy}
//! else  begin if theta=0 then
//!     begin alpha:=u; beta:=v;
//!     end
//!   else  begin alpha:=take_fraction(u,n_cos)+take_fraction(v,n_sin);
//!     beta:=take_fraction(v,n_cos)-take_fraction(u,n_sin);
//!     end;
//!   alpha:=make_fraction(alpha,delta);
//!   beta:=make_fraction(beta,delta);
//!   d:=pyth_add(take_fraction(major_axis,alpha),
//!     take_fraction(minor_axis,beta));
//!   end;
//! alpha:=abs(u); beta:=abs(v);
//! if alpha<beta then
//!   begin alpha:=abs(v); beta:=abs(u);
//!   end; {now $\alpha=\max(\vert u\vert,\vert v\vert)$,
//!       $\beta=\min(\vert u\vert,\vert v\vert)$}
//! if internal[fillin]<>0 then
//!   d:=d-take_fraction(internal[fillin],make_fraction(beta+beta,delta));
//! d:=take_fraction((d+4) div 8,delta); alpha:=alpha div half_unit;
//! if d<alpha then d:=alpha
//!
//! @ At this point there's a line of length |<=delta| from vertex~|p|
//! to vertex~|q|, orthogonal to direction $\bigl($|right_u(p),left_v(q)|$\bigr)$;
//! and there's a line of length |>=delta| from vertex~|q|
//! to vertex~|r|, orthogonal to direction $\bigl($|right_u(q),left_v(r)|$\bigr)$.
//! The best line to direction $(u,v)$ should replace the line from
//! |p| to~|q|; this new line will have the same length as the old.
//!
//! @<Remove the line from |p| to |q|...@>=
//! begin delta:=left_length(q);@/
//! right_class(p):=c-delta; right_u(p):=u; left_v(q):=v;@/
//! x_coord(q):=x_coord(q)-delta*left_v(r);
//! y_coord(q):=y_coord(q)+delta*right_u(q);@/
//! left_length(r):=left_length(r)-delta;
//! end
//!
//! @ Here is the main case, now that we have dealt with the exception:
//! We insert a new line of length |delta| for direction |(u,v)|, decreasing
//! each of the adjacent lines by |delta| steps.
//!
//! @<Insert a new line for direction |(u,v)| between |p| and~|q|@>=
//! begin s:=get_node(knot_node_size); link(p):=s; link(s):=q;@/
//! x_coord(s):=x_coord(q)+delta*left_v(q);
//! y_coord(s):=y_coord(q)-delta*right_u(p);@/
//! x_coord(q):=x_coord(q)-delta*left_v(r);
//! y_coord(q):=y_coord(q)+delta*right_u(q);@/
//! left_v(s):=left_v(q); right_u(s):=u; left_v(q):=v;@/
//! right_class(s):=c-delta;@/
//! left_length(s):=left_length(q)-delta; left_length(q):=delta;
//! left_length(r):=left_length(r)-delta;
//! end
//!
//! @ Only the coordinates need to be copied, not the class numbers and other stuff.
//! At this point either |link(p)| or |link(link(p))| is |null|.
//!
//! @<Complete the half ellipse...@>=
//! begin s:=null; q:=h;
//! loop@+  begin r:=get_node(knot_node_size); link(r):=s; s:=r;@/
//!   x_coord(s):=x_coord(q); y_coord(s):=-y_coord(q);
//!   if q=p then goto done1;
//!   q:=link(q);
//!   if y_coord(q)=0 then goto done1;
//!   end;
//! done1: if (link(p)<>null) then free_node(link(p),knot_node_size);
//! link(p):=s; beta:=-y_coord(h);
//! while y_coord(p)<>beta do p:=link(p);
//! q:=link(p);
//! end
//!
//! @ Now we use a somewhat tricky fact: The pointer |q| will be null if and
//! only if the line for the final direction $(0,1)$ has been removed. If
//! that line still survives, it should be combined with a possibly
//! surviving line in the initial direction $(0,-1)$.
//!
//! @<Complete the ellipse by copying...@>=
//! if q<>null then
//!   begin if right_u(h)=0 then
//!     begin p:=h; h:=link(h); free_node(p,knot_node_size);@/
//!     x_coord(q):=-x_coord(h);
//!     end;
//!   p:=q;
//!   end
//! else q:=p;
//! r:=link(h); {now |p=q|, |x_coord(p)=-x_coord(h)|, |y_coord(p)=-y_coord(h)|}
//! repeat s:=get_node(knot_node_size); link(p):=s; p:=s;@/
//! x_coord(p):=-x_coord(r); y_coord(p):=-y_coord(r); r:=link(r);
//! until r=q;
//! link(p):=h
//!
//! @* \[26] Direction and intersection times.
//! A path of length $n$ is defined parametrically by functions $x(t)$ and
//! $y(t)$, for |0<=t<=n|; we can regard $t$ as the ``time'' at which the path
//! reaches the point $\bigl(x(t),y(t)\bigr)$.  In this section of the program
//! we shall consider operations that determine special times associated with
//! given paths: the first time that a path travels in a given direction, and
//! a pair of times at which two paths cross each other.
//!
//! @ Let's start with the easier task. The function |find_direction_time| is
//! given a direction |(x,y)| and a path starting at~|h|. If the path never
//! travels in direction |(x,y)|, the direction time will be~|-1|; otherwise
//! it will be nonnegative.
//!
//! Certain anomalous cases can arise: If |(x,y)=(0,0)|, so that the given
//! direction is undefined, the direction time will be~0. If $\bigl(x'(t),
//! y'(t)\bigr)=(0,0)$, so that the path direction is undefined, it will be
//! assumed to match any given direction at time~|t|.
//!
//! The routine solves this problem in nondegenerate cases by rotating the path
//! and the given direction so that |(x,y)=(1,0)|; i.e., the main task will be
//! to find when a given path first travels ``due east.''
//!
//! @p function find_direction_time(@!x,@!y:scaled;@!h:pointer):scaled;
//! label exit,found,not_found,done;
//! var @!max:scaled; {$\max\bigl(\vert x\vert,\vert y\vert\bigr)$}
//! @!p,@!q:pointer; {for list traversal}
//! @!n:scaled; {the direction time at knot |p|}
//! @!tt:scaled; {the direction time within a cubic}
//! @<Other local variables for |find_direction_time|@>@;
//! begin @<Normalize the given direction for better accuracy;
//!   but |return| with zero result if it's zero@>;
//! n:=0; p:=h;
//! loop@+  begin if right_type(p)=endpoint then goto not_found;
//!   q:=link(p);
//!   @<Rotate the cubic between |p| and |q|; then
//!     |goto found| if the rotated cubic travels due east at some time |tt|;
//!     but |goto not_found| if an entire cyclic path has been traversed@>;
//!   p:=q; n:=n+unity;
//!   end;
//! not_found: find_direction_time:=-unity; return;
//! found: find_direction_time:=n+tt;
//! exit:end;
//!
//! @ @<Normalize the given direction for better accuracy...@>=
//! if abs(x)<abs(y) then
//!   begin x:=make_fraction(x,abs(y));
//!   if y>0 then y:=fraction_one@+else y:=-fraction_one;
//!   end
//! else if x=0 then
//!   begin find_direction_time:=0; return;
//!   end
//! else  begin y:=make_fraction(y,abs(x));
//!   if x>0 then x:=fraction_one@+else x:=-fraction_one;
//!   end
//!
//! @ Since we're interested in the tangent directions, we work with the
//! derivative $${1\over3}B'(x_0,x_1,x_2,x_3;t)=
//! B(x_1-x_0,x_2-x_1,x_3-x_2;t)$$ instead of
//! $B(x_0,x_1,x_2,x_3;t)$ itself. The derived coefficients are also scaled up
//! in order to achieve better accuracy.
//!
//! The given path may turn abruptly at a knot, and it might pass the critical
//! tangent direction at such a time. Therefore we remember the direction |phi|
//! in which the previous rotated cubic was traveling. (The value of |phi| will be
//! undefined on the first cubic, i.e., when |n=0|.)
//!
//! @<Rotate the cubic between |p| and |q|; then...@>=
//! tt:=0;
//! @<Set local variables |x1,x2,x3| and |y1,y2,y3| to multiples of the control
//!   points of the rotated derivatives@>;
//! if y1=0 then if x1>=0 then goto found;
//! if n>0 then
//!   begin @<Exit to |found| if an eastward direction occurs at knot |p|@>;
//!   if p=h then goto not_found;
//!   end;
//! if (x3<>0)or(y3<>0) then phi:=n_arg(x3,y3);
//! @<Exit to |found| if the curve whose derivatives are specified by
//!   |x1,x2,x3,y1,y2,y3| travels eastward at some time~|tt|@>
//!
//! @ @<Other local variables for |find_direction_time|@>=
//! @!x1,@!x2,@!x3,@!y1,@!y2,@!y3:scaled; {multiples of rotated derivatives}
//! @!theta,@!phi:angle; {angles of exit and entry at a knot}
//! @!t:fraction; {temp storage}
//!
//! @ @<Set local variables |x1,x2,x3| and |y1,y2,y3| to multiples...@>=
//! x1:=right_x(p)-x_coord(p); x2:=left_x(q)-right_x(p);
//! x3:=x_coord(q)-left_x(q);@/
//! y1:=right_y(p)-y_coord(p); y2:=left_y(q)-right_y(p);
//! y3:=y_coord(q)-left_y(q);@/
//! max:=abs(x1);
//! if abs(x2)>max then max:=abs(x2);
//! if abs(x3)>max then max:=abs(x3);
//! if abs(y1)>max then max:=abs(y1);
//! if abs(y2)>max then max:=abs(y2);
//! if abs(y3)>max then max:=abs(y3);
//! if max=0 then goto found;
//! while max<fraction_half do
//!   begin double(max); double(x1); double(x2); double(x3);
//!   double(y1); double(y2); double(y3);
//!   end;
//! t:=x1; x1:=take_fraction(x1,x)+take_fraction(y1,y);
//! y1:=take_fraction(y1,x)-take_fraction(t,y);@/
//! t:=x2; x2:=take_fraction(x2,x)+take_fraction(y2,y);
//! y2:=take_fraction(y2,x)-take_fraction(t,y);@/
//! t:=x3; x3:=take_fraction(x3,x)+take_fraction(y3,y);
//! y3:=take_fraction(y3,x)-take_fraction(t,y)
//!
//! @ @<Exit to |found| if an eastward direction occurs at knot |p|@>=
//! theta:=n_arg(x1,y1);
//! if theta>=0 then if phi<=0 then if phi>=theta-one_eighty_deg then goto found;
//! if theta<=0 then if phi>=0 then if phi<=theta+one_eighty_deg then goto found
//!
//! @ In this step we want to use the |crossing_point| routine to find the
//! roots of the quadratic equation $B(y_1,y_2,y_3;t)=0$.
//! Several complications arise: If the quadratic equation has a double root,
//! the curve never crosses zero, and |crossing_point| will find nothing;
//! this case occurs iff $y_1y_3=y_2^2$ and $y_1y_2<0$. If the quadratic
//! equation has simple roots, or only one root, we may have to negate it
//! so that $B(y_1,y_2,y_3;t)$ crosses from positive to negative at its first root.
//! And finally, we need to do special things if $B(y_1,y_2,y_3;t)$ is
//! identically zero.
//!
//! @ @<Exit to |found| if the curve whose derivatives are specified by...@>=
//! if x1<0 then if x2<0 then if x3<0 then goto done;
//! if ab_vs_cd(y1,y3,y2,y2)=0 then
//!   @<Handle the test for eastward directions when $y_1y_3=y_2^2$;
//!     either |goto found| or |goto done|@>;
//! if y1<=0 then
//!   if y1<0 then
//!     begin y1:=-y1; y2:=-y2; y3:=-y3;
//!     end
//!   else if y2>0 then
//!     begin y2:=-y2; y3:=-y3;
//!     end;
//! @<Check the places where $B(y_1,y_2,y_3;t)=0$ to see if
//!   $B(x_1,x_2,x_3;t)\ge0$@>;
//! done:
//!
//! @ The quadratic polynomial $B(y_1,y_2,y_3;t)$ begins |>=0| and has at most
//! two roots, because we know that it isn't identically zero.
//!
//! It must be admitted that the |crossing_point| routine is not perfectly accurate;
//! rounding errors might cause it to find a root when $y_1y_3>y_2^2$, or to
//! miss the roots when $y_1y_3<y_2^2$. The rotation process is itself
//! subject to rounding errors. Yet this code optimistically tries to
//! do the right thing.
//!
//! @d we_found_it==begin tt:=(t+@'4000) div @'10000; goto found;
//!   end
//!
//! @<Check the places where $B(y_1,y_2,y_3;t)=0$...@>=
//! t:=crossing_point(y1,y2,y3);
//! if t>fraction_one then goto done;
//! y2:=t_of_the_way(y2)(y3);
//! x1:=t_of_the_way(x1)(x2);
//! x2:=t_of_the_way(x2)(x3);
//! x1:=t_of_the_way(x1)(x2);
//! if x1>=0 then we_found_it;
//! if y2>0 then y2:=0;
//! tt:=t; t:=crossing_point(0,-y2,-y3);
//! if t>fraction_one then goto done;
//! x1:=t_of_the_way(x1)(x2);
//! x2:=t_of_the_way(x2)(x3);
//! if t_of_the_way(x1)(x2)>=0 then
//!   begin t:=t_of_the_way(tt)(fraction_one); we_found_it;
//!   end
//!
//! @ @<Handle the test for eastward directions when $y_1y_3=y_2^2$;
//!     either |goto found| or |goto done|@>=
//! begin if ab_vs_cd(y1,y2,0,0)<0 then
//!   begin t:=make_fraction(y1,y1-y2);
//!   x1:=t_of_the_way(x1)(x2);
//!   x2:=t_of_the_way(x2)(x3);
//!   if t_of_the_way(x1)(x2)>=0 then we_found_it;
//!   end
//! else if y3=0 then
//!   if y1=0 then
//!     @<Exit to |found| if the derivative $B(x_1,x_2,x_3;t)$ becomes |>=0|@>
//!   else if x3>=0 then
//!     begin tt:=unity; goto found;
//!     end;
//! goto done;
//! end
//!
//! @ At this point we know that the derivative of |y(t)| is identically zero,
//! and that |x1<0|; but either |x2>=0| or |x3>=0|, so there's some hope of
//! traveling east.
//!
//! @<Exit to |found| if the derivative $B(x_1,x_2,x_3;t)$ becomes |>=0|...@>=
//! begin t:=crossing_point(-x1,-x2,-x3);
//! if t<=fraction_one then we_found_it;
//! if ab_vs_cd(x1,x3,x2,x2)<=0 then
//!   begin t:=make_fraction(x1,x1-x2); we_found_it;
//!   end;
//! end
//!
//! @ The intersection of two cubics can be found by an interesting variant
//! of the general bisection scheme described in the introduction to |make_moves|.\
//! Given $w(t)=B(w_0,w_1,w_2,w_3;t)$ and $z(t)=B(z_0,z_1,z_2,z_3;t)$,
//! we wish to find a pair of times $(t_1,t_2)$ such that $w(t_1)=z(t_2)$,
//! if an intersection exists. First we find the smallest rectangle that
//! encloses the points $\{w_0,w_1,w_2,w_3\}$ and check that it overlaps
//! the smallest rectangle that encloses
//! $\{z_0,z_1,z_2,z_3\}$; if not, the cubics certainly don't intersect.
//! But if the rectangles do overlap, we bisect the intervals, getting
//! new cubics $w'$ and~$w''$, $z'$~and~$z''$; the intersection routine first
//! tries for an intersection between $w'$ and~$z'$, then (if unsuccessful)
//! between $w'$ and~$z''$, then (if still unsuccessful) between $w''$ and~$z'$,
//! finally (if thrice unsuccessful) between $w''$ and~$z''$. After $l$~successful
//! levels of bisection we will have determined the intersection times $t_1$
//! and~$t_2$ to $l$~bits of accuracy.
//!
//! \def\submin{_{\rm min}} \def\submax{_{\rm max}}
//! As before, it is better to work with the numbers $W_k=2^l(w_k-w_{k-1})$
//! and $Z_k=2^l(z_k-z_{k-1})$ rather than the coefficients $w_k$ and $z_k$
//! themselves. We also need one other quantity, $\Delta=2^l(w_0-z_0)$,
//! to determine when the enclosing rectangles overlap. Here's why:
//! The $x$~coordinates of~$w(t)$ are between $u\submin$ and $u\submax$,
//! and the $x$~coordinates of~$z(t)$ are between $x\submin$ and $x\submax$,
//! if we write $w_k=(u_k,v_k)$ and $z_k=(x_k,y_k)$ and $u\submin=
//! \min(u_0,u_1,u_2,u_3)$, etc. These intervals of $x$~coordinates
//! overlap if and only if $u\submin\L x\submax$ and
//! $x\submin\L u\submax$. Letting
//! $$U\submin=\min(0,U_1,U_1+U_2,U_1+U_2+U_3),\;
//!   U\submax=\max(0,U_1,U_1+U_2,U_1+U_2+U_3),$$
//! we have $2^lu\submin=2^lu_0+U\submin$, etc.; the condition for overlap
//! reduces to
//! $$X\submin-U\submax\L 2^l(u_0-x_0)\L X\submax-U\submin.$$
//! Thus we want to maintain the quantity $2^l(u_0-x_0)$; similarly,
//! the quantity $2^l(v_0-y_0)$ accounts for the $y$~coordinates. The
//! coordinates of $\Delta=2^l(w_0-z_0)$ must stay bounded as $l$ increases,
//! because of the overlap condition; i.e., we know that $X\submin$,
//! $X\submax$, and their relatives are bounded, hence $X\submax-
//! U\submin$ and $X\submin-U\submax$ are bounded.
//!
//! @ Incidentally, if the given cubics intersect more than once, the process
//! just sketched will not necessarily find the lexicographically smallest pair
//! $(t_1,t_2)$. The solution actually obtained will be smallest in ``shuffled
//! order''; i.e., if $t_1=(.a_1a_2\ldots a_{16})_2$ and
//! $t_2=(.b_1b_2\ldots b_{16})_2$, then we will minimize
//! $a_1b_1a_2b_2\ldots a_{16}b_{16}$, not
//! $a_1a_2\ldots a_{16}b_1b_2\ldots b_{16}$.
//! Shuffled order agrees with lexicographic order if all pairs of solutions
//! $(t_1,t_2)$ and $(t_1',t_2')$ have the property that $t_1<t_1'$ iff
//! $t_2<t_2'$; but in general, lexicographic order can be quite different,
//! and the bisection algorithm would be substantially less efficient if it were
//! constrained by lexicographic order.
//!
//! For example, suppose that an overlap has been found for $l=3$ and
//! $(t_1,t_2)= (.101,.011)$ in binary, but that no overlap is produced by
//! either of the alternatives $(.1010,.0110)$, $(.1010,.0111)$ at level~4.
//! Then there is probably an intersection in one of the subintervals
//! $(.1011,.011x)$; but lexicographic order would require us to explore
//! $(.1010,.1xxx)$ and $(.1011,.00xx)$ and $(.1011,.010x)$ first. We wouldn't
//! want to store all of the subdivision data for the second path, so the
//! subdivisions would have to be regenerated many times. Such inefficiencies
//! would be associated with every `1' in the binary representation of~$t_1$.
//!
//! @ The subdivision process introduces rounding errors, hence we need to
//! make a more liberal test for overlap. It is not hard to show that the
//! computed values of $U_i$ differ from the truth by at most~$l$, on
//! level~$l$, hence $U\submin$ and $U\submax$ will be at most $3l$ in error.
//! If $\beta$ is an upper bound on the absolute error in the computed
//! components of $\Delta=(|delx|,|dely|)$ on level~$l$, we will replace
//! the test `$X\submin-U\submax\L|delx|$' by the more liberal test
//! `$X\submin-U\submax\L|delx|+|tol|$', where $|tol|=6l+\beta$.
//!
//! More accuracy is obtained if we try the algorithm first with |tol=0|;
//! the more liberal tolerance is used only if an exact approach fails.
//! It is convenient to do this double-take by letting `3' in the preceding
//! paragraph be a parameter, which is first 0, then 3.
//!
//! @<Glob...@>=
//! @!tol_step:0..6; {either 0 or 3, usually}
//!
//! @ We shall use an explicit stack to implement the recursive bisection
//! method described above. In fact, the |bisect_stack| array is available for
//! this purpose. It will contain numerous 5-word packets like
//! $(U_1,U_2,U_3,U\submin,U\submax)$, as well as 20-word packets comprising
//! the 5-word packets for $U$, $V$, $X$, and~$Y$.
//!
//! The following macros define the allocation of stack positions to
//! the quantities needed for bisection-intersection.
//!
//! @d stack_1(#)==bisect_stack[#] {$U_1$, $V_1$, $X_1$, or $Y_1$}
//! @d stack_2(#)==bisect_stack[#+1] {$U_2$, $V_2$, $X_2$, or $Y_2$}
//! @d stack_3(#)==bisect_stack[#+2] {$U_3$, $V_3$, $X_3$, or $Y_3$}
//! @d stack_min(#)==bisect_stack[#+3]
//!   {$U\submin$, $V\submin$, $X\submin$, or $Y\submin$}
//! @d stack_max(#)==bisect_stack[#+4]
//!   {$U\submax$, $V\submax$, $X\submax$, or $Y\submax$}
//! @d int_packets=20 {number of words to represent $U_k$, $V_k$, $X_k$, and $Y_k$}
//! @#
//! @d u_packet(#)==#-5
//! @d v_packet(#)==#-10
//! @d x_packet(#)==#-15
//! @d y_packet(#)==#-20
//! @d l_packets==bisect_ptr-int_packets
//! @d r_packets==bisect_ptr
//! @d ul_packet==u_packet(l_packets) {base of $U'_k$ variables}
//! @d vl_packet==v_packet(l_packets) {base of $V'_k$ variables}
//! @d xl_packet==x_packet(l_packets) {base of $X'_k$ variables}
//! @d yl_packet==y_packet(l_packets) {base of $Y'_k$ variables}
//! @d ur_packet==u_packet(r_packets) {base of $U''_k$ variables}
//! @d vr_packet==v_packet(r_packets) {base of $V''_k$ variables}
//! @d xr_packet==x_packet(r_packets) {base of $X''_k$ variables}
//! @d yr_packet==y_packet(r_packets) {base of $Y''_k$ variables}
//! @#
//! @d u1l==stack_1(ul_packet) {$U'_1$}
//! @d u2l==stack_2(ul_packet) {$U'_2$}
//! @d u3l==stack_3(ul_packet) {$U'_3$}
//! @d v1l==stack_1(vl_packet) {$V'_1$}
//! @d v2l==stack_2(vl_packet) {$V'_2$}
//! @d v3l==stack_3(vl_packet) {$V'_3$}
//! @d x1l==stack_1(xl_packet) {$X'_1$}
//! @d x2l==stack_2(xl_packet) {$X'_2$}
//! @d x3l==stack_3(xl_packet) {$X'_3$}
//! @d y1l==stack_1(yl_packet) {$Y'_1$}
//! @d y2l==stack_2(yl_packet) {$Y'_2$}
//! @d y3l==stack_3(yl_packet) {$Y'_3$}
//! @d u1r==stack_1(ur_packet) {$U''_1$}
//! @d u2r==stack_2(ur_packet) {$U''_2$}
//! @d u3r==stack_3(ur_packet) {$U''_3$}
//! @d v1r==stack_1(vr_packet) {$V''_1$}
//! @d v2r==stack_2(vr_packet) {$V''_2$}
//! @d v3r==stack_3(vr_packet) {$V''_3$}
//! @d x1r==stack_1(xr_packet) {$X''_1$}
//! @d x2r==stack_2(xr_packet) {$X''_2$}
//! @d x3r==stack_3(xr_packet) {$X''_3$}
//! @d y1r==stack_1(yr_packet) {$Y''_1$}
//! @d y2r==stack_2(yr_packet) {$Y''_2$}
//! @d y3r==stack_3(yr_packet) {$Y''_3$}
//! @#
//! @d stack_dx==bisect_stack[bisect_ptr] {stacked value of |delx|}
//! @d stack_dy==bisect_stack[bisect_ptr+1] {stacked value of |dely|}
//! @d stack_tol==bisect_stack[bisect_ptr+2] {stacked value of |tol|}
//! @d stack_uv==bisect_stack[bisect_ptr+3] {stacked value of |uv|}
//! @d stack_xy==bisect_stack[bisect_ptr+4] {stacked value of |xy|}
//! @d int_increment=int_packets+int_packets+5 {number of stack words per level}
//!
//! @<Check the ``constant''...@>=
//! if int_packets+17*int_increment>bistack_size then bad:=32;
//!
//! @ Computation of the min and max is a tedious but fairly fast sequence of
//! instructions; exactly four comparisons are made in each branch.
//!
//! @d set_min_max(#)==
//!   if stack_1(#)<0 then
//!     if stack_3(#)>=0 then
//!       begin if stack_2(#)<0 then stack_min(#):=stack_1(#)+stack_2(#)
//!         else stack_min(#):=stack_1(#);
//!       stack_max(#):=stack_1(#)+stack_2(#)+stack_3(#);
//!       if stack_max(#)<0 then stack_max(#):=0;
//!       end
//!     else  begin stack_min(#):=stack_1(#)+stack_2(#)+stack_3(#);
//!       if stack_min(#)>stack_1(#) then stack_min(#):=stack_1(#);
//!       stack_max(#):=stack_1(#)+stack_2(#);
//!       if stack_max(#)<0 then stack_max(#):=0;
//!       end
//!   else if stack_3(#)<=0 then
//!     begin if stack_2(#)>0 then stack_max(#):=stack_1(#)+stack_2(#)
//!       else stack_max(#):=stack_1(#);
//!     stack_min(#):=stack_1(#)+stack_2(#)+stack_3(#);
//!     if stack_min(#)>0 then stack_min(#):=0;
//!     end
//!   else  begin stack_max(#):=stack_1(#)+stack_2(#)+stack_3(#);
//!     if stack_max(#)<stack_1(#) then stack_max(#):=stack_1(#);
//!     stack_min(#):=stack_1(#)+stack_2(#);
//!     if stack_min(#)>0 then stack_min(#):=0;
//!     end
//!
//! @ It's convenient to keep the current values of $l$, $t_1$, and $t_2$ in
//! the integer form $2^l+2^lt_1$ and $2^l+2^lt_2$. The |cubic_intersection|
//! routine uses global variables |cur_t| and |cur_tt| for this purpose;
//! after successful completion, |cur_t| and |cur_tt| will contain |unity|
//! plus the |scaled| values of $t_1$ and~$t_2$.
//!
//! The values of |cur_t| and |cur_tt| will be set to zero if |cubic_intersection|
//! finds no intersection. The routine gives up and gives an approximate answer
//! if it has backtracked
//! more than 5000 times (otherwise there are cases where several minutes
//! of fruitless computation would be possible).
//!
//! @d max_patience=5000
//!
//! @<Glob...@>=
//! @!cur_t,@!cur_tt:integer; {controls and results of |cubic_intersection|}
//! @!time_to_go:integer; {this many backtracks before giving up}
//! @!max_t:integer; {maximum of $2^{l+1}$ so far achieved}
//!
//! @ The given cubics $B(w_0,w_1,w_2,w_3;t)$ and
//! $B(z_0,z_1,z_2,z_3;t)$ are specified in adjacent knot nodes |(p,link(p))|
//! and |(pp,link(pp))|, respectively.
//!
//! @p procedure cubic_intersection(@!p,@!pp:pointer);
//! label continue, not_found, exit;
//! var @!q,@!qq:pointer; {|link(p)|, |link(pp)|}
//! begin time_to_go:=max_patience; max_t:=2;
//! @<Initialize for intersections at level zero@>;
//! loop@+  begin continue:
//!   if delx-tol<=stack_max(x_packet(xy))-stack_min(u_packet(uv)) then
//!    if delx+tol>=stack_min(x_packet(xy))-stack_max(u_packet(uv)) then
//!    if dely-tol<=stack_max(y_packet(xy))-stack_min(v_packet(uv)) then
//!    if dely+tol>=stack_min(y_packet(xy))-stack_max(v_packet(uv)) then
//!     begin if cur_t>=max_t then
//!       begin if max_t=two then {we've done 17 bisections}
//!         begin cur_t:=half(cur_t+1); cur_tt:=half(cur_tt+1); return;
//!         end;
//!       double(max_t); appr_t:=cur_t; appr_tt:=cur_tt;
//!       end;
//!     @<Subdivide for a new level of intersection@>;
//!     goto continue;
//!     end;
//!   if time_to_go>0 then decr(time_to_go)
//!   else  begin while appr_t<unity do
//!       begin double(appr_t); double(appr_tt);
//!       end;
//!     cur_t:=appr_t; cur_tt:=appr_tt; return;
//!     end;
//!   @<Advance to the next pair |(cur_t,cur_tt)|@>;
//!   end;
//! exit:end;
//!
//! @ The following variables are global, although they are used only by
//! |cubic_intersection|, because it is necessary on some machines to
//! split |cubic_intersection| up into two procedures.
//!
//! @<Glob...@>=
//! @!delx,@!dely:integer; {the components of $\Delta=2^l(w_0-z_0)$}
//! @!tol:integer; {bound on the uncertainty in the overlap test}
//! @!uv,@!xy:0..bistack_size; {pointers to the current packets of interest}
//! @!three_l:integer; {|tol_step| times the bisection level}
//! @!appr_t,@!appr_tt:integer; {best approximations known to the answers}
//!
//! @ We shall assume that the coordinates are sufficiently non-extreme that
//! integer overflow will not occur.
//! @^overflow in arithmetic@>
//!
//! @<Initialize for intersections at level zero@>=
//! q:=link(p); qq:=link(pp); bisect_ptr:=int_packets;@/
//! u1r:=right_x(p)-x_coord(p); u2r:=left_x(q)-right_x(p);
//! u3r:=x_coord(q)-left_x(q); set_min_max(ur_packet);@/
//! v1r:=right_y(p)-y_coord(p); v2r:=left_y(q)-right_y(p);
//! v3r:=y_coord(q)-left_y(q); set_min_max(vr_packet);@/
//! x1r:=right_x(pp)-x_coord(pp); x2r:=left_x(qq)-right_x(pp);
//! x3r:=x_coord(qq)-left_x(qq); set_min_max(xr_packet);@/
//! y1r:=right_y(pp)-y_coord(pp); y2r:=left_y(qq)-right_y(pp);
//! y3r:=y_coord(qq)-left_y(qq); set_min_max(yr_packet);@/
//! delx:=x_coord(p)-x_coord(pp); dely:=y_coord(p)-y_coord(pp);@/
//! tol:=0; uv:=r_packets; xy:=r_packets; three_l:=0; cur_t:=1; cur_tt:=1
//!
//! @ @<Subdivide for a new level of intersection@>=
//! stack_dx:=delx; stack_dy:=dely; stack_tol:=tol; stack_uv:=uv; stack_xy:=xy;
//! bisect_ptr:=bisect_ptr+int_increment;@/
//! double(cur_t); double(cur_tt);@/
//! u1l:=stack_1(u_packet(uv)); u3r:=stack_3(u_packet(uv));
//! u2l:=half(u1l+stack_2(u_packet(uv)));
//! u2r:=half(u3r+stack_2(u_packet(uv)));
//! u3l:=half(u2l+u2r); u1r:=u3l;
//! set_min_max(ul_packet); set_min_max(ur_packet);@/
//! v1l:=stack_1(v_packet(uv)); v3r:=stack_3(v_packet(uv));
//! v2l:=half(v1l+stack_2(v_packet(uv)));
//! v2r:=half(v3r+stack_2(v_packet(uv)));
//! v3l:=half(v2l+v2r); v1r:=v3l;
//! set_min_max(vl_packet); set_min_max(vr_packet);@/
//! x1l:=stack_1(x_packet(xy)); x3r:=stack_3(x_packet(xy));
//! x2l:=half(x1l+stack_2(x_packet(xy)));
//! x2r:=half(x3r+stack_2(x_packet(xy)));
//! x3l:=half(x2l+x2r); x1r:=x3l;
//! set_min_max(xl_packet); set_min_max(xr_packet);@/
//! y1l:=stack_1(y_packet(xy)); y3r:=stack_3(y_packet(xy));
//! y2l:=half(y1l+stack_2(y_packet(xy)));
//! y2r:=half(y3r+stack_2(y_packet(xy)));
//! y3l:=half(y2l+y2r); y1r:=y3l;
//! set_min_max(yl_packet); set_min_max(yr_packet);@/
//! uv:=l_packets; xy:=l_packets;
//! double(delx); double(dely);@/
//! tol:=tol-three_l+tol_step; double(tol); three_l:=three_l+tol_step
//!
//! @ @<Advance to the next pair |(cur_t,cur_tt)|@>=
//! not_found: if odd(cur_tt) then
//!   if odd(cur_t) then @<Descend to the previous level and |goto not_found|@>
//!   else  begin incr(cur_t);
//!     delx:=delx+stack_1(u_packet(uv))+stack_2(u_packet(uv))
//!       +stack_3(u_packet(uv));
//!     dely:=dely+stack_1(v_packet(uv))+stack_2(v_packet(uv))
//!       +stack_3(v_packet(uv));
//!     uv:=uv+int_packets; {switch from |l_packets| to |r_packets|}
//!     decr(cur_tt); xy:=xy-int_packets; {switch from |r_packets| to |l_packets|}
//!     delx:=delx+stack_1(x_packet(xy))+stack_2(x_packet(xy))
//!       +stack_3(x_packet(xy));
//!     dely:=dely+stack_1(y_packet(xy))+stack_2(y_packet(xy))
//!       +stack_3(y_packet(xy));
//!     end
//! else  begin incr(cur_tt); tol:=tol+three_l;
//!   delx:=delx-stack_1(x_packet(xy))-stack_2(x_packet(xy))
//!     -stack_3(x_packet(xy));
//!   dely:=dely-stack_1(y_packet(xy))-stack_2(y_packet(xy))
//!     -stack_3(y_packet(xy));
//!   xy:=xy+int_packets; {switch from |l_packets| to |r_packets|}
//!   end
//!
//! @ @<Descend to the previous level...@>=
//! begin cur_t:=half(cur_t); cur_tt:=half(cur_tt);
//! if cur_t=0 then return;
//! bisect_ptr:=bisect_ptr-int_increment; three_l:=three_l-tol_step;
//! delx:=stack_dx; dely:=stack_dy; tol:=stack_tol; uv:=stack_uv; xy:=stack_xy;@/
//! goto not_found;
//! end
//!
//! @ The |path_intersection| procedure is much simpler.
//! It invokes |cubic_intersection| in lexicographic order until finding a
//! pair of cubics that intersect. The final intersection times are placed in
//! |cur_t| and~|cur_tt|.
//!
//! @p procedure path_intersection(@!h,@!hh:pointer);
//! label exit;
//! var @!p,@!pp:pointer; {link registers that traverse the given paths}
//! @!n,@!nn:integer; {integer parts of intersection times, minus |unity|}
//! begin @<Change one-point paths into dead cycles@>;
//! tol_step:=0;
//! repeat n:=-unity; p:=h;
//!   repeat if right_type(p)<>endpoint then
//!     begin nn:=-unity; pp:=hh;
//!     repeat if right_type(pp)<>endpoint then
//!       begin cubic_intersection(p,pp);
//!       if cur_t>0 then
//!         begin cur_t:=cur_t+n; cur_tt:=cur_tt+nn; return;
//!         end;
//!       end;
//!     nn:=nn+unity; pp:=link(pp);
//!     until pp=hh;
//!     end;
//!   n:=n+unity; p:=link(p);
//!   until p=h;
//! tol_step:=tol_step+3;
//! until tol_step>3;
//! cur_t:=-unity; cur_tt:=-unity;
//! exit:end;
//!
//! @ @<Change one-point paths...@>=
//! if right_type(h)=endpoint then
//!   begin right_x(h):=x_coord(h); left_x(h):=x_coord(h);
//!   right_y(h):=y_coord(h); left_y(h):=y_coord(h); right_type(h):=explicit;
//!   end;
//! if right_type(hh)=endpoint then
//!   begin right_x(hh):=x_coord(hh); left_x(hh):=x_coord(hh);
//!   right_y(hh):=y_coord(hh); left_y(hh):=y_coord(hh); right_type(hh):=explicit;
//!   end;
//!
//! @* \[27] Online graphic output.
//! \MF\ displays images on the user's screen by means of a few primitive
//! operations that are defined below. These operations have deliberately been
//! kept simple so that they can be implemented without great difficulty on a
//! wide variety of machines. Since \PASCAL\ has no traditional standards for
//! graphic output, some system-dependent code needs to be written in order to
//! support this aspect of \MF; but the necessary routines are usually quite
//! easy to write.
//! @^system dependencies@>
//!
//! In fact, there are exactly four such routines:
//!
//! \yskip\hang
//! |init_screen| does whatever initialization is necessary to
//! support the other operations; it is a boolean function that returns
//! |false| if graphic output cannot be supported (e.g., if the other three
//! routines have not been written, or if the user doesn't have the
//! right kind of terminal).
//!
//! \yskip\hang
//! |blank_rectangle| updates a buffer area in memory so that
//! all pixels in a specified rectangle will be set to the background color.
//!
//! \yskip\hang
//! |paint_row| assigns values to specified pixels in a row of
//! the buffer just mentioned, based on ``transition'' indices explained below.
//!
//! \yskip\hang
//! |update_screen| displays the current screen buffer; the
//! effects of |blank_rectangle| and |paint_row| commands may or may not
//! become visible until the next |update_screen| operation is performed.
//! (Thus, |update_screen| is analogous to |update_terminal|.)
//!
//! \yskip\noindent
//! The \PASCAL\ code here is a minimum version of |init_screen| and
//! |update_screen|, usable on \MF\ installations that don't
//! support screen output. If |init_screen| is changed to return |true|
//! instead of |false|, the other routines will simply log the fact
//! that they have been called; they won't really display anything.
//! The standard test routines for \MF\ use this log information to check
//! that \MF\ is working properly, but the |wlog| instructions should be
//! removed from production versions of \MF.
//!
//! @p function init_screen:boolean;
//! begin init_screen:=false;
//! end;
//! @#
//! procedure update_screen; {will be called only if |init_screen| returns |true|}
//! begin @!init wlog_ln('Calling UPDATESCREEN');@+tini {for testing only}
//! end;
//!
//! @ The user's screen is assumed to be a rectangular area, |screen_width|
//! pixels wide and |screen_depth| pixels deep. The pixel in the upper left
//! corner is said to be in column~0 of row~0; the pixel in the lower right
//! corner is said to be in column |screen_width-1| of row |screen_depth-1|.
//! Notice that row numbers increase from top to bottom, contrary to \MF's
//! other coordinates.
//!
//! Each pixel is assumed to have two states, referred to in this documentation
//! as |black| and |white|. The background color is called |white| and the
//! other color is called |black|; but any two distinct pixel values
//! can actually be used. For example, the author developed \MF\ on a
//! system for which |white| was black and |black| was bright green.
//!
//! @d white=0 {background pixels}
//! @d black=1 {visible pixels}
//!
//! @<Types...@>=
//! @!screen_row=0..screen_depth; {a row number on the screen}
//! @!screen_col=0..screen_width; {a column number on the screen}
//! @!trans_spec=array[screen_col] of screen_col; {a transition spec, see below}
//! @!pixel_color=white..black; {specifies one of the two pixel values}
//!
//! @ We'll illustrate the |blank_rectangle| and |paint_row| operations by
//! pretending to declare a screen buffer called |screen_pixel|. This code
//! is actually commented out, but it does specify the intended effects.
//!
//! @<Glob...@>=
//! @{@+@!screen_pixel:array[screen_row,screen_col] of pixel_color@t; @>@}
//!
//! @ The |blank_rectangle| routine simply whitens all pixels that lie in
//! columns |left_col| through |right_col-1|, inclusive, of rows
//! |top_row| through |bot_row-1|, inclusive, given four parameters that satisfy
//! the relations
//! $$\hbox{|0<=left_col<=right_col<=screen_width|,\quad
//!   |0<=top_row<=bot_row<=screen_depth|.}$$
//! If |left_col=right_col| or |top_row=bot_row|, nothing happens.
//!
//! The commented-out code in the following procedure is for illustrative
//! purposes only.
//! @^system dependencies@>
//!
//! @p procedure blank_rectangle(@!left_col,@!right_col:screen_col;
//!   @!top_row,@!bot_row:screen_row);
//! var @!r:screen_row;
//! @!c:screen_col;
//! begin @{@+for r:=top_row to bot_row-1 do
//!   for c:=left_col to right_col-1 do
//!     screen_pixel[r,c]:=white;@+@}@/
//! @!init wlog_cr; {this will be done only after |init_screen=true|}
//! wlog_ln('Calling BLANKRECTANGLE(',left_col:1,',',
//!   right_col:1,',',top_row:1,',',bot_row:1,')');@+tini
//! end;
//!
//! @ The real work of screen display is done by |paint_row|. But it's not
//! hard work, because the operation affects only
//! one of the screen rows, and it affects only a contiguous set of columns
//! in that row. There are four parameters: |r|~(the row),
//! |b|~(the initial color),
//! |a|~(the array of transition specifications),
//! and |n|~(the number of transitions). The elements of~|a| will satisfy
//! $$0\L a[0]<a[1]<\cdots<a[n]\L |screen_width|;$$
//! the value of |r| will satisfy |0<=r<screen_depth|; and |n| will be positive.
//!
//! The general idea is to paint blocks of pixels in alternate colors;
//! the precise details are best conveyed by means of a \PASCAL\
//! program (see the commented-out code below).
//! @^system dependencies@>
//!
//! @p procedure paint_row(@!r:screen_row;@!b:pixel_color;var @!a:trans_spec;
//!   @!n:screen_col);
//! var @!k:screen_col; {an index into |a|}
//! @!c:screen_col; {an index into |screen_pixel|}
//! begin @{@+k:=0; c:=a[0];
//! repeat incr(k);
//!   repeat screen_pixel[r,c]:=b; incr(c);
//!   until c=a[k];
//!   b:=black-b; {$|black|\swap|white|$}
//!   until k=n;@+@}@/
//! @!init wlog('Calling PAINTROW(',r:1,',',b:1,';');
//!   {this is done only after |init_screen=true|}
//! for k:=0 to n do
//!   begin wlog(a[k]:1); if k<>n then wlog(',');
//!   end;
//! wlog_ln(')');@+tini
//! end;
//!
//! @ The remainder of \MF's screen routines are system-independent calls
//! on the four primitives just defined.
//!
//! First we have a global boolean variable that tells if |init_screen|
//! has been called, and another one that tells if |init_screen| has
//! given a |true| response.
//!
//! @<Glob...@>=
//! @!screen_started:boolean; {have the screen primitives been initialized?}
//! @!screen_OK:boolean; {is it legitimate to call |blank_rectangle|,
//!   |paint_row|, and |update_screen|?}
//!
//! @ @d start_screen==begin if not screen_started then
//!     begin screen_OK:=init_screen; screen_started:=true;
//!     end;
//!   end
//!
//! @<Set init...@>=
//! screen_started:=false; screen_OK:=false;
//!
//! @ \MF\ provides the user with 16 ``window'' areas on the screen, in each
//! of which it is possible to produce independent displays.
//!
//! It should be noted that \MF's windows aren't really independent
//! ``clickable'' entities in the sense of multi-window graphic workstations;
//! \MF\ simply maps them into subsets of a single screen image that is
//! controlled by |init_screen|, |blank_rectangle|, |paint_row|, and
//! |update_screen| as described above. Implementations of \MF\ on a
//! multi-window workstation probably therefore make use of only two
//! windows in the other sense: one for the terminal output and another
//! for the screen with \MF's 16 areas. Henceforth we shall
//! use the term window only in \MF's sense.
//!
//! @<Types...@>=
//! @!window_number=0..15;
//!
//! @ A user doesn't have to use any of the 16 windows. But when a window is
//! ``opened,'' it is allocated to a specific rectangular portion of the screen
//! and to a specific rectangle with respect to \MF's coordinates. The relevant
//! data is stored in global arrays |window_open|, |left_col|, |right_col|,
//! |top_row|, |bot_row|, |m_window|, and |n_window|.
//!
//! The |window_open| array is boolean, and its significance is obvious. The
//! |left_col|, \dots, |bot_row| arrays contain screen coordinates that
//! can be used to blank the entire window with |blank_rectangle|. And the
//! other two arrays just mentioned handle the conversion between
//! actual coordinates and screen coordinates: \MF's pixel in column~$m$
//! of row~$n$ will appear in screen column |m_window+m| and in screen row
//! |n_window-n|, provided that these lie inside the boundaries of the window.
//!
//! Another array |window_time| holds the number of times this window has
//! been updated.
//!
//! @<Glob...@>=
//! @!window_open:array[window_number] of boolean;
//!   {has this window been opened?}
//! @!left_col:array[window_number] of screen_col;
//!   {leftmost column position on screen}
//! @!right_col:array[window_number] of screen_col;
//!   {rightmost column position, plus~1}
//! @!top_row:array[window_number] of screen_row;
//!   {topmost row position on screen}
//! @!bot_row:array[window_number] of screen_row;
//!   {bottommost row position, plus~1}
//! @!m_window:array[window_number] of integer;
//!   {offset between user and screen columns}
//! @!n_window:array[window_number] of integer;
//!   {offset between user and screen rows}
//! @!window_time:array[window_number] of integer;
//!   {it has been updated this often}
//!
//! @ @<Set init...@>=
//! for k:=0 to 15 do
//!   begin window_open[k]:=false; window_time[k]:=0;
//!   end;
//!
//! @ Opening a window isn't like opening a file, because you can open it
//! as often as you like, and you never have to close it again. The idea is
//! simply to define special points on the current screen display.
//!
//! Overlapping window specifications may cause complex effects that can
//! be understood only by scrutinizing \MF's display algorithms; thus it
//! has been left undefined in the \MF\ user manual, although the behavior
//! @:METAFONTbook}{\sl The {\logos METAFONT\/}book@>
//! is in fact predictable.
//!
//! Here is a subroutine that implements the command `\&{openwindow}~|k|
//! \&{from}~$(\\{r0},\\{c0})$ \&{to}~$(\\{r1},\\{c1})$ \&{at}~$(x,y)$'.
//!
//! @p procedure open_a_window(@!k:window_number;@!r0,@!c0,@!r1,@!c1:scaled;
//!     @!x,@!y:scaled);
//! var @!m,@!n:integer; {pixel coordinates}
//! begin @<Adjust the coordinates |(r0,c0)| and |(r1,c1)| so that
//!   they lie in the proper range@>;
//! window_open[k]:=true; incr(window_time[k]);@/
//! left_col[k]:=c0; right_col[k]:=c1; top_row[k]:=r0; bot_row[k]:=r1;@/
//! @<Compute the offsets between screen coordinates and actual coordinates@>;
//! start_screen;
//! if screen_OK then
//!   begin blank_rectangle(c0,c1,r0,r1); update_screen;
//!   end;
//! end;
//!
//! @ A window whose coordinates don't fit the existing screen size will be
//! truncated until they do.
//!
//! @<Adjust the coordinates |(r0,c0)| and |(r1,c1)|...@>=
//! if r0<0 then r0:=0@+else r0:=round_unscaled(r0);
//! r1:=round_unscaled(r1);
//! if r1>screen_depth then r1:=screen_depth;
//! if r1<r0 then
//!   if r0>screen_depth then r0:=r1@+else r1:=r0;
//! if c0<0 then c0:=0@+else c0:=round_unscaled(c0);
//! c1:=round_unscaled(c1);
//! if c1>screen_width then c1:=screen_width;
//! if c1<c0 then
//!   if c0>screen_width then c0:=c1@+else c1:=c0
//!
//! @ Three sets of coordinates are rampant, and they must be kept straight!
//! (i)~\MF's main coordinates refer to the edges between pixels. (ii)~\MF's
//! pixel coordinates (within edge structures) say that the pixel bounded by
//! $(m,n)$, $(m,n+1)$, $(m+1,n)$, and~$(m+1,n+1)$ is in pixel row number~$n$
//! and pixel column number~$m$. (iii)~Screen coordinates, on the other hand,
//! have rows numbered in increasing order from top to bottom, as mentioned
//! above.
//! @^coordinates, explained@>
//!
//! The program here first computes integers $m$ and $n$ such that
//! pixel column~$m$ of pixel row~$n$ will be at the upper left corner
//! of the window. Hence pixel column |m-c0| of pixel row |n+r0|
//! will be at the upper left corner of the screen.
//!
//! @<Compute the offsets between screen coordinates and actual coordinates@>=
//! m:=round_unscaled(x); n:=round_unscaled(y)-1;@/
//! m_window[k]:=c0-m; n_window[k]:=r0+n
//!
//! @ Now here comes \MF's most complicated operation related to window
//! display: Given the number~|k| of an open window, the pixels of positive
//! weight in |cur_edges| will be shown as |black| in the window; all other
//! pixels will be shown as |white|.
//!
//! @p procedure disp_edges(@!k:window_number);
//! label done,found;
//! var @!p,@!q:pointer; {for list manipulation}
//! @!already_there:boolean; {is a previous incarnation in the window?}
//! @!r:integer; {row number}
//! @<Other local variables for |disp_edges|@>@;
//! begin if screen_OK then
//!  if left_col[k]<right_col[k] then if top_row[k]<bot_row[k] then
//!   begin already_there:=false;
//!   if last_window(cur_edges)=k then
//!    if last_window_time(cur_edges)=window_time[k] then
//!     already_there:=true;
//!   if not already_there then
//!     blank_rectangle(left_col[k],right_col[k],top_row[k],bot_row[k]);
//!   @<Initialize for the display computations@>;
//!   p:=link(cur_edges); r:=n_window[k]-(n_min(cur_edges)-zero_field);
//!   while (p<>cur_edges)and(r>=top_row[k]) do
//!     begin if r<bot_row[k] then
//!       @<Display the pixels of edge row |p| in screen row |r|@>;
//!     p:=link(p); decr(r);
//!     end;
//!   update_screen;
//!   incr(window_time[k]);
//!   last_window(cur_edges):=k; last_window_time(cur_edges):=window_time[k];
//!   end;
//! end;
//!
//! @ Since it takes some work to display a row, we try to avoid recomputation
//! whenever we can.
//!
//! @<Display the pixels of edge row |p| in screen row |r|@>=
//! begin if unsorted(p)>void then sort_edges(p)
//! else if unsorted(p)=void then if already_there then goto done;
//! unsorted(p):=void; {this time we'll paint, but maybe not next time}
//! @<Set up the parameters needed for |paint_row|;
//!   but |goto done| if no painting is needed after all@>;
//! paint_row(r,b,row_transition,n);
//! done: end
//!
//! @ The transition-specification parameter to |paint_row| is always the same
//! array.
//!
//! @<Glob...@>=
//! @!row_transition:trans_spec; {an array of |black|/|white| transitions}
//!
//! @ The job remaining is to go through the list |sorted(p)|, unpacking the
//! |info| fields into |m| and weight, then making |black| the pixels whose
//! accumulated weight~|w| is positive.
//!
//! @<Other local variables for |disp_edges|@>=
//! @!n:screen_col; {the highest active index in |row_transition|}
//! @!w,@!ww:integer; {old and new accumulated weights}
//! @!b:pixel_color; {status of first pixel in the row transitions}
//! @!m,@!mm:integer; {old and new screen column positions}
//! @!d:integer; {edge-and-weight without |min_halfword| compensation}
//! @!m_adjustment:integer; {conversion between edge and screen coordinates}
//! @!right_edge:integer; {largest edge-and-weight that could affect the window}
//! @!min_col:screen_col; {the smallest screen column number in the window}
//!
//! @ Some precomputed constants make the display calculations faster.
//!
//! @<Initialize for the display computations@>=
//! m_adjustment:=m_window[k]-m_offset(cur_edges);@/
//! right_edge:=8*(right_col[k]-m_adjustment);@/
//! min_col:=left_col[k]
//!
//! @ @<Set up the parameters needed for |paint_row|...@>=
//! n:=0; ww:=0; m:=-1; w:=0;
//! q:=sorted(p); row_transition[0]:=min_col;
//! loop@+  begin if q=sentinel then d:=right_edge
//!   else d:=ho(info(q));
//!   mm:=(d div 8)+m_adjustment;
//!   if mm<>m then
//!     begin @<Record a possible transition in column |m|@>;
//!     m:=mm; w:=ww;
//!     end;
//!   if d>=right_edge then goto found;
//!   ww:=ww+(d mod 8)-zero_w;
//!   q:=link(q);
//!   end;
//! found:@<Wind up the |paint_row| parameter calculation by inserting the
//!   final transition; |goto done| if no painting is needed@>;
//!
//! @ Now |m| is a screen column |<right_col[k]|.
//!
//! @<Record a possible transition in column |m|@>=
//! if w<=0 then
//!   begin if ww>0 then if m>min_col then
//!     begin if n=0 then
//!       if already_there then
//!         begin b:=white; incr(n);
//!         end
//!       else b:=black
//!     else incr(n);
//!     row_transition[n]:=m;
//!     end;
//!   end
//! else if ww<=0 then if m>min_col then
//!   begin if n=0 then b:=black;
//!   incr(n); row_transition[n]:=m;
//!   end
//!
//! @ If the entire row is |white| in the window area, we can omit painting it
//! when |already_there| is false, since it has already been blanked out in
//! that case.
//!
//! When the following code is invoked, |row_transition[n]| will be
//! strictly less than |right_col[k]|.
//!
//! @<Wind up the |paint_row|...@>=
//! if already_there or(ww>0) then
//!   begin if n=0 then
//!     if ww>0 then b:=black
//!     else b:=white;
//!   incr(n); row_transition[n]:=right_col[k];
//!   end
//! else if n=0 then goto done
//!
//! @* \[28] Dynamic linear equations.
//! \MF\ users define variables implicitly by stating equations that should be
//! satisfied; the computer is supposed to be smart enough to solve those equations.
//! And indeed, the computer tries valiantly to do so, by distinguishing five
//! different types of numeric values:
//!
//! \smallskip\hang
//! |type(p)=known| is the nice case, when |value(p)| is the |scaled| value
//! of the variable whose address is~|p|.
//!
//! \smallskip\hang
//! |type(p)=dependent| means that |value(p)| is not present, but |dep_list(p)|
//! points to a {\sl dependency list\/} that expresses the value of variable~|p|
//! as a |scaled| number plus a sum of independent variables with |fraction|
//! coefficients.
//!
//! \smallskip\hang
//! |type(p)=independent| means that |value(p)=64s+m|, where |s>0| is a ``serial
//! number'' reflecting the time this variable was first used in an equation;
//! also |0<=m<64|, and each dependent variable
//! that refers to this one is actually referring to the future value of
//! this variable times~$2^m$. (Usually |m=0|, but higher degrees of
//! scaling are sometimes needed to keep the coefficients in dependency lists
//! from getting too large. The value of~|m| will always be even.)
//!
//! \smallskip\hang
//! |type(p)=numeric_type| means that variable |p| hasn't appeared in an
//! equation before, but it has been explicitly declared to be numeric.
//!
//! \smallskip\hang
//! |type(p)=undefined| means that variable |p| hasn't appeared before.
//!
//! \smallskip\noindent
//! We have actually discussed these five types in the reverse order of their
//! history during a computation: Once |known|, a variable never again
//! becomes |dependent|; once |dependent|, it almost never again becomes
//! |independent|; once |independent|, it never again becomes |numeric_type|;
//! and once |numeric_type|, it never again becomes |undefined| (except
//! of course when the user specifically decides to scrap the old value
//! and start again). A backward step may, however, take place: Sometimes
//! a |dependent| variable becomes |independent| again, when one of the
//! independent variables it depends on is reverting to |undefined|.
//!
//! @d s_scale=64 {the serial numbers are multiplied by this factor}
//! @d new_indep(#)== {create a new independent variable}
//!   begin if serial_no>el_gordo-s_scale then
//!       overflow("independent variables",serial_no div s_scale);
//! @:METAFONT capacity exceeded independent variables}{\quad independent variables@>
//!   type(#):=independent; serial_no:=serial_no+s_scale;
//!   value(#):=serial_no;
//!   end
//!
//! @<Glob...@>=
//! @!serial_no:integer; {the most recent serial number, times |s_scale|}
//!
//! @ @<Make variable |q+s| newly independent@>=new_indep(q+s)
//!
//! @ But how are dependency lists represented? It's simple: The linear combination
//! $\alpha_1v_1+\cdots+\alpha_kv_k+\beta$ appears in |k+1| value nodes. If
//! |q=dep_list(p)| points to this list, and if |k>0|, then |value(q)=
//! @t$\alpha_1$@>| (which is a |fraction|); |info(q)| points to the location
//! of $v_1$; and |link(p)| points to the dependency list
//! $\alpha_2v_2+\cdots+\alpha_kv_k+\beta$. On the other hand if |k=0|,
//! then |value(q)=@t$\beta$@>| (which is |scaled|) and |info(q)=null|.
//! The independent variables $v_1$, \dots,~$v_k$ have been sorted so that
//! they appear in decreasing order of their |value| fields (i.e., of
//! their serial numbers). \ (It is convenient to use decreasing order,
//! since |value(null)=0|. If the independent variables were not sorted by
//! serial number but by some other criterion, such as their location in |mem|,
//! the equation-solving mechanism would be too system-dependent, because
//! the ordering can affect the computed results.)
//!
//! The |link| field in the node that contains the constant term $\beta$ is
//! called the {\sl final link\/} of the dependency list. \MF\ maintains
//! a doubly-linked master list of all dependency lists, in terms of a permanently
//! allocated node
//! in |mem| called |dep_head|. If there are no dependencies, we have
//! |link(dep_head)=dep_head| and |prev_dep(dep_head)=dep_head|;
//! otherwise |link(dep_head)| points to the first dependent variable, say~|p|,
//! and |prev_dep(p)=dep_head|. We have |type(p)=dependent|, and |dep_list(p)|
//! points to its dependency list. If the final link of that dependency list
//! occurs in location~|q|, then |link(q)| points to the next dependent
//! variable (say~|r|); and we have |prev_dep(r)=q|, etc.
//!
//! @d dep_list(#)==link(value_loc(#))
//!   {half of the |value| field in a |dependent| variable}
//! @d prev_dep(#)==info(value_loc(#))
//!   {the other half; makes a doubly linked list}
//! @d dep_node_size=2 {the number of words per dependency node}
//!
//! @<Initialize table entries...@>= serial_no:=0;
//! link(dep_head):=dep_head; prev_dep(dep_head):=dep_head;
//! info(dep_head):=null; dep_list(dep_head):=null;
//!
//! @ Actually the description above contains a little white lie. There's
//! another kind of variable called |proto_dependent|, which is
//! just like a |dependent| one except that the $\alpha$ coefficients
//! in its dependency list are |scaled| instead of being fractions.
//! Proto-dependency lists are mixed with dependency lists in the
//! nodes reachable from |dep_head|.
//!
//! @ Here is a procedure that prints a dependency list in symbolic form.
//! The second parameter should be either |dependent| or |proto_dependent|,
//! to indicate the scaling of the coefficients.
//!
//! @<Declare subroutines for printing expressions@>=
//! procedure print_dependency(@!p:pointer;@!t:small_number);
//! label exit;
//! var @!v:integer; {a coefficient}
//! @!pp,@!q:pointer; {for list manipulation}
//! begin pp:=p;
//! loop@+  begin v:=abs(value(p)); q:=info(p);
//!   if q=null then {the constant term}
//!     begin if (v<>0)or(p=pp) then
//!       begin if value(p)>0 then if p<>pp then print_char("+");
//!       print_scaled(value(p));
//!       end;
//!     return;
//!     end;
//!   @<Print the coefficient, unless it's $\pm1.0$@>;
//!   if type(q)<>independent then confusion("dep");
//! @:this can't happen dep}{\quad dep@>
//!   print_variable_name(q); v:=value(q) mod s_scale;
//!   while v>0 do
//!     begin print("*4"); v:=v-2;
//!     end;
//!   p:=link(p);
//!   end;
//! exit:end;
//!
//! @ @<Print the coefficient, unless it's $\pm1.0$@>=
//! if value(p)<0 then print_char("-")
//! else if p<>pp then print_char("+");
//! if t=dependent then v:=round_fraction(v);
//! if v<>unity then print_scaled(v)
//!
//! @ The maximum absolute value of a coefficient in a given dependency list
//! is returned by the following simple function.
//!
//! @p function max_coef(@!p:pointer):fraction;
//! var @!x:fraction; {the maximum so far}
//! begin x:=0;
//! while info(p)<>null do
//!   begin if abs(value(p))>x then x:=abs(value(p));
//!   p:=link(p);
//!   end;
//! max_coef:=x;
//! end;
//!
//! @ One of the main operations needed on dependency lists is to add a multiple
//! of one list to the other; we call this |p_plus_fq|, where |p| and~|q| point
//! to dependency lists and |f| is a fraction.
//!
//! If the coefficient of any independent variable becomes |coef_bound| or
//! more, in absolute value, this procedure changes the type of that variable
//! to `|independent_needing_fix|', and sets the global variable |fix_needed|
//! to~|true|. The value of $|coef_bound|=\mu$ is chosen so that
//! $\mu^2+\mu<8$; this means that the numbers we deal with won't
//! get too large. (Instead of the ``optimum'' $\mu=(\sqrt{33}-1)/2\approx
//! 2.3723$, the safer value 7/3 is taken as the threshold.)
//!
//! The changes mentioned in the preceding paragraph are actually done only if
//! the global variable |watch_coefs| is |true|. But it usually is; in fact,
//! it is |false| only when \MF\ is making a dependency list that will soon
//! be equated to zero.
//!
//! Several procedures that act on dependency lists, including |p_plus_fq|,
//! set the global variable |dep_final| to the final (constant term) node of
//! the dependency list that they produce.
//!
//! @d coef_bound==@'4525252525 {|fraction| approximation to 7/3}
//! @d independent_needing_fix=0
//!
//! @<Glob...@>=
//! @!fix_needed:boolean; {does at least one |independent| variable need scaling?}
//! @!watch_coefs:boolean; {should we scale coefficients that exceed |coef_bound|?}
//! @!dep_final:pointer; {location of the constant term and final link}
//!
//! @ @<Set init...@>=
//! fix_needed:=false; watch_coefs:=true;
//!
//! @ The |p_plus_fq| procedure has a fourth parameter, |t|, that should be
//! set to |proto_dependent| if |p| is a proto-dependency list. In this
//! case |f| will be |scaled|, not a |fraction|. Similarly, the fifth parameter~|tt|
//! should be |proto_dependent| if |q| is a proto-dependency list.
//!
//! List |q| is unchanged by the operation; but list |p| is totally destroyed.
//!
//! The final link of the dependency list or proto-dependency list returned
//! by |p_plus_fq| is the same as the original final link of~|p|. Indeed, the
//! constant term of the result will be located in the same |mem| location
//! as the original constant term of~|p|.
//!
//! Coefficients of the result are assumed to be zero if they are less than
//! a certain threshold. This compensates for inevitable rounding errors,
//! and tends to make more variables `|known|'. The threshold is approximately
//! $10^{-5}$ in the case of normal dependency lists, $10^{-4}$ for
//! proto-dependencies.
//!
//! @d fraction_threshold=2685 {a |fraction| coefficient less than this is zeroed}
//! @d half_fraction_threshold=1342 {half of |fraction_threshold|}
//! @d scaled_threshold=8 {a |scaled| coefficient less than this is zeroed}
//! @d half_scaled_threshold=4 {half of |scaled_threshold|}
//!
//! @<Declare basic dependency-list subroutines@>=
//! function p_plus_fq(@!p:pointer;@!f:integer;@!q:pointer;
//!   @!t,@!tt:small_number):pointer;
//! label done;
//! var @!pp,@!qq:pointer; {|info(p)| and |info(q)|, respectively}
//! @!r,@!s:pointer; {for list manipulation}
//! @!threshold:integer; {defines a neighborhood of zero}
//! @!v:integer; {temporary register}
//! begin if t=dependent then threshold:=fraction_threshold
//! else threshold:=scaled_threshold;
//! r:=temp_head; pp:=info(p); qq:=info(q);
//! loop@+  if pp=qq then
//!     if pp=null then goto done
//!     else @<Contribute a term from |p|, plus |f| times the
//!       corresponding term from |q|@>
//!   else if value(pp)<value(qq) then
//!     @<Contribute a term from |q|, multiplied by~|f|@>
//!   else  begin link(r):=p; r:=p; p:=link(p); pp:=info(p);
//!     end;
//! done: if t=dependent then
//!   value(p):=slow_add(value(p),take_fraction(value(q),f))
//! else  value(p):=slow_add(value(p),take_scaled(value(q),f));
//! link(r):=p; dep_final:=p; p_plus_fq:=link(temp_head);
//! end;
//!
//! @ @<Contribute a term from |p|, plus |f|...@>=
//! begin if tt=dependent then v:=value(p)+take_fraction(f,value(q))
//! else v:=value(p)+take_scaled(f,value(q));
//! value(p):=v; s:=p; p:=link(p);
//! if abs(v)<threshold then free_node(s,dep_node_size)
//! else  begin if abs(v)>=coef_bound then if watch_coefs then
//!     begin type(qq):=independent_needing_fix; fix_needed:=true;
//!     end;
//!   link(r):=s; r:=s;
//!   end;
//! pp:=info(p); q:=link(q); qq:=info(q);
//! end
//!
//! @ @<Contribute a term from |q|, multiplied by~|f|@>=
//! begin if tt=dependent then v:=take_fraction(f,value(q))
//! else v:=take_scaled(f,value(q));
//! if abs(v)>half(threshold) then
//!   begin s:=get_node(dep_node_size); info(s):=qq; value(s):=v;
//!   if abs(v)>=coef_bound then if watch_coefs then
//!     begin type(qq):=independent_needing_fix; fix_needed:=true;
//!     end;
//!   link(r):=s; r:=s;
//!   end;
//! q:=link(q); qq:=info(q);
//! end
//!
//! @ It is convenient to have another subroutine for the special case
//! of |p_plus_fq| when |f=1.0|. In this routine lists |p| and |q| are
//! both of the same type~|t| (either |dependent| or |proto_dependent|).
//!
//! @p function p_plus_q(@!p:pointer;@!q:pointer;@!t:small_number):pointer;
//! label done;
//! var @!pp,@!qq:pointer; {|info(p)| and |info(q)|, respectively}
//! @!r,@!s:pointer; {for list manipulation}
//! @!threshold:integer; {defines a neighborhood of zero}
//! @!v:integer; {temporary register}
//! begin if t=dependent then threshold:=fraction_threshold
//! else threshold:=scaled_threshold;
//! r:=temp_head; pp:=info(p); qq:=info(q);
//! loop@+  if pp=qq then
//!     if pp=null then goto done
//!     else @<Contribute a term from |p|, plus the
//!       corresponding term from |q|@>
//!   else if value(pp)<value(qq) then
//!     begin s:=get_node(dep_node_size); info(s):=qq; value(s):=value(q);
//!     q:=link(q); qq:=info(q); link(r):=s; r:=s;
//!     end
//!   else  begin link(r):=p; r:=p; p:=link(p); pp:=info(p);
//!     end;
//! done: value(p):=slow_add(value(p),value(q));
//! link(r):=p; dep_final:=p; p_plus_q:=link(temp_head);
//! end;
//!
//! @ @<Contribute a term from |p|, plus the...@>=
//! begin v:=value(p)+value(q);
//! value(p):=v; s:=p; p:=link(p); pp:=info(p);
//! if abs(v)<threshold then free_node(s,dep_node_size)
//! else  begin if abs(v)>=coef_bound then if watch_coefs then
//!     begin type(qq):=independent_needing_fix; fix_needed:=true;
//!     end;
//!   link(r):=s; r:=s;
//!   end;
//! q:=link(q); qq:=info(q);
//! end
//!
//! @ A somewhat simpler routine will multiply a dependency list
//! by a given constant~|v|. The constant is either a |fraction| less than
//! |fraction_one|, or it is |scaled|. In the latter case we might be forced to
//! convert a dependency list to a proto-dependency list.
//! Parameters |t0| and |t1| are the list types before and after;
//! they should agree unless |t0=dependent| and |t1=proto_dependent|
//! and |v_is_scaled=true|.
//!
//! @p function p_times_v(@!p:pointer;@!v:integer;
//!   @!t0,@!t1:small_number;@!v_is_scaled:boolean):pointer;
//! var @!r,@!s:pointer; {for list manipulation}
//! @!w:integer; {tentative coefficient}
//! @!threshold:integer;
//! @!scaling_down:boolean;
//! begin if t0<>t1 then scaling_down:=true@+else scaling_down:=not v_is_scaled;
//! if t1=dependent then threshold:=half_fraction_threshold
//! else threshold:=half_scaled_threshold;
//! r:=temp_head;
//! while info(p)<>null do
//!   begin if scaling_down then w:=take_fraction(v,value(p))
//!   else w:=take_scaled(v,value(p));
//!   if abs(w)<=threshold then
//!     begin s:=link(p); free_node(p,dep_node_size); p:=s;
//!     end
//!   else  begin if abs(w)>=coef_bound then
//!       begin fix_needed:=true; type(info(p)):=independent_needing_fix;
//!       end;
//!     link(r):=p; r:=p; value(p):=w; p:=link(p);
//!     end;
//!   end;
//! link(r):=p;
//! if v_is_scaled then value(p):=take_scaled(value(p),v)
//! else value(p):=take_fraction(value(p),v);
//! p_times_v:=link(temp_head);
//! end;
//!
//! @ Similarly, we sometimes need to divide a dependency list
//! by a given |scaled| constant.
//!
//! @<Declare basic dependency-list subroutines@>=
//! function p_over_v(@!p:pointer;@!v:scaled;
//!   @!t0,@!t1:small_number):pointer;
//! var @!r,@!s:pointer; {for list manipulation}
//! @!w:integer; {tentative coefficient}
//! @!threshold:integer;
//! @!scaling_down:boolean;
//! begin if t0<>t1 then scaling_down:=true@+else scaling_down:=false;
//! if t1=dependent then threshold:=half_fraction_threshold
//! else threshold:=half_scaled_threshold;
//! r:=temp_head;
//! while info(p)<>null do
//!   begin if scaling_down then
//!     if abs(v)<@'2000000 then w:=make_scaled(value(p),v*@'10000)
//!     else w:=make_scaled(round_fraction(value(p)),v)
//!   else w:=make_scaled(value(p),v);
//!   if abs(w)<=threshold then
//!     begin s:=link(p); free_node(p,dep_node_size); p:=s;
//!     end
//!   else  begin if abs(w)>=coef_bound then
//!       begin fix_needed:=true; type(info(p)):=independent_needing_fix;
//!       end;
//!     link(r):=p; r:=p; value(p):=w; p:=link(p);
//!     end;
//!   end;
//! link(r):=p; value(p):=make_scaled(value(p),v);
//! p_over_v:=link(temp_head);
//! end;
//!
//! @ Here's another utility routine for dependency lists. When an independent
//! variable becomes dependent, we want to remove it from all existing
//! dependencies. The |p_with_x_becoming_q| function computes the
//! dependency list of~|p| after variable~|x| has been replaced by~|q|.
//!
//! This procedure has basically the same calling conventions as |p_plus_fq|:
//! List~|q| is unchanged; list~|p| is destroyed; the constant node and the
//! final link are inherited from~|p|; and the fourth parameter tells whether
//! or not |p| is |proto_dependent|. However, the global variable |dep_final|
//! is not altered if |x| does not occur in list~|p|.
//!
//! @p function p_with_x_becoming_q(@!p,@!x,@!q:pointer;@!t:small_number):pointer;
//! var @!r,@!s:pointer; {for list manipulation}
//! @!v:integer; {coefficient of |x|}
//! @!sx:integer; {serial number of |x|}
//! begin s:=p; r:=temp_head; sx:=value(x);
//! while value(info(s))>sx do
//!   begin r:=s; s:=link(s);
//!   end;
//! if info(s)<>x then p_with_x_becoming_q:=p
//! else  begin link(temp_head):=p; link(r):=link(s); v:=value(s);
//!   free_node(s,dep_node_size);
//!   p_with_x_becoming_q:=p_plus_fq(link(temp_head),v,q,t,dependent);
//!   end;
//! end;
//!
//! @ Here's a simple procedure that reports an error when a variable
//! has just received a known value that's out of the required range.
//!
//! @<Declare basic dependency-list subroutines@>=
//! procedure val_too_big(@!x:scaled);
//! begin if internal[warning_check]>0 then
//!   begin print_err("Value is too large ("); print_scaled(x); print_char(")");
//! @.Value is too large@>
//!   help4("The equation I just processed has given some variable")@/
//!     ("a value of 4096 or more. Continue and I'll try to cope")@/
//!     ("with that big value; but it might be dangerous.")@/
//!     ("(Set warningcheck:=0 to suppress this message.)");
//!   error;
//!   end;
//! end;
//!
//! @ When a dependent variable becomes known, the following routine
//! removes its dependency list. Here |p| points to the variable, and
//! |q| points to the dependency list (which is one node long).
//!
//! @<Declare basic dependency-list subroutines@>=
//! procedure make_known(@!p,@!q:pointer);
//! var @!t:dependent..proto_dependent; {the previous type}
//! begin prev_dep(link(q)):=prev_dep(p);
//! link(prev_dep(p)):=link(q); t:=type(p);
//! type(p):=known; value(p):=value(q); free_node(q,dep_node_size);
//! if abs(value(p))>=fraction_one then val_too_big(value(p));
//! if internal[tracing_equations]>0 then if interesting(p) then
//!   begin begin_diagnostic; print_nl("#### ");
//! @:]]]\#\#\#\#_}{\.{\#\#\#\#}@>
//!   print_variable_name(p); print_char("="); print_scaled(value(p));
//!   end_diagnostic(false);
//!   end;
//! if cur_exp=p then if cur_type=t then
//!   begin cur_type:=known; cur_exp:=value(p);
//!   free_node(p,value_node_size);
//!   end;
//! end;
//!
//! @ The |fix_dependencies| routine is called into action when |fix_needed|
//! has been triggered. The program keeps a list~|s| of independent variables
//! whose coefficients must be divided by~4.
//!
//! In unusual cases, this fixup process might reduce one or more coefficients
//! to zero, so that a variable will become known more or less by default.
//!
//! @<Declare basic dependency-list subroutines@>=
//! procedure fix_dependencies;
//! label done;
//! var @!p,@!q,@!r,@!s,@!t:pointer; {list manipulation registers}
//! @!x:pointer; {an independent variable}
//! begin r:=link(dep_head); s:=null;
//! while r<>dep_head do
//!   begin t:=r;
//!   @<Run through the dependency list for variable |t|, fixing
//!     all nodes, and ending with final link~|q|@>;
//!   r:=link(q);
//!   if q=dep_list(t) then make_known(t,q);
//!   end;
//! while s<>null do
//!   begin p:=link(s); x:=info(s); free_avail(s); s:=p;
//!   type(x):=independent; value(x):=value(x)+2;
//!   end;
//! fix_needed:=false;
//! end;
//!
//! @ @d independent_being_fixed=1 {this variable already appears in |s|}
//!
//! @<Run through the dependency list for variable |t|...@>=
//! r:=value_loc(t); {|link(r)=dep_list(t)|}
//! loop@+  begin q:=link(r); x:=info(q);
//!   if x=null then goto done;
//!   if type(x)<=independent_being_fixed then
//!     begin if type(x)<independent_being_fixed then
//!       begin p:=get_avail; link(p):=s; s:=p;
//!       info(s):=x; type(x):=independent_being_fixed;
//!       end;
//!     value(q):=value(q) div 4;
//!     if value(q)=0 then
//!       begin link(r):=link(q); free_node(q,dep_node_size); q:=r;
//!       end;
//!     end;
//!   r:=q;
//!   end;
//! done:
//!
//! @ The |new_dep| routine installs a dependency list~|p| into the value node~|q|,
//! linking it into the list of all known dependencies. We assume that
//! |dep_final| points to the final node of list~|p|.
//!
//! @p procedure new_dep(@!q,@!p:pointer);
//! var @!r:pointer; {what used to be the first dependency}
//! begin dep_list(q):=p; prev_dep(q):=dep_head;
//! r:=link(dep_head); link(dep_final):=r; prev_dep(r):=dep_final;
//! link(dep_head):=q;
//! end;
//!
//! @ Here is one of the ways a dependency list gets started.
//! The |const_dependency| routine produces a list that has nothing but
//! a constant term.
//!
//! @p function const_dependency(@!v:scaled):pointer;
//! begin dep_final:=get_node(dep_node_size);
//! value(dep_final):=v; info(dep_final):=null;
//! const_dependency:=dep_final;
//! end;
//!
//! @ And here's a more interesting way to start a dependency list from scratch:
//! The parameter to |single_dependency| is the location of an
//! independent variable~|x|, and the result is the simple dependency list
//! `|x+0|'.
//!
//! In the unlikely event that the given independent variable has been doubled so
//! often that we can't refer to it with a nonzero coefficient,
//! |single_dependency| returns the simple list `0'.  This case can be
//! recognized by testing that the returned list pointer is equal to
//! |dep_final|.
//!
//! @p function single_dependency(@!p:pointer):pointer;
//! var @!q:pointer; {the new dependency list}
//! @!m:integer; {the number of doublings}
//! begin m:=value(p) mod s_scale;
//! if m>28 then single_dependency:=const_dependency(0)
//! else  begin q:=get_node(dep_node_size);
//!   value(q):=two_to_the[28-m]; info(q):=p;@/
//!   link(q):=const_dependency(0); single_dependency:=q;
//!   end;
//! end;
//!
//! @ We sometimes need to make an exact copy of a dependency list.
//!
//! @p function copy_dep_list(@!p:pointer):pointer;
//! label done;
//! var @!q:pointer; {the new dependency list}
//! begin q:=get_node(dep_node_size); dep_final:=q;
//! loop@+  begin info(dep_final):=info(p); value(dep_final):=value(p);
//!   if info(dep_final)=null then goto done;
//!   link(dep_final):=get_node(dep_node_size);
//!   dep_final:=link(dep_final); p:=link(p);
//!   end;
//! done:copy_dep_list:=q;
//! end;
//!
//! @ But how do variables normally become known? Ah, now we get to the heart of the
//! equation-solving mechanism. The |linear_eq| procedure is given a |dependent|
//! or |proto_dependent| list,~|p|, in which at least one independent variable
//! appears. It equates this list to zero, by choosing an independent variable
//! with the largest coefficient and making it dependent on the others. The
//! newly dependent variable is eliminated from all current dependencies,
//! thereby possibly making other dependent variables known.
//!
//! The given list |p| is, of course, totally destroyed by all this processing.
//!
//! @p procedure linear_eq(@!p:pointer;@!t:small_number);
//! var @!q,@!r,@!s:pointer; {for link manipulation}
//! @!x:pointer; {the variable that loses its independence}
//! @!n:integer; {the number of times |x| had been halved}
//! @!v:integer; {the coefficient of |x| in list |p|}
//! @!prev_r:pointer; {lags one step behind |r|}
//! @!final_node:pointer; {the constant term of the new dependency list}
//! @!w:integer; {a tentative coefficient}
//! begin @<Find a node |q| in list |p| whose coefficient |v| is largest@>;
//! x:=info(q); n:=value(x) mod s_scale;@/
//! @<Divide list |p| by |-v|, removing node |q|@>;
//! if internal[tracing_equations]>0 then @<Display the new dependency@>;
//! @<Simplify all existing dependencies by substituting for |x|@>;
//! @<Change variable |x| from |independent| to |dependent| or |known|@>;
//! if fix_needed then fix_dependencies;
//! end;
//!
//! @ @<Find a node |q| in list |p| whose coefficient |v| is largest@>=
//! q:=p; r:=link(p); v:=value(q);
//! while info(r)<>null do
//!   begin if abs(value(r))>abs(v) then
//!     begin q:=r; v:=value(r);
//!     end;
//!   r:=link(r);
//!   end
//!
//! @ Here we want to change the coefficients from |scaled| to |fraction|,
//! except in the constant term. In the common case of a trivial equation
//! like `\.{x=3.14}', we will have |v=-fraction_one|, |q=p|, and |t=dependent|.
//!
//! @<Divide list |p| by |-v|, removing node |q|@>=
//! s:=temp_head; link(s):=p; r:=p;
//! repeat if r=q then
//!   begin link(s):=link(r); free_node(r,dep_node_size);
//!   end
//! else  begin w:=make_fraction(value(r),v);
//!   if abs(w)<=half_fraction_threshold then
//!     begin link(s):=link(r); free_node(r,dep_node_size);
//!     end
//!   else  begin value(r):=-w; s:=r;
//!     end;
//!   end;
//! r:=link(s);
//! until info(r)=null;
//! if t=proto_dependent then value(r):=-make_scaled(value(r),v)
//! else if v<>-fraction_one then value(r):=-make_fraction(value(r),v);
//! final_node:=r; p:=link(temp_head)
//!
//! @ @<Display the new dependency@>=
//! if interesting(x) then
//!   begin begin_diagnostic; print_nl("## "); print_variable_name(x);
//! @:]]]\#\#_}{\.{\#\#}@>
//!   w:=n;
//!   while w>0 do
//!     begin print("*4"); w:=w-2;
//!     end;
//!   print_char("="); print_dependency(p,dependent); end_diagnostic(false);
//!   end
//!
//! @ @<Simplify all existing dependencies by substituting for |x|@>=
//! prev_r:=dep_head; r:=link(dep_head);
//! while r<>dep_head do
//!   begin s:=dep_list(r); q:=p_with_x_becoming_q(s,x,p,type(r));
//!   if info(q)=null then make_known(r,q)
//!   else  begin dep_list(r):=q;
//!     repeat q:=link(q);
//!     until info(q)=null;
//!     prev_r:=q;
//!     end;
//!   r:=link(prev_r);
//!   end
//!
//! @ @<Change variable |x| from |independent| to |dependent| or |known|@>=
//! if n>0 then @<Divide list |p| by $2^n$@>;
//! if info(p)=null then
//!   begin type(x):=known;
//!   value(x):=value(p);
//!   if abs(value(x))>=fraction_one then val_too_big(value(x));
//!   free_node(p,dep_node_size);
//!   if cur_exp=x then if cur_type=independent then
//!     begin cur_exp:=value(x); cur_type:=known;
//!     free_node(x,value_node_size);
//!     end;
//!   end
//! else  begin type(x):=dependent; dep_final:=final_node; new_dep(x,p);
//!   if cur_exp=x then if cur_type=independent then cur_type:=dependent;
//!   end
//!
//! @ @<Divide list |p| by $2^n$@>=
//! begin s:=temp_head; link(temp_head):=p; r:=p;
//! repeat if n>30 then w:=0
//! else w:=value(r) div two_to_the[n];
//! if (abs(w)<=half_fraction_threshold)and(info(r)<>null) then
//!   begin link(s):=link(r);
//!   free_node(r,dep_node_size);
//!   end
//! else  begin value(r):=w; s:=r;
//!   end;
//! r:=link(s);
//! until info(s)=null;
//! p:=link(temp_head);
//! end
//!
//! @ The |check_mem| procedure, which is used only when \MF\ is being
//! debugged, makes sure that the current dependency lists are well formed.
//!
//! @<Check the list of linear dependencies@>=
//! q:=dep_head; p:=link(q);
//! while p<>dep_head do
//!   begin if prev_dep(p)<>q then
//!     begin print_nl("Bad PREVDEP at "); print_int(p);
//! @.Bad PREVDEP...@>
//!     end;
//!   p:=dep_list(p); r:=inf_val;
//!   repeat if value(info(p))>=value(r) then
//!     begin print_nl("Out of order at "); print_int(p);
//! @.Out of order...@>
//!     end;
//!   r:=info(p); q:=p; p:=link(q);
//!   until r=null;
//!   end
//!
//! @* \[29] Dynamic nonlinear equations.
//! Variables of numeric type are maintained by the general scheme of
//! independent, dependent, and known values that we have just studied;
//! and the components of pair and transform variables are handled in the
//! same way. But \MF\ also has five other types of values: \&{boolean},
//! \&{string}, \&{pen}, \&{path}, and \&{picture}; what about them?
//!
//! Equations are allowed between nonlinear quantities, but only in a
//! simple form. Two variables that haven't yet been assigned values are
//! either equal to each other, or they're not.
//!
//! Before a boolean variable has received a value, its type is |unknown_boolean|;
//! similarly, there are variables whose type is |unknown_string|, |unknown_pen|,
//! |unknown_path|, and |unknown_picture|. In such cases the value is either
//! |null| (which means that no other variables are equivalent to this one), or
//! it points to another variable of the same undefined type. The pointers in the
//! latter case form a cycle of nodes, which we shall call a ``ring.''
//! Rings of undefined variables may include capsules, which arise as
//! intermediate results within expressions or as \&{expr} parameters to macros.
//!
//! When one member of a ring receives a value, the same value is given to
//! all the other members. In the case of paths and pictures, this implies
//! making separate copies of a potentially large data structure; users should
//! restrain their enthusiasm for such generality, unless they have lots and
//! lots of memory space.
//!
//! @ The following procedure is called when a capsule node is being
//! added to a ring (e.g., when an unknown variable is mentioned in an expression).
//!
//! @p function new_ring_entry(@!p:pointer):pointer;
//! var q:pointer; {the new capsule node}
//! begin q:=get_node(value_node_size); name_type(q):=capsule;
//! type(q):=type(p);
//! if value(p)=null then value(q):=p@+else value(q):=value(p);
//! value(p):=q;
//! new_ring_entry:=q;
//! end;
//!
//! @ Conversely, we might delete a capsule or a variable before it becomes known.
//! The following procedure simply detaches a quantity from its ring,
//! without recycling the storage.
//!
//! @<Declare the recycling subroutines@>=
//! procedure ring_delete(@!p:pointer);
//! var @!q:pointer;
//! begin q:=value(p);
//! if q<>null then if q<>p then
//!   begin while value(q)<>p do q:=value(q);
//!   value(q):=value(p);
//!   end;
//! end;
//!
//! @ Eventually there might be an equation that assigns values to all of the
//! variables in a ring. The |nonlinear_eq| subroutine does the necessary
//! propagation of values.
//!
//! If the parameter |flush_p| is |true|, node |p| itself needn't receive a
//! value; it will soon be recycled.
//!
//! @p procedure nonlinear_eq(@!v:integer;@!p:pointer;@!flush_p:boolean);
//! var @!t:small_number; {the type of ring |p|}
//! @!q,@!r:pointer; {link manipulation registers}
//! begin t:=type(p)-unknown_tag; q:=value(p);
//! if flush_p then type(p):=vacuous@+else p:=q;
//! repeat r:=value(q); type(q):=t;
//! case t of
//! boolean_type: value(q):=v;
//! string_type: begin value(q):=v; add_str_ref(v);
//!   end;
//! pen_type: begin value(q):=v; add_pen_ref(v);
//!   end;
//! path_type: value(q):=copy_path(v);
//! picture_type: value(q):=copy_edges(v);
//! end; {there ain't no more cases}
//! q:=r;
//! until q=p;
//! end;
//!
//! @ If two members of rings are equated, and if they have the same type,
//! the |ring_merge| procedure is called on to make them equivalent.
//!
//! @p procedure ring_merge(@!p,@!q:pointer);
//! label exit;
//! var @!r:pointer; {traverses one list}
//! begin r:=value(p);
//! while r<>p do
//!   begin if r=q then
//!     begin @<Exclaim about a redundant equation@>;
//!     return;
//!     end;
//!   r:=value(r);
//!   end;
//! r:=value(p); value(p):=value(q); value(q):=r;
//! exit:end;
//!
//! @ @<Exclaim about a redundant equation@>=
//! begin print_err("Redundant equation");@/
//! @.Redundant equation@>
//! help2("I already knew that this equation was true.")@/
//!   ("But perhaps no harm has been done; let's continue.");@/
//! put_get_error;
//! end
//!
