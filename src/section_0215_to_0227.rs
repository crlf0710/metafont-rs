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
