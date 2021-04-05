//! @ @<Put each...@>=
//! primitive("end",stop,0);@/
//! @!@:end_}{\&{end} primitive@>
//! primitive("dump",stop,1);@/
//! @!@:dump_}{\&{dump} primitive@>
//!
//! @ @<Cases of |print_cmd...@>=
//! stop:if m=0 then print("end")@+else print("dump");
//!
//! @* \[44] Commands.
//! Let's turn now to statements that are classified as ``commands'' because
//! of their imperative nature. We'll begin with simple ones, so that it
//! will be clear how to hook command processing into the |do_statement| routine;
//! then we'll tackle the tougher commands.
//!
//! Here's one of the simplest:
//!
//! @<Cases of |do_statement|...@>=
//! random_seed: do_random_seed;
//!
//! @ @<Declare action procedures for use by |do_statement|@>=
//! procedure do_random_seed;
//! begin get_x_next;
//! if cur_cmd<>assignment then
//!   begin missing_err(":=");
//! @.Missing `:='@>
//!   help1("Always say `randomseed:=<numeric expression>'.");
//!   back_error;
//!   end;
//! get_x_next; scan_expression;
//! if cur_type<>known then
//!   begin exp_err("Unknown value will be ignored");
//! @.Unknown value...ignored@>
//!   help2("Your expression was too random for me to handle,")@/
//!     ("so I won't change the random seed just now.");@/
//!   put_get_flush_error(0);
//!   end
//! else @<Initialize the random seed to |cur_exp|@>;
//! end;
//!
//! @ @<Initialize the random seed to |cur_exp|@>=
//! begin init_randoms(cur_exp);
//! if selector>=log_only then
//!   begin old_setting:=selector; selector:=log_only;
//!   print_nl("{randomseed:="); print_scaled(cur_exp); print_char("}");
//!   print_nl(""); selector:=old_setting;
//!   end;
//! end
//!
//! @ And here's another simple one (somewhat different in flavor):
//!
//! @<Cases of |do_statement|...@>=
//! mode_command: begin print_ln; interaction:=cur_mod;
//!   @<Initialize the print |selector| based on |interaction|@>;
//!   if log_opened then selector:=selector+2;
//!   get_x_next;
//!   end;
//!
//! @ @<Put each...@>=
//! primitive("batchmode",mode_command,batch_mode);
//! @!@:batch_mode_}{\&{batchmode} primitive@>
//! primitive("nonstopmode",mode_command,nonstop_mode);
//! @!@:nonstop_mode_}{\&{nonstopmode} primitive@>
//! primitive("scrollmode",mode_command,scroll_mode);
//! @!@:scroll_mode_}{\&{scrollmode} primitive@>
//! primitive("errorstopmode",mode_command,error_stop_mode);
//! @!@:error_stop_mode_}{\&{errorstopmode} primitive@>
//!
//! @ @<Cases of |print_cmd_mod|...@>=
//! mode_command: case m of
//!   batch_mode: print("batchmode");
//!   nonstop_mode: print("nonstopmode");
//!   scroll_mode: print("scrollmode");
//!   othercases print("errorstopmode")
//!   endcases;
//!
//! @ The `\&{inner}' and `\&{outer}' commands are only slightly harder.
//!
//! @<Cases of |do_statement|...@>=
//! protection_command: do_protection;
//!
//! @ @<Put each...@>=
//! primitive("inner",protection_command,0);@/
//! @!@:inner_}{\&{inner} primitive@>
//! primitive("outer",protection_command,1);@/
//! @!@:outer_}{\&{outer} primitive@>
//!
//! @ @<Cases of |print_cmd...@>=
//! protection_command: if m=0 then print("inner")@+else print("outer");
//!
//! @ @<Declare action procedures for use by |do_statement|@>=
//! procedure do_protection;
//! var @!m:0..1; {0 to unprotect, 1 to protect}
//! @!t:halfword; {the |eq_type| before we change it}
//! begin m:=cur_mod;
//! repeat get_symbol; t:=eq_type(cur_sym);
//!   if m=0 then
//!     begin if t>=outer_tag then eq_type(cur_sym):=t-outer_tag;
//!     end
//!   else if t<outer_tag then eq_type(cur_sym):=t+outer_tag;
//!   get_x_next;
//! until cur_cmd<>comma;
//! end;
//!
//! @ \MF\ never defines the tokens `\.(' and `\.)' to be primitives, but
//! plain \MF\ begins with the declaration `\&{delimiters} \.{()}'. Such a
//! declaration assigns the command code |left_delimiter| to `\.{(}' and
//! |right_delimiter| to `\.{)}'; the |equiv| of each delimiter is the
//! hash address of its mate.
//!
//! @<Cases of |do_statement|...@>=
//! delimiters: def_delims;
//!
//! @ @<Declare action procedures for use by |do_statement|@>=
//! procedure def_delims;
//! var l_delim,r_delim:pointer; {the new delimiter pair}
//! begin get_clear_symbol; l_delim:=cur_sym;@/
//! get_clear_symbol; r_delim:=cur_sym;@/
//! eq_type(l_delim):=left_delimiter; equiv(l_delim):=r_delim;@/
//! eq_type(r_delim):=right_delimiter; equiv(r_delim):=l_delim;@/
//! get_x_next;
//! end;
//!
//! @ Here is a procedure that is called when \MF\ has reached a point
//! where some right delimiter is mandatory.
//!
//! @<Declare the procedure called |check_delimiter|@>=
//! procedure check_delimiter(@!l_delim,@!r_delim:pointer);
//! label exit;
//! begin if cur_cmd=right_delimiter then if cur_mod=l_delim then return;
//! if cur_sym<>r_delim then
//!   begin  missing_err(text(r_delim));@/
//! @.Missing `)'@>
//!   help2("I found no right delimiter to match a left one. So I've")@/
//!     ("put one in, behind the scenes; this may fix the problem.");
//!   back_error;
//!   end
//! else  begin print_err("The token `"); slow_print(text(r_delim));
//! @.The token...delimiter@>
//!   print("' is no longer a right delimiter");
//!   help3("Strange: This token has lost its former meaning!")@/
//!     ("I'll read it as a right delimiter this time;")@/
//!     ("but watch out, I'll probably miss it later.");
//!   error;
//!   end;
//! exit:end;
//!
//! @ The next four commands save or change the values associated with tokens.
//!
//! @<Cases of |do_statement|...@>=
//! save_command: repeat get_symbol; save_variable(cur_sym); get_x_next;
//!   until cur_cmd<>comma;
//! interim_command: do_interim;
//! let_command: do_let;
//! new_internal: do_new_internal;
//!
//! @ @<Declare action procedures for use by |do_statement|@>=
//! procedure@?do_statement; forward;@t\2@>@/
//! procedure do_interim;
//! begin get_x_next;
//! if cur_cmd<>internal_quantity then
//!   begin print_err("The token `");
//! @.The token...quantity@>
//!   if cur_sym=0 then print("(%CAPSULE)")
//!   else slow_print(text(cur_sym));
//!   print("' isn't an internal quantity");
//!   help1("Something like `tracingonline' should follow `interim'.");
//!   back_error;
//!   end
//! else  begin save_internal(cur_mod); back_input;
//!   end;
//! do_statement;
//! end;
//!
//! @ The following procedure is careful not to undefine the left-hand symbol
//! too soon, lest commands like `{\tt let x=x}' have a surprising effect.
//!
//! @<Declare action procedures for use by |do_statement|@>=
//! procedure do_let;
//! var @!l:pointer; {hash location of the left-hand symbol}
//! begin get_symbol; l:=cur_sym; get_x_next;
//! if cur_cmd<>equals then if cur_cmd<>assignment then
//!   begin missing_err("=");
//! @.Missing `='@>
//!   help3("You should have said `let symbol = something'.")@/
//!     ("But don't worry; I'll pretend that an equals sign")@/
//!     ("was present. The next token I read will be `something'.");
//!   back_error;
//!   end;
//! get_symbol;
//! case cur_cmd of
//! defined_macro,secondary_primary_macro,tertiary_secondary_macro,
//!  expression_tertiary_macro: add_mac_ref(cur_mod);
//! othercases do_nothing
//! endcases;@/
//! clear_symbol(l,false); eq_type(l):=cur_cmd;
//! if cur_cmd=tag_token then equiv(l):=null
//! else equiv(l):=cur_mod;
//! get_x_next;
//! end;
//!
//! @ @<Declare action procedures for use by |do_statement|@>=
//! procedure do_new_internal;
//! begin repeat if int_ptr=max_internal then
//!   overflow("number of internals",max_internal);
//! @:METAFONT capacity exceeded number of int}{\quad number of internals@>
//! get_clear_symbol; incr(int_ptr);
//! eq_type(cur_sym):=internal_quantity; equiv(cur_sym):=int_ptr;
//! int_name[int_ptr]:=text(cur_sym); internal[int_ptr]:=0;
//! get_x_next;
//! until cur_cmd<>comma;
//! end;
//!
//! @ The various `\&{show}' commands are distinguished by modifier fields
//! in the usual way.
//!
//! @d show_token_code=0 {show the meaning of a single token}
//! @d show_stats_code=1 {show current memory and string usage}
//! @d show_code=2 {show a list of expressions}
//! @d show_var_code=3 {show a variable and its descendents}
//! @d show_dependencies_code=4 {show dependent variables in terms of independents}
//!
//! @<Put each...@>=
//! primitive("showtoken",show_command,show_token_code);@/
//! @!@:show_token_}{\&{showtoken} primitive@>
//! primitive("showstats",show_command,show_stats_code);@/
//! @!@:show_stats_}{\&{showstats} primitive@>
//! primitive("show",show_command,show_code);@/
//! @!@:show_}{\&{show} primitive@>
//! primitive("showvariable",show_command,show_var_code);@/
//! @!@:show_var_}{\&{showvariable} primitive@>
//! primitive("showdependencies",show_command,show_dependencies_code);@/
//! @!@:show_dependencies_}{\&{showdependencies} primitive@>
//!
//! @ @<Cases of |print_cmd...@>=
//! show_command: case m of
//!   show_token_code:print("showtoken");
//!   show_stats_code:print("showstats");
//!   show_code:print("show");
//!   show_var_code:print("showvariable");
//!   othercases print("showdependencies")
//!   endcases;
//!
//! @ @<Cases of |do_statement|...@>=
//! show_command:do_show_whatever;
//!
//! @ The value of |cur_mod| controls the |verbosity| in the |print_exp| routine:
//! If it's |show_code|, complicated structures are abbreviated, otherwise
//! they aren't.
//!
//! @<Declare action procedures for use by |do_statement|@>=
//! procedure do_show;
//! begin repeat get_x_next; scan_expression;
//! print_nl(">> ");
//! @.>>@>
//! print_exp(null,2); flush_cur_exp(0);
//! until cur_cmd<>comma;
//! end;
//!
//! @ @<Declare action procedures for use by |do_statement|@>=
//! procedure disp_token;
//! begin print_nl("> ");
//! @.>\relax@>
//! if cur_sym=0 then @<Show a numeric or string or capsule token@>
//! else  begin slow_print(text(cur_sym)); print_char("=");
//!   if eq_type(cur_sym)>=outer_tag then print("(outer) ");
//!   print_cmd_mod(cur_cmd,cur_mod);
//!   if cur_cmd=defined_macro then
//!     begin print_ln; show_macro(cur_mod,null,100000);
//!     end; {this avoids recursion between |show_macro| and |print_cmd_mod|}
//! @^recursion@>
//!   end;
//! end;
//!
//! @ @<Show a numeric or string or capsule token@>=
//! begin if cur_cmd=numeric_token then print_scaled(cur_mod)
//! else if cur_cmd=capsule_token then
//!   begin g_pointer:=cur_mod; print_capsule;
//!   end
//! else  begin print_char(""""); slow_print(cur_mod); print_char("""");
//!   delete_str_ref(cur_mod);
//!   end;
//! end
//!
//! @ The following cases of |print_cmd_mod| might arise in connection
//! with |disp_token|, although they don't necessarily correspond to
//! primitive tokens.
//!
//! @<Cases of |print_cmd_...@>=
//! left_delimiter,right_delimiter: begin if c=left_delimiter then print("lef")
//!   else print("righ");
//!   print("t delimiter that matches "); slow_print(text(m));
//!   end;
//! tag_token:if m=null then print("tag")@+else print("variable");
//! defined_macro: print("macro:");
//! secondary_primary_macro,tertiary_secondary_macro,expression_tertiary_macro:
//!   begin print_cmd_mod(macro_def,c); print("'d macro:");
//!   print_ln; show_token_list(link(link(m)),null,1000,0);
//!   end;
//! repeat_loop:print("[repeat the loop]");
//! internal_quantity:slow_print(int_name[m]);
//!
//! @ @<Declare action procedures for use by |do_statement|@>=
//! procedure do_show_token;
//! begin repeat get_next; disp_token;
//! get_x_next;
//! until cur_cmd<>comma;
//! end;
//!
//! @ @<Declare action procedures for use by |do_statement|@>=
//! procedure do_show_stats;
//! begin print_nl("Memory usage ");
//! @.Memory usage...@>
//! @!stat print_int(var_used); print_char("&"); print_int(dyn_used);
//! if false then@+tats@t@>@;@/
//! print("unknown");
//! print(" ("); print_int(hi_mem_min-lo_mem_max-1);
//! print(" still untouched)"); print_ln;
//! print_nl("String usage ");
//! print_int(str_ptr-init_str_ptr); print_char("&");
//! print_int(pool_ptr-init_pool_ptr);
//! print(" (");
//! print_int(max_strings-max_str_ptr); print_char("&");
//! print_int(pool_size-max_pool_ptr); print(" still untouched)"); print_ln;
//! get_x_next;
//! end;
//!
//! @ Here's a recursive procedure that gives an abbreviated account
//! of a variable, for use by |do_show_var|.
//!
//! @<Declare action procedures for use by |do_statement|@>=
//! procedure disp_var(@!p:pointer);
//! var @!q:pointer; {traverses attributes and subscripts}
//! @!n:0..max_print_line; {amount of macro text to show}
//! begin if type(p)=structured then @<Descend the structure@>
//! else if type(p)>=unsuffixed_macro then @<Display a variable macro@>
//! else if type(p)<>undefined then
//!   begin print_nl(""); print_variable_name(p); print_char("=");
//!   print_exp(p,0);
//!   end;
//! end;
//!
//! @ @<Descend the structure@>=
//! begin q:=attr_head(p);
//! repeat disp_var(q); q:=link(q);
//! until q=end_attr;
//! q:=subscr_head(p);
//! while name_type(q)=subscr do
//!   begin disp_var(q); q:=link(q);
//!   end;
//! end
//!
//! @ @<Display a variable macro@>=
//! begin print_nl(""); print_variable_name(p);
//! if type(p)>unsuffixed_macro then print("@@#"); {|suffixed_macro|}
//! print("=macro:");
//! if file_offset>=max_print_line-20 then n:=5
//! else n:=max_print_line-file_offset-15;
//! show_macro(value(p),null,n);
//! end
//!
//! @ @<Declare action procedures for use by |do_statement|@>=
//! procedure do_show_var;
//! label done;
//! begin repeat get_next;
//! if cur_sym>0 then if cur_sym<=hash_end then
//!  if cur_cmd=tag_token then if cur_mod<>null then
//!   begin disp_var(cur_mod); goto done;
//!   end;
//! disp_token;
//! done:get_x_next;
//! until cur_cmd<>comma;
//! end;
//!
//! @ @<Declare action procedures for use by |do_statement|@>=
//! procedure do_show_dependencies;
//! var @!p:pointer; {link that runs through all dependencies}
//! begin p:=link(dep_head);
//! while p<>dep_head do
//!   begin if interesting(p) then
//!     begin print_nl(""); print_variable_name(p);
//!     if type(p)=dependent then print_char("=")
//!     else print(" = "); {extra spaces imply proto-dependency}
//!     print_dependency(dep_list(p),type(p));
//!     end;
//!   p:=dep_list(p);
//!   while info(p)<>null do p:=link(p);
//!   p:=link(p);
//!   end;
//! get_x_next;
//! end;
//!
//! @ Finally we are ready for the procedure that governs all of the
//! show commands.
//!
//! @<Declare action procedures for use by |do_statement|@>=
//! procedure do_show_whatever;
//! begin if interaction=error_stop_mode then wake_up_terminal;
//! case cur_mod of
//! show_token_code:do_show_token;
//! show_stats_code:do_show_stats;
//! show_code:do_show;
//! show_var_code:do_show_var;
//! show_dependencies_code:do_show_dependencies;
//! end; {there are no other cases}
//! if internal[showstopping]>0 then
//!   begin print_err("OK");
//! @.OK@>
//!   if interaction<error_stop_mode then
//!     begin help0; decr(error_count);
//!     end
//!   else help1("This isn't an error message; I'm just showing something.");
//!   if cur_cmd=semicolon then error@+else put_get_error;
//!   end;
//! end;
//!
//! @ The `\&{addto}' command needs the following additional primitives:
//!
//! @d drop_code=0 {command modifier for `\&{dropping}'}
//! @d keep_code=1 {command modifier for `\&{keeping}'}
//!
//! @<Put each...@>=
//! primitive("contour",thing_to_add,contour_code);@/
//! @!@:contour_}{\&{contour} primitive@>
//! primitive("doublepath",thing_to_add,double_path_code);@/
//! @!@:double_path_}{\&{doublepath} primitive@>
//! primitive("also",thing_to_add,also_code);@/
//! @!@:also_}{\&{also} primitive@>
//! primitive("withpen",with_option,pen_type);@/
//! @!@:with_pen_}{\&{withpen} primitive@>
//! primitive("withweight",with_option,known);@/
//! @!@:with_weight_}{\&{withweight} primitive@>
//! primitive("dropping",cull_op,drop_code);@/
//! @!@:dropping_}{\&{dropping} primitive@>
//! primitive("keeping",cull_op,keep_code);@/
//! @!@:keeping_}{\&{keeping} primitive@>
//!
//! @ @<Cases of |print_cmd...@>=
//! thing_to_add:if m=contour_code then print("contour")
//!   else if m=double_path_code then print("doublepath")
//!   else print("also");
//! with_option:if m=pen_type then print("withpen")
//!   else print("withweight");
//! cull_op:if m=drop_code then print("dropping")
//!   else print("keeping");
//!
//! @ @<Declare action procedures for use by |do_statement|@>=
//! function scan_with:boolean;
//! var @!t:small_number; {|known| or |pen_type|}
//! @!result:boolean; {the value to return}
//! begin t:=cur_mod; cur_type:=vacuous; get_x_next; scan_expression;
//! result:=false;
//! if cur_type<>t then @<Complain about improper type@>
//! else if cur_type=pen_type then result:=true
//! else @<Check the tentative weight@>;
//! scan_with:=result;
//! end;
//!
//! @ @<Complain about improper type@>=
//! begin exp_err("Improper type");
//! @.Improper type@>
//! help2("Next time say `withweight <known numeric expression>';")@/
//!   ("I'll ignore the bad `with' clause and look for another.");
//! if t=pen_type then
//!   help_line[1]:="Next time say `withpen <known pen expression>';";
//! put_get_flush_error(0);
//! end
//!
//! @ @<Check the tentative weight@>=
//! begin cur_exp:=round_unscaled(cur_exp);
//! if (abs(cur_exp)<4)and(cur_exp<>0) then result:=true
//! else  begin print_err("Weight must be -3, -2, -1, +1, +2, or +3");
//! @.Weight must be...@>
//!   help1("I'll ignore the bad `with' clause and look for another.");
//!   put_get_flush_error(0);
//!   end;
//! end
//!
//! @ One of the things we need to do when we've parsed an \&{addto} or
//! similar command is set |cur_edges| to the header of a supposed \&{picture}
//! variable, given a token list for that variable.
//!
//! @<Declare action procedures for use by |do_statement|@>=
//! procedure find_edges_var(@!t:pointer);
//! var @!p:pointer;
//! begin p:=find_variable(t); cur_edges:=null;
//! if p=null then
//!   begin obliterated(t); put_get_error;
//!   end
//! else if type(p)<>picture_type then
//!   begin print_err("Variable "); show_token_list(t,null,1000,0);
//! @.Variable x is the wrong type@>
//!   print(" is the wrong type ("); print_type(type(p)); print_char(")");
//!   help2("I was looking for a ""known"" picture variable.")@/
//!     ("So I'll not change anything just now."); put_get_error;
//!   end
//! else cur_edges:=value(p);
//! flush_node_list(t);
//! end;
//!
//! @ @<Cases of |do_statement|...@>=
//! add_to_command: do_add_to;
//!
//! @ @<Declare action procedures for use by |do_statement|@>=
//! procedure do_add_to;
//! label done, not_found;
//! var @!lhs,@!rhs:pointer; {variable on left, path on right}
//! @!w:integer; {tentative weight}
//! @!p:pointer; {list manipulation register}
//! @!q:pointer; {beginning of second half of doubled path}
//! @!add_to_type:double_path_code..also_code; {modifier of \&{addto}}
//! begin get_x_next; var_flag:=thing_to_add; scan_primary;
//! if cur_type<>token_list then
//!   @<Abandon edges command because there's no variable@>
//! else  begin lhs:=cur_exp; add_to_type:=cur_mod;@/
//!   cur_type:=vacuous; get_x_next; scan_expression;
//!   if add_to_type=also_code then @<Augment some edges by others@>
//!   else @<Get ready to fill a contour, and fill it@>;
//!   end;
//! end;
//!
//! @ @<Abandon edges command because there's no variable@>=
//! begin exp_err("Not a suitable variable");
//! @.Not a suitable variable@>
//! help4("At this point I needed to see the name of a picture variable.")@/
//!   ("(Or perhaps you have indeed presented me with one; I might")@/
//!   ("have missed it, if it wasn't followed by the proper token.)")@/
//!   ("So I'll not change anything just now.");
//! put_get_flush_error(0);
//! end
//!
//! @ @<Augment some edges by others@>=
//! begin find_edges_var(lhs);
//! if cur_edges=null then flush_cur_exp(0)
//! else if cur_type<>picture_type then
//!   begin exp_err("Improper `addto'");
//! @.Improper `addto'@>
//!   help2("This expression should have specified a known picture.")@/
//!     ("So I'll not change anything just now."); put_get_flush_error(0);
//!   end
//! else  begin merge_edges(cur_exp); flush_cur_exp(0);
//!   end;
//! end
//!
//! @ @<Get ready to fill a contour...@>=
//! begin if cur_type=pair_type then pair_to_path;
//! if cur_type<>path_type then
//!   begin exp_err("Improper `addto'");
//! @.Improper `addto'@>
//!   help2("This expression should have been a known path.")@/
//!     ("So I'll not change anything just now.");
//!   put_get_flush_error(0); flush_token_list(lhs);
//!   end
//! else  begin rhs:=cur_exp; w:=1; cur_pen:=null_pen;
//!   while cur_cmd=with_option do
//!     if scan_with then
//!       if cur_type=known then w:=cur_exp
//!       else @<Change the tentative pen@>;
//!   @<Complete the contour filling operation@>;
//!   delete_pen_ref(cur_pen);
//!   end;
//! end
//!
//! @ We could say `|add_pen_ref(cur_pen)|; |flush_cur_exp(0)|' after changing
//! |cur_pen| here.  But that would have no effect, because the current expression
//! will not be flushed. Thus we save a bit of code (at the risk of being too
//! tricky).
//!
//! @<Change the tentative pen@>=
//! begin delete_pen_ref(cur_pen); cur_pen:=cur_exp;
//! end
//!
//! @ @<Complete the contour filling...@>=
//! find_edges_var(lhs);
//! if cur_edges=null then toss_knot_list(rhs)
//! else  begin lhs:=null; cur_path_type:=add_to_type;
//!   if left_type(rhs)=endpoint then
//!     if cur_path_type=double_path_code then @<Double the path@>
//!     else @<Complain about non-cycle and |goto not_found|@>
//!   else if cur_path_type=double_path_code then lhs:=htap_ypoc(rhs);
//!   cur_wt:=w; rhs:=make_spec(rhs,max_offset(cur_pen),internal[tracing_specs]);
//!   @<Check the turning number@>;
//!   if max_offset(cur_pen)=0 then fill_spec(rhs)
//!   else fill_envelope(rhs);
//!   if lhs<>null then
//!     begin rev_turns:=true;
//!     lhs:=make_spec(lhs,max_offset(cur_pen),internal[tracing_specs]);
//!     rev_turns:=false;
//!     if max_offset(cur_pen)=0 then fill_spec(lhs)
//!     else fill_envelope(lhs);
//!     end;
//! not_found: end
//!
//! @ @<Double the path@>=
//! if link(rhs)=rhs then @<Make a trivial one-point path cycle@>
//! else  begin p:=htap_ypoc(rhs); q:=link(p);@/
//!   right_x(path_tail):=right_x(q); right_y(path_tail):=right_y(q);
//!   right_type(path_tail):=right_type(q);
//!   link(path_tail):=link(q); free_node(q,knot_node_size);@/
//!   right_x(p):=right_x(rhs); right_y(p):=right_y(rhs);
//!   right_type(p):=right_type(rhs);
//!   link(p):=link(rhs); free_node(rhs,knot_node_size);@/
//!   rhs:=p;
//!   end
//!
//! @ @<Make a trivial one-point path cycle@>=
//! begin right_x(rhs):=x_coord(rhs); right_y(rhs):=y_coord(rhs);
//! left_x(rhs):=x_coord(rhs); left_y(rhs):=y_coord(rhs);
//! left_type(rhs):=explicit; right_type(rhs):=explicit;
//! end
//!
//! @ @<Complain about non-cycle...@>=
//! begin print_err("Not a cycle");
//! @.Not a cycle@>
//! help2("That contour should have ended with `..cycle' or `&cycle'.")@/
//!   ("So I'll not change anything just now."); put_get_error;
//! toss_knot_list(rhs); goto not_found;
//! end
//!
//! @ @<Check the turning number@>=
//! if turning_number<=0 then
//!  if cur_path_type<>double_path_code then if internal[turning_check]>0 then
//!   if (turning_number<0)and(link(cur_pen)=null) then negate(cur_wt)
//!   else  begin if turning_number=0 then
//!       if (internal[turning_check]<=unity)and(link(cur_pen)=null) then goto done
//!       else print_strange("Strange path (turning number is zero)")
//! @.Strange path...@>
//!     else print_strange("Backwards path (turning number is negative)");
//! @.Backwards path...@>
//!     help3("The path doesn't have a counterclockwise orientation,")@/
//!       ("so I'll probably have trouble drawing it.")@/
//!       ("(See Chapter 27 of The METAFONTbook for more help.)");
//! @:METAFONTbook}{\sl The {\logos METAFONT\/}book@>
//!     put_get_error;
//!     end;
//! done:
//!
//! @ @<Cases of |do_statement|...@>=
//! ship_out_command: do_ship_out;
//! display_command: do_display;
//! open_window: do_open_window;
//! cull_command: do_cull;
//!
//! @ @<Declare action procedures for use by |do_statement|@>=
//! @t\4@>@<Declare the function called |tfm_check|@>@;
//! procedure do_ship_out;
//! label exit;
//! var @!c:integer; {the character code}
//! begin get_x_next; var_flag:=semicolon; scan_expression;
//! if cur_type<>token_list then
//!   if cur_type=picture_type then cur_edges:=cur_exp
//!   else  begin @<Abandon edges command because there's no variable@>;
//!     return;
//!     end
//! else  begin find_edges_var(cur_exp); cur_type:=vacuous;
//!   end;
//! if cur_edges<>null then
//!   begin c:=round_unscaled(internal[char_code]) mod 256;
//!   if c<0 then c:=c+256;
//!   @<Store the width information for character code~|c|@>;
//!   if internal[proofing]>=0 then ship_out(c);
//!   end;
//! flush_cur_exp(0);
//! exit:end;
//!
//! @ @<Declare action procedures for use by |do_statement|@>=
//! procedure do_display;
//! label not_found,common_ending,exit;
//! var @!e:pointer; {token list for a picture variable}
//! begin get_x_next; var_flag:=in_window; scan_primary;
//! if cur_type<>token_list then
//!   @<Abandon edges command because there's no variable@>
//! else  begin e:=cur_exp; cur_type:=vacuous;
//!   get_x_next; scan_expression;
//!   if cur_type<>known then goto common_ending;
//!   cur_exp:=round_unscaled(cur_exp);
//!   if cur_exp<0 then goto not_found;
//!   if cur_exp>15 then goto not_found;
//!   if not window_open[cur_exp] then goto not_found;
//!   find_edges_var(e);
//!   if cur_edges<>null then disp_edges(cur_exp);
//!   return;
//!  not_found: cur_exp:=cur_exp*unity;
//!  common_ending: exp_err("Bad window number");
//! @.Bad window number@>
//!   help1("It should be the number of an open window.");
//!   put_get_flush_error(0); flush_token_list(e);
//!   end;
//! exit:end;
//!
//! @ The only thing difficult about `\&{openwindow}' is that the syntax
//! allows the user to go astray in many ways. The following subroutine
//! helps keep the necessary program reasonably short and sweet.
//!
//! @<Declare action procedures for use by |do_statement|@>=
//! function get_pair(@!c:command_code):boolean;
//! var @!p:pointer; {a pair of values that are known (we hope)}
//! @!b:boolean; {did we find such a pair?}
//! begin if cur_cmd<>c then get_pair:=false
//! else  begin get_x_next; scan_expression;
//!   if nice_pair(cur_exp,cur_type) then
//!     begin p:=value(cur_exp);
//!     cur_x:=value(x_part_loc(p)); cur_y:=value(y_part_loc(p));
//!     b:=true;
//!     end
//!   else b:=false;
//!   flush_cur_exp(0); get_pair:=b;
//!   end;
//! end;
//!
//! @ @<Declare action procedures for use by |do_statement|@>=
//! procedure do_open_window;
//! label not_found,exit;
//! var @!k:integer; {the window number in question}
//! @!r0,@!c0,@!r1,@!c1:scaled; {window coordinates}
//! begin get_x_next; scan_expression;
//! if cur_type<>known then goto not_found;
//! k:=round_unscaled(cur_exp);
//! if k<0 then goto not_found;
//! if k>15 then goto not_found;
//! if not get_pair(from_token) then goto not_found;
//! r0:=cur_x; c0:=cur_y;
//! if not get_pair(to_token) then goto not_found;
//! r1:=cur_x; c1:=cur_y;
//! if not get_pair(at_token) then goto not_found;
//! open_a_window(k,r0,c0,r1,c1,cur_x,cur_y); return;
//! not_found:print_err("Improper `openwindow'");
//! @.Improper `openwindow'@>
//! help2("Say `openwindow k from (r0,c0) to (r1,c1) at (x,y)',")@/
//!   ("where all quantities are known and k is between 0 and 15.");
//! put_get_error;
//! exit:end;
//!
//! @ @<Declare action procedures for use by |do_statement|@>=
//! procedure do_cull;
//! label not_found,exit;
//! var @!e:pointer; {token list for a picture variable}
//! @!keeping:drop_code..keep_code; {modifier of |cull_op|}
//! @!w,@!w_in,@!w_out:integer; {culling weights}
//! begin w:=1;
//! get_x_next; var_flag:=cull_op; scan_primary;
//! if cur_type<>token_list then
//!   @<Abandon edges command because there's no variable@>
//! else  begin e:=cur_exp; cur_type:=vacuous; keeping:=cur_mod;
//!   if not get_pair(cull_op) then goto not_found;
//!   while (cur_cmd=with_option)and(cur_mod=known) do
//!     if scan_with then w:=cur_exp;
//!   @<Set up the culling weights,
//!     or |goto not_found| if the thresholds are bad@>;
//!   find_edges_var(e);
//!   if cur_edges<>null then
//!     cull_edges(floor_unscaled(cur_x+unity-1),floor_unscaled(cur_y),w_out,w_in);
//!   return;
//!  not_found: print_err("Bad culling amounts");
//! @.Bad culling amounts@>
//!   help1("Always cull by known amounts that exclude 0.");
//!   put_get_error; flush_token_list(e);
//!   end;
//! exit:end;
//!
//! @ @<Set up the culling weights, or |goto not_found| if the thresholds are bad@>=
//! if cur_x>cur_y then goto not_found;
//! if keeping=drop_code then
//!   begin if (cur_x>0)or(cur_y<0) then goto not_found;
//!   w_out:=w; w_in:=0;
//!   end
//! else  begin if (cur_x<=0)and(cur_y>=0) then goto not_found;
//!   w_out:=0; w_in:=w;
//!   end
//!
//! @ The \&{everyjob} command simply assigns a nonzero value to the global variable
//! |start_sym|.
//!
//! @<Cases of |do_statement|...@>=
//! every_job_command: begin get_symbol; start_sym:=cur_sym; get_x_next;
//!   end;
//!
