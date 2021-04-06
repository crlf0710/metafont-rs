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
