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
