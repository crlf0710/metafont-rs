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
