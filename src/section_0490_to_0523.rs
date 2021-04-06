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
