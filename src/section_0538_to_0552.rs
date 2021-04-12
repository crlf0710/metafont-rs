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
