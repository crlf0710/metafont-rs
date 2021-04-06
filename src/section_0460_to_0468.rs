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
