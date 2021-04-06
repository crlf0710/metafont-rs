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
