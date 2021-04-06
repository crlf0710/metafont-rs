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
