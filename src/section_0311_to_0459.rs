//! @ The |make_moves| subroutine is given |scaled| values $(x_0,x_1,x_2,x_3)$
//! and $(y_0,y_1,y_2,y_3)$ that represent monotone-nondecreasing polynomials;
//! it makes $\lfloor x_3+\xi\rfloor-\lfloor x_0+\xi\rfloor$ rightward moves
//! and $\lfloor y_3+\eta\rfloor-\lfloor y_0+\eta\rfloor$ upward moves, as
//! explained earlier.  (Here $\lfloor x+\xi\rfloor$ actually stands for
//! $\lfloor x/2^{16}-|xi_corr|\rfloor$, if $x$ is regarded as an integer
//! without scaling.) The unscaled integers $x_k$ and~$y_k$ should be less
//! than $2^{28}$ in magnitude.
//!
//! It is assumed that $|move_ptr| + \lfloor y_3+\eta\rfloor -
//! \lfloor y_0+\eta\rfloor < |move_size|$ when this procedure is called,
//! so that the capacity of the |move| array will not be exceeded.
//!
//! The variables |r| and |s| in this procedure stand respectively for
//! $R-|xi_corr|$ and $S-|eta_corr|$ in the theory discussed above.
//!
//! @p procedure make_moves(@!xx0,@!xx1,@!xx2,@!xx3,@!yy0,@!yy1,@!yy2,@!yy3:
//!   scaled;@!xi_corr,@!eta_corr:small_number);
//! label continue, done, exit;
//! var @!x1,@!x2,@!x3,@!m,@!r,@!y1,@!y2,@!y3,@!n,@!s,@!l:integer;
//!   {bisection variables explained above}
//! @!q,@!t,@!u,@!x2a,@!x3a,@!y2a,@!y3a:integer; {additional temporary registers}
//! begin if (xx3<xx0)or(yy3<yy0) then confusion("m");
//! @:this can't happen m}{\quad m@>
//! l:=16; bisect_ptr:=0;@/
//! x1:=xx1-xx0; x2:=xx2-xx1; x3:=xx3-xx2;
//! if xx0>=xi_corr then r:=(xx0-xi_corr) mod unity
//! else r:=unity-1-((-xx0+xi_corr-1) mod unity);
//! m:=(xx3-xx0+r) div unity;@/
//! y1:=yy1-yy0; y2:=yy2-yy1; y3:=yy3-yy2;
//! if yy0>=eta_corr then s:=(yy0-eta_corr) mod unity
//! else s:=unity-1-((-yy0+eta_corr-1) mod unity);
//! n:=(yy3-yy0+s) div unity;@/
//! if (xx3-xx0>=fraction_one)or(yy3-yy0>=fraction_one) then
//!   @<Divide the variables by two, to avoid overflow problems@>;
//! loop@+  begin continue:@<Make moves for current subinterval;
//!     if bisection is necessary, push the second subinterval
//!     onto the stack, and |goto continue| in order to handle
//!     the first subinterval@>;
//!   if bisect_ptr=0 then return;
//!   @<Remove a subproblem for |make_moves| from the stack@>;
//!   end;
//! exit: end;
//!
//! @ @<Remove a subproblem for |make_moves| from the stack@>=
//! bisect_ptr:=bisect_ptr-move_increment;@/
//! x1:=stack_x1; x2:=stack_x2; x3:=stack_x3; r:=stack_r; m:=stack_m;@/
//! y1:=stack_y1; y2:=stack_y2; y3:=stack_y3; s:=stack_s; n:=stack_n;@/
//! l:=stack_l
//!
//! @ Our variables |(x1,x2,x3)| correspond to $(X_1,X_2,X_3)$ in the notation
//! of the theory developed above. We need to keep them less than $2^{28}$
//! in order to avoid integer overflow in weird circumstances.
//! For example, data like $x_0=-2^{28}+2^{16}-1$ and $x_1=x_2=x_3=2^{28}-1$
//! would otherwise be problematical. Hence this part of the code is
//! needed, if only to thwart malicious users.
//!
//! @<Divide the variables by two, to avoid overflow problems@>=
//! begin x1:=half(x1+xi_corr); x2:=half(x2+xi_corr); x3:=half(x3+xi_corr);
//! r:=half(r+xi_corr);@/
//! y1:=half(y1+eta_corr); y2:=half(y2+eta_corr); y3:=half(y3+eta_corr);
//! s:=half(s+eta_corr);@/
//! l:=15;
//! end
//!
//! @ @<Make moves...@>=
//! if m=0 then @<Move upward |n| steps@>
//! else if n=0 then @<Move to the right |m| steps@>
//! else if m+n=2 then @<Make one move of each kind@>
//! else  begin incr(l); stack_l:=l;@/
//!   stack_x3:=x3; stack_x2:=half(x2+x3+xi_corr); x2:=half(x1+x2+xi_corr);
//!   x3:=half(x2+stack_x2+xi_corr); stack_x1:=x3;@/
//!   r:=r+r+xi_corr; t:=x1+x2+x3+r;@/
//!   q:=t div two_to_the[l]; stack_r:=t mod two_to_the[l];@/
//!   stack_m:=m-q; m:=q;@/
//!   stack_y3:=y3; stack_y2:=half(y2+y3+eta_corr); y2:=half(y1+y2+eta_corr);
//!   y3:=half(y2+stack_y2+eta_corr); stack_y1:=y3;@/
//!   s:=s+s+eta_corr; u:=y1+y2+y3+s;@/
//!   q:=u div two_to_the[l]; stack_s:=u mod two_to_the[l];@/
//!   stack_n:=n-q; n:=q;@/
//!   bisect_ptr:=bisect_ptr+move_increment; goto continue;
//!   end
//!
//! @ @<Move upward |n| steps@>=
//! while n>0 do
//!   begin incr(move_ptr); move[move_ptr]:=1; decr(n);
//!   end
//!
//! @ @<Move to the right |m| steps@>=
//! move[move_ptr]:=move[move_ptr]+m
//!
//! @ @<Make one move of each kind@>=
//! begin r:=two_to_the[l]-r; s:=two_to_the[l]-s;@/
//! while l<30 do
//!   begin x3a:=x3; x2a:=half(x2+x3+xi_corr); x2:=half(x1+x2+xi_corr);
//!   x3:=half(x2+x2a+xi_corr);
//!   t:=x1+x2+x3; r:=r+r-xi_corr;@/
//!   y3a:=y3; y2a:=half(y2+y3+eta_corr); y2:=half(y1+y2+eta_corr);
//!   y3:=half(y2+y2a+eta_corr);
//!   u:=y1+y2+y3; s:=s+s-eta_corr;@/
//!   if t<r then if u<s then @<Switch to the right subinterval@>
//!     else  begin @<Move up then right@>; goto done;
//!       end
//!   else if u<s then
//!     begin @<Move right then up@>; goto done;
//!     end;
//!   incr(l);
//!   end;
//! r:=r-xi_corr; s:=s-eta_corr;
//! if ab_vs_cd(x1+x2+x3,s,y1+y2+y3,r)-xi_corr>=0 then @<Move right then up@>
//!   else @<Move up then right@>;
//! done:
//! end
//!
//! @ @<Switch to the right subinterval@>=
//! begin x1:=x3; x2:=x2a; x3:=x3a; r:=r-t;
//! y1:=y3; y2:=y2a; y3:=y3a; s:=s-u;
//! end
//!
//! @ @<Move right then up@>=
//! begin incr(move[move_ptr]); incr(move_ptr); move[move_ptr]:=1;
//! end
//!
//! @ @<Move up then right@>=
//! begin incr(move_ptr); move[move_ptr]:=2;
//! end
//!
//! @ After |make_moves| has acted, possibly for several curves that move toward
//! the same octant, a ``smoothing'' operation might be done on the |move| array.
//! This removes optical glitches that can arise even when the curve has been
//! digitized without rounding errors.
//!
//! The smoothing process replaces the integers $a_0\ldots a_n$ in
//! |move[b..t]| by ``smoothed'' integers $a_0'\ldots a_n'$ defined as
//! follows:
//! $$a_k'=a_k+\delta\k-\delta_k;\qquad
//! \delta_k=\cases{+1,&if $1<k<n$ and $a_{k-2}\G a_{k-1}\ll a_k\G a\k$;\cr
//! -1,&if $1<k<n$ and $a_{k-2}\L a_{k-1}\gg a_k\L a\k$;\cr
//! 0,&otherwise.\cr}$$
//! Here $a\ll b$ means that $a\L b-2$, and $a\gg b$ means that $a\G b+2$.
//!
//! The smoothing operation is symmetric in the sense that, if $a_0\ldots a_n$
//! smooths to $a_0'\ldots a_n'$, then the reverse sequence $a_n\ldots a_0$
//! smooths to $a_n'\ldots a_0'$; also the complementary sequence
//! $(m-a_0)\ldots(m-a_n)$ smooths to $(m-a_0')\ldots(m-a_n')$.
//! We have $a_0'+\cdots+a_n'=a_0+\cdots+a_n$ because $\delta_0=\delta_{n+1}=0$.
//!
//! @p procedure smooth_moves(@!b,@!t:integer);
//! var@!k:1..move_size; {index into |move|}
//! @!a,@!aa,@!aaa:integer; {original values of |move[k],move[k-1],move[k-2]|}
//! begin if t-b>=3 then
//!   begin k:=b+2; aa:=move[k-1]; aaa:=move[k-2];
//!   repeat a:=move[k];
//!   if abs(a-aa)>1 then
//!     @<Increase and decrease |move[k-1]| and |move[k]| by $\delta_k$@>;
//!   incr(k); aaa:=aa; aa:=a;
//!   until k=t;
//!   end;
//! end;
//!
//! @ @<Increase and decrease |move[k-1]| and |move[k]| by $\delta_k$@>=
//! if a>aa then
//!   begin if aaa>=aa then if a>=move[k+1] then
//!     begin incr(move[k-1]); move[k]:=a-1;
//!     end;
//!   end
//! else  begin if aaa<=aa then if a<=move[k+1] then
//!     begin decr(move[k-1]); move[k]:=a+1;
//!     end;
//!   end
//!
//! @* \[20] Edge structures.
//! Now we come to \MF's internal scheme for representing what the user can
//! actually ``see,'' the edges between pixels. Each pixel has an integer
//! weight, obtained by summing the weights on all edges to its left. \MF\
//! represents only the nonzero edge weights, since most of the edges are
//! weightless; in this way, the data storage requirements grow only linearly
//! with respect to the number of pixels per point, even though two-dimensional
//! data is being represented. (Well, the actual dependence on the underlying
//! resolution is order $n\log n$, but the $\log n$ factor is buried in our
//! implicit restriction on the maximum raster size.) The sum of all edge
//! weights in each row should be zero.
//!
//! The data structure for edge weights must be compact and flexible,
//! yet it should support efficient updating and display operations. We
//! want to be able to have many different edge structures in memory at
//! once, and we want the computer to be able to translate them, reflect them,
//! and/or merge them together with relative ease.
//!
//! \MF's solution to this problem requires one single-word node per
//! nonzero edge weight, plus one two-word node for each row in a contiguous
//! set of rows. There's also a header node that provides global information
//! about the entire structure.
//!
//! @ Let's consider the edge-weight nodes first. The |info| field of such
//! nodes contains both an $m$~value and a weight~$w$, in the form
//! $8m+w+c$, where $c$ is a constant that depends on data found in the header.
//! We shall consider $c$ in detail later; for now, it's best just to think
//! of it as a way to compensate for the fact that $m$ and~$w$ can be negative,
//! together with the fact that an |info| field must have a value between
//! |min_halfword| and |max_halfword|. The $m$ value is an unscaled $x$~coordinate,
//! so it satisfies $\vert m\vert<
//! 4096$; the $w$ value is always in the range $1\L\vert w\vert\L3$. We can
//! unpack the data in the |info| field by fetching |ho(info(p))=
//! info(p)-min_halfword| and dividing this nonnegative number by~8;
//! the constant~$c$ will be chosen so that the remainder of this division
//! is $4+w$. Thus, for example, a remainder of~3 will correspond to
//! the edge weight $w=-1$.
//!
//! Every row of an edge structure contains two lists of such edge-weight
//! nodes, called the |sorted| and |unsorted| lists, linked together by their
//! |link| fields in the normal way. The difference between them is that we
//! always have |info(p)<=info(link(p))| in the |sorted| list, but there's no
//! such restriction on the elements of the |unsorted| list. The reason for
//! this distinction is that it would take unnecessarily long to maintain
//! edge-weight lists in sorted order while they're being updated; but when we
//! need to process an entire row from left to right in order of the
//! $m$~values, it's fairly easy and quick to sort a short list of unsorted
//! elements and to merge them into place among their sorted cohorts.
//! Furthermore, the fact that the |unsorted| list is empty can sometimes be
//! used to good advantage, because it allows us to conclude that a particular
//! row has not changed since the last time we sorted it.
//!
//! The final |link| of the |sorted| list will be |sentinel|, which points to
//! a special one-word node whose |info| field is essentially infinite; this
//! facilitates the sorting and merging operations. The final |link| of the
//! |unsorted| list will be either |null| or |void|, where |void=null+1|
//! is used to avoid redisplaying data that has not changed:
//! A |void| value is stored at the head of the
//! unsorted list whenever the corresponding row has been displayed.
//!
//! @d zero_w=4
//! @d void==null+1
//!
//! @<Initialize table entries...@>=
//! info(sentinel):=max_halfword; {|link(sentinel)=null|}
//!
//! @ The rows themselves are represented by row header nodes that
//! contain four link fields. Two of these four, |sorted| and |unsorted|,
//! point to the first items of the edge-weight lists just mentioned.
//! The other two, |link| and |knil|, point to the headers of the two
//! adjacent rows. If |p| points to the header for row number~|n|, then
//! |link(p)| points up to the header for row~|n+1|, and |knil(p)| points
//! down to the header for row~|n-1|. This double linking makes it
//! convenient to move through consecutive rows either upward or downward;
//! as usual, we have |link(knil(p))=knil(link(p))=p| for all row headers~|p|.
//!
//! The row associated with a given value of |n| contains weights for
//! edges that run between the lattice points |(m,n)| and |(m,n+1)|.
//!
//! @d knil==info {inverse of the |link| field, in a doubly linked list}
//! @d sorted_loc(#)==#+1 {where the |sorted| link field resides}
//! @d sorted(#)==link(sorted_loc(#)) {beginning of the list of sorted edge weights}
//! @d unsorted(#)==info(#+1) {beginning of the list of unsorted edge weights}
//! @d row_node_size=2 {number of words in a row header node}
//!
//! @ The main header node |h| for an edge structure has |link| and |knil|
//! fields that link it above the topmost row and below the bottommost row.
//! It also has fields called |m_min|, |m_max|, |n_min|, and |n_max| that
//! bound the current extent of the edge data: All |m| values in edge-weight
//! nodes should lie between |m_min(h)-4096| and |m_max(h)-4096|, inclusive.
//! Furthermore the topmost row header, pointed to by |knil(h)|,
//! is for row number |n_max(h)-4096|; the bottommost row header, pointed to by
//! |link(h)|, is for row number |n_min(h)-4096|.
//!
//! The offset constant |c| that's used in all of the edge-weight data is
//! represented implicitly in |m_offset(h)|; its actual value is
//! $$\hbox{|c=min_halfword+zero_w+8*m_offset(h)|.}$$
//! Notice that it's possible to shift an entire edge structure by an
//! amount $(\Delta m,\Delta n)$ by adding $\Delta n$ to |n_min(h)| and |n_max(h)|,
//! adding $\Delta m$ to |m_min(h)| and |m_max(h)|, and subtracting
//! $\Delta m$ from |m_offset(h)|;
//! none of the other edge data needs to be modified. Initially the |m_offset|
//! field is~4096, but it will change if the user requests such a shift.
//! The contents of these five fields should always be positive and less than
//! 8192; |n_max| should, in fact, be less than 8191.  Furthermore
//! |m_min+m_offset-4096| and |m_max+m_offset-4096| must also lie strictly
//! between 0 and 8192, so that the |info| fields of edge-weight nodes will
//! fit in a halfword.
//!
//! The header node of an edge structure also contains two somewhat unusual
//! fields that are called |last_window(h)| and |last_window_time(h)|. When this
//! structure is displayed in window~|k| of the user's screen, after that
//! window has been updated |t| times, \MF\ sets |last_window(h):=k| and
//! |last_window_time(h):=t|; it also sets |unsorted(p):=void| for all row
//! headers~|p|, after merging any existing unsorted weights with the sorted
//! ones.  A subsequent display in the same window will be able to avoid
//! redisplaying rows whose |unsorted| list is still |void|, if the window
//! hasn't been used for something else in the meantime.
//!
//! A pointer to the row header of row |n_pos(h)-4096| is provided in
//! |n_rover(h)|. Most of the algorithms that update an edge structure
//! are able to get by without random row references; they usually
//! access rows that are neighbors of each other or of the current |n_pos| row.
//! Exception: If |link(h)=h| (so that the edge structure contains
//! no rows), we have |n_rover(h)=h|, and |n_pos(h)| is irrelevant.
//!
//! @d zero_field=4096 {amount added to coordinates to make them positive}
//! @d n_min(#)==info(#+1) {minimum row number present, plus |zero_field|}
//! @d n_max(#)==link(#+1) {maximum row number present, plus |zero_field|}
//! @d m_min(#)==info(#+2) {minimum column number present, plus |zero_field|}
//! @d m_max(#)==link(#+2) {maximum column number present, plus |zero_field|}
//! @d m_offset(#)==info(#+3) {translation of $m$ data in edge-weight nodes}
//! @d last_window(#)==link(#+3) {the last display went into this window}
//! @d last_window_time(#)==mem[#+4].int {after this many window updates}
//! @d n_pos(#)==info(#+5) {the row currently in |n_rover|, plus |zero_field|}
//! @d n_rover(#)==link(#+5) {a row recently referenced}
//! @d edge_header_size=6 {number of words in an edge-structure header}
//! @d valid_range(#)==(abs(#-4096)<4096) {is |#| strictly between 0 and 8192?}
//! @d empty_edges(#)==link(#)=# {are there no rows in this edge header?}
//!
//! @p procedure init_edges(@!h:pointer); {initialize an edge header to null values}
//! begin knil(h):=h; link(h):=h;@/
//! n_min(h):=zero_field+4095; n_max(h):=zero_field-4095;
//! m_min(h):=zero_field+4095; m_max(h):=zero_field-4095;
//! m_offset(h):=zero_field;@/
//! last_window(h):=0; last_window_time(h):=0;@/
//! n_rover(h):=h; n_pos(h):=0;@/
//! end;
//!
//! @ When a lot of work is being done on a particular edge structure, we plant
//! a pointer to its main header in the global variable |cur_edges|.
//! This saves us from having to pass this pointer as a parameter over and
//! over again between subroutines.
//!
//! Similarly, |cur_wt| is a global weight that is being used by several
//! procedures at once.
//!
//! @<Glob...@>=
//! @!cur_edges:pointer; {the edge structure of current interest}
//! @!cur_wt:integer; {the edge weight of current interest}
//!
//! @ The |fix_offset| routine goes through all the edge-weight nodes of
//! |cur_edges| and adds a constant to their |info| fields, so that
//! |m_offset(cur_edges)| can be brought back to |zero_field|. (This
//! is necessary only in unusual cases when the offset has gotten too
//! large or too small.)
//!
//! @p procedure fix_offset;
//! var @!p,@!q:pointer; {list traversers}
//! @!delta:integer; {the amount of change}
//! begin delta:=8*(m_offset(cur_edges)-zero_field);
//! m_offset(cur_edges):=zero_field;
//! q:=link(cur_edges);
//! while q<>cur_edges do
//!   begin p:=sorted(q);
//!   while p<>sentinel do
//!     begin info(p):=info(p)-delta; p:=link(p);
//!     end;
//!   p:=unsorted(q);
//!   while p>void do
//!     begin info(p):=info(p)-delta; p:=link(p);
//!     end;
//!   q:=link(q);
//!   end;
//! end;
//!
//! @ The |edge_prep| routine makes the |cur_edges| structure ready to
//! accept new data whose coordinates satisfy |ml<=m<=mr| and |nl<=n<=nr-1|,
//! assuming that |-4096<ml<=mr<4096| and |-4096<nl<=nr<4096|. It makes
//! appropriate adjustments to |m_min|, |m_max|, |n_min|, and |n_max|,
//! adding new empty rows if necessary.
//!
//! @p procedure edge_prep(@!ml,@!mr,@!nl,@!nr:integer);
//! var @!delta:halfword; {amount of change}
//! @!p,@!q:pointer; {for list manipulation}
//! begin ml:=ml+zero_field; mr:=mr+zero_field;
//! nl:=nl+zero_field; nr:=nr-1+zero_field;@/
//! if ml<m_min(cur_edges) then m_min(cur_edges):=ml;
//! if mr>m_max(cur_edges) then m_max(cur_edges):=mr;
//! if not valid_range(m_min(cur_edges)+m_offset(cur_edges)-zero_field) or@|
//!  not valid_range(m_max(cur_edges)+m_offset(cur_edges)-zero_field) then
//!   fix_offset;
//! if empty_edges(cur_edges) then {there are no rows}
//!   begin n_min(cur_edges):=nr+1; n_max(cur_edges):=nr;
//!   end;
//! if nl<n_min(cur_edges) then
//!   @<Insert exactly |n_min(cur_edges)-nl| empty rows at the bottom@>;
//! if nr>n_max(cur_edges) then
//!   @<Insert exactly |nr-n_max(cur_edges)| empty rows at the top@>;
//! end;
//!
//! @ @<Insert exactly |n_min(cur_edges)-nl| empty rows at the bottom@>=
//! begin delta:=n_min(cur_edges)-nl; n_min(cur_edges):=nl;
//! p:=link(cur_edges);
//! repeat q:=get_node(row_node_size); sorted(q):=sentinel; unsorted(q):=void;
//! knil(p):=q; link(q):=p; p:=q; decr(delta);
//! until delta=0;
//! knil(p):=cur_edges; link(cur_edges):=p;
//! if n_rover(cur_edges)=cur_edges then n_pos(cur_edges):=nl-1;
//! end
//!
//! @ @<Insert exactly |nr-n_max(cur_edges)| empty rows at the top@>=
//! begin delta:=nr-n_max(cur_edges); n_max(cur_edges):=nr;
//! p:=knil(cur_edges);
//! repeat q:=get_node(row_node_size); sorted(q):=sentinel; unsorted(q):=void;
//! link(p):=q; knil(q):=p; p:=q; decr(delta);
//! until delta=0;
//! link(p):=cur_edges; knil(cur_edges):=p;
//! if n_rover(cur_edges)=cur_edges then n_pos(cur_edges):=nr+1;
//! end
//!
//! @ The |print_edges| subroutine gives a symbolic rendition of an edge
//! structure, for use in `\&{show}' commands. A rather terse output
//! format has been chosen since edge structures can grow quite large.
//!
//! @<Declare subroutines for printing expressions@>=
//! @t\4@>@<Declare the procedure called |print_weight|@>@;@/
//! procedure print_edges(@!s:str_number;@!nuline:boolean;@!x_off,@!y_off:integer);
//! var @!p,@!q,@!r:pointer; {for list traversal}
//! @!n:integer; {row number}
//! begin print_diagnostic("Edge structure",s,nuline);
//! p:=knil(cur_edges); n:=n_max(cur_edges)-zero_field;
//! while p<>cur_edges do
//!   begin q:=unsorted(p); r:=sorted(p);
//!   if(q>void)or(r<>sentinel) then
//!     begin print_nl("row "); print_int(n+y_off); print_char(":");
//!     while q>void do
//!       begin print_weight(q,x_off); q:=link(q);
//!       end;
//!     print(" |");
//!     while r<>sentinel do
//!       begin print_weight(r,x_off); r:=link(r);
//!       end;
//!     end;
//!   p:=knil(p); decr(n);
//!   end;
//! end_diagnostic(true);
//! end;
//!
//! @ @<Declare the procedure called |print_weight|@>=
//! procedure print_weight(@!q:pointer;@!x_off:integer);
//! var @!w,@!m:integer; {unpacked weight and coordinate}
//! @!d:integer; {temporary data register}
//! begin d:=ho(info(q)); w:=d mod 8; m:=(d div 8)-m_offset(cur_edges);
//! if file_offset>max_print_line-9 then print_nl(" ")
//! else print_char(" ");
//! print_int(m+x_off);
//! while w>zero_w do
//!   begin print_char("+"); decr(w);
//!   end;
//! while w<zero_w do
//!   begin print_char("-"); incr(w);
//!   end;
//! end;
//!
//! @ Here's a trivial subroutine that copies an edge structure. (Let's hope
//! that the given structure isn't too gigantic.)
//!
//! @p function copy_edges(@!h:pointer):pointer;
//! var @!p,@!r:pointer; {variables that traverse the given structure}
//! @!hh,@!pp,@!qq,@!rr,@!ss:pointer; {variables that traverse the new structure}
//! begin hh:=get_node(edge_header_size);
//! mem[hh+1]:=mem[h+1]; mem[hh+2]:=mem[h+2];
//! mem[hh+3]:=mem[h+3]; mem[hh+4]:=mem[h+4]; {we've now copied |n_min|, |n_max|,
//!   |m_min|, |m_max|, |m_offset|, |last_window|, and |last_window_time|}
//! n_pos(hh):=n_max(hh)+1;n_rover(hh):=hh;@/
//! p:=link(h); qq:=hh;
//! while p<>h do
//!   begin pp:=get_node(row_node_size); link(qq):=pp; knil(pp):=qq;
//!   @<Copy both |sorted| and |unsorted| lists of |p| to |pp|@>;
//!   p:=link(p); qq:=pp;
//!   end;
//! link(qq):=hh; knil(hh):=qq;
//! copy_edges:=hh;
//! end;
//!
//! @ @<Copy both |sorted| and |unsorted|...@>=
//! r:=sorted(p); rr:=sorted_loc(pp); {|link(rr)=sorted(pp)|}
//! while r<>sentinel do
//!   begin ss:=get_avail; link(rr):=ss; rr:=ss; info(rr):=info(r);@/
//!   r:=link(r);
//!   end;
//! link(rr):=sentinel;@/
//! r:=unsorted(p); rr:=temp_head;
//! while r>void do
//!   begin ss:=get_avail; link(rr):=ss; rr:=ss; info(rr):=info(r);@/
//!   r:=link(r);
//!   end;
//! link(rr):=r; unsorted(pp):=link(temp_head)
//!
//! @ Another trivial routine flips |cur_edges| about the |x|-axis
//! (i.e., negates all the |y| coordinates), assuming that at least
//! one row is present.
//!
//! @p procedure y_reflect_edges;
//! var @!p,@!q,@!r:pointer; {list manipulation registers}
//! begin p:=n_min(cur_edges);
//! n_min(cur_edges):=zero_field+zero_field-1-n_max(cur_edges);
//! n_max(cur_edges):=zero_field+zero_field-1-p;
//! n_pos(cur_edges):=zero_field+zero_field-1-n_pos(cur_edges);@/
//! p:=link(cur_edges); q:=cur_edges; {we assume that |p<>q|}
//! repeat r:=link(p); link(p):=q; knil(q):=p; q:=p; p:=r;
//! until q=cur_edges;
//! last_window_time(cur_edges):=0;
//! end;
//!
//! @ It's somewhat more difficult, yet not too hard, to reflect about the |y|-axis.
//!
//! @p procedure x_reflect_edges;
//! var @!p,@!q,@!r,@!s:pointer; {list manipulation registers}
//! @!m:integer; {|info| fields will be reflected with respect to this number}
//! begin p:=m_min(cur_edges);
//! m_min(cur_edges):=zero_field+zero_field-m_max(cur_edges);
//! m_max(cur_edges):=zero_field+zero_field-p;
//! m:=(zero_field+m_offset(cur_edges))*8+zero_w+min_halfword+zero_w+min_halfword;
//! m_offset(cur_edges):=zero_field;
//! p:=link(cur_edges);
//! repeat @<Reflect the edge-and-weight data in |sorted(p)|@>;
//! @<Reflect the edge-and-weight data in |unsorted(p)|@>;
//! p:=link(p);
//! until p=cur_edges;
//! last_window_time(cur_edges):=0;
//! end;
//!
//! @ We want to change the sign of the weight as we change the sign of the
//! |x|~coordinate. Fortunately, it's easier to do this than to negate
//! one without the other.
//!
//! @<Reflect the edge-and-weight data in |unsorted(p)|@>=
//! q:=unsorted(p);
//! while q>void do
//!   begin info(q):=m-info(q); q:=link(q);
//!   end
//!
//! @ Reversing the order of a linked list is best thought of as the process of
//! popping nodes off one stack and pushing them on another. In this case we
//! pop from stack~|q| and push to stack~|r|.
//!
//! @<Reflect the edge-and-weight data in |sorted(p)|@>=
//! q:=sorted(p); r:=sentinel;
//! while q<>sentinel do
//!   begin s:=link(q); link(q):=r; r:=q; info(r):=m-info(q); q:=s;
//!   end;
//! sorted(p):=r
//!
//! @ Now let's multiply all the $y$~coordinates of a nonempty edge structure
//! by a small integer $s>1$:
//!
//! @p procedure y_scale_edges(@!s:integer);
//! var @!p,@!q,@!pp,@!r,@!rr,@!ss:pointer; {list manipulation registers}
//! @!t:integer; {replication counter}
//! begin if (s*(n_max(cur_edges)+1-zero_field)>=4096) or@|
//!  (s*(n_min(cur_edges)-zero_field)<=-4096) then
//!   begin print_err("Scaled picture would be too big");
//! @.Scaled picture...big@>
//!   help3("I can't yscale the picture as requested---it would")@/
//!     ("make some coordinates too large or too small.")@/
//!     ("Proceed, and I'll omit the transformation.");
//!   put_get_error;
//!   end
//! else  begin n_max(cur_edges):=s*(n_max(cur_edges)+1-zero_field)-1+zero_field;
//!   n_min(cur_edges):=s*(n_min(cur_edges)-zero_field)+zero_field;
//!   @<Replicate every row exactly $s$ times@>;
//!   last_window_time(cur_edges):=0;
//!   end;
//! end;
//!
//! @ @<Replicate...@>=
//! p:=cur_edges;
//! repeat q:=p; p:=link(p);
//! for t:=2 to s do
//!   begin pp:=get_node(row_node_size); link(q):=pp; knil(p):=pp;
//!   link(pp):=p; knil(pp):=q; q:=pp;
//!   @<Copy both |sorted| and |unsorted|...@>;
//!   end;
//! until link(p)=cur_edges
//!
//! @ Scaling the $x$~coordinates is, of course, our next task.
//!
//! @p procedure x_scale_edges(@!s:integer);
//! var @!p,@!q:pointer; {list manipulation registers}
//! @!t:0..65535; {unpacked |info| field}
//! @!w:0..7; {unpacked weight}
//! @!delta:integer; {amount added to scaled |info|}
//! begin if (s*(m_max(cur_edges)-zero_field)>=4096) or@|
//!  (s*(m_min(cur_edges)-zero_field)<=-4096) then
//!   begin print_err("Scaled picture would be too big");
//! @.Scaled picture...big@>
//!   help3("I can't xscale the picture as requested---it would")@/
//!     ("make some coordinates too large or too small.")@/
//!     ("Proceed, and I'll omit the transformation.");
//!   put_get_error;
//!   end
//! else if (m_max(cur_edges)<>zero_field)or(m_min(cur_edges)<>zero_field) then
//!   begin m_max(cur_edges):=s*(m_max(cur_edges)-zero_field)+zero_field;
//!   m_min(cur_edges):=s*(m_min(cur_edges)-zero_field)+zero_field;
//!   delta:=8*(zero_field-s*m_offset(cur_edges))+min_halfword;
//!   m_offset(cur_edges):=zero_field;@/
//!   @<Scale the $x$~coordinates of each row by $s$@>;
//!   last_window_time(cur_edges):=0;
//!   end;
//! end;
//!
//! @ The multiplications cannot overflow because we know that |s<4096|.
//!
//! @<Scale the $x$~coordinates of each row by $s$@>=
//! q:=link(cur_edges);
//! repeat p:=sorted(q);
//! while p<>sentinel do
//!   begin t:=ho(info(p)); w:=t mod 8; info(p):=(t-w)*s+w+delta; p:=link(p);
//!   end;
//! p:=unsorted(q);
//! while p>void do
//!   begin t:=ho(info(p)); w:=t mod 8; info(p):=(t-w)*s+w+delta; p:=link(p);
//!   end;
//! q:=link(q);
//! until q=cur_edges
//!
//! @ Here is a routine that changes the signs of all the weights, without
//! changing anything else.
//!
//! @p procedure negate_edges(@!h:pointer);
//! label done;
//! var @!p,@!q,@!r,@!s,@!t,@!u:pointer; {structure traversers}
//! begin p:=link(h);
//! while p<>h do
//!   begin q:=unsorted(p);
//!   while q>void do
//!     begin info(q):=8-2*((ho(info(q))) mod 8)+info(q); q:=link(q);
//!     end;
//!   q:=sorted(p);
//!   if q<>sentinel then
//!     begin repeat info(q):=8-2*((ho(info(q))) mod 8)+info(q); q:=link(q);
//!     until q=sentinel;
//!     @<Put the list |sorted(p)| back into sort@>;
//!     end;
//!   p:=link(p);
//!   end;
//! last_window_time(h):=0;
//! end;
//!
//! @ \MF\ would work even if the code in this section were omitted, because
//! a list of edge-and-weight data that is sorted only by
//! |m| but not~|w| turns out to be good enough for correct operation.
//! However, the author decided not to make the program even trickier than
//! it is already, since |negate_edges| isn't needed very often.
//! The simpler-to-state condition, ``keep the |sorted| list fully sorted,''
//! is therefore being preserved at the cost of extra computation.
//!
//! @<Put the list |sorted(p)|...@>=
//! u:=sorted_loc(p); q:=link(u); r:=q; s:=link(r); {|q=sorted(p)|}
//! loop@+  if info(s)>info(r) then
//!     begin link(u):=q;
//!     if s=sentinel then goto done;
//!     u:=r; q:=s; r:=q; s:=link(r);
//!     end
//!   else  begin t:=s; s:=link(t); link(t):=q; q:=t;
//!     end;
//! done: link(r):=sentinel
//!
//! @ The |unsorted| edges of a row are merged into the |sorted| ones by
//! a subroutine called |sort_edges|. It uses simple insertion sort,
//! followed by a merge, because the unsorted list is supposedly quite short.
//! However, the unsorted list is assumed to be nonempty.
//!
//! @p procedure sort_edges(@!h:pointer); {|h| is a row header}
//! label done;
//! var @!k:halfword; {key register that we compare to |info(q)|}
//! @!p,@!q,@!r,@!s:pointer;
//! begin r:=unsorted(h); unsorted(h):=null;
//! p:=link(r); link(r):=sentinel; link(temp_head):=r;
//! while p>void do {sort node |p| into the list that starts at |temp_head|}
//!   begin k:=info(p); q:=temp_head;
//!   repeat r:=q; q:=link(r);
//!   until k<=info(q);
//!   link(r):=p; r:=link(p); link(p):=q; p:=r;
//!   end;
//! @<Merge the |temp_head| list into |sorted(h)|@>;
//! end;
//!
//! @ In this step we use the fact that |sorted(h)=link(sorted_loc(h))|.
//!
//! @<Merge the |temp_head| list into |sorted(h)|@>=
//! begin r:=sorted_loc(h); q:=link(r); p:=link(temp_head);
//! loop@+  begin k:=info(p);
//!   while k>info(q) do
//!     begin r:=q; q:=link(r);
//!     end;
//!   link(r):=p; s:=link(p); link(p):=q;
//!   if s=sentinel then goto done;
//!   r:=p; p:=s;
//!   end;
//! done:end
//!
//! @ The |cull_edges| procedure ``optimizes'' an edge structure by making all
//! the pixel weights either |w_out| or~|w_in|. The weight will be~|w_in| after the
//! operation if and only if it was in the closed interval |[w_lo,w_hi]|
//! before, where |w_lo<=w_hi|. Either |w_out| or |w_in| is zero, while the other is
//! $\pm1$, $\pm2$, or $\pm3$. The parameters will be such that zero-weight
//! pixels will remain of weight zero.  (This is fortunate,
//! because there are infinitely many of them.)
//!
//! The procedure also computes the tightest possible bounds on the resulting
//! data, by updating |m_min|, |m_max|, |n_min|, and~|n_max|.
//!
//! @p procedure cull_edges(@!w_lo,@!w_hi,@!w_out,@!w_in:integer);
//! label done;
//! var @!p,@!q,@!r,@!s:pointer; {for list manipulation}
//! @!w:integer; {new weight after culling}
//! @!d:integer; {data register for unpacking}
//! @!m:integer; {the previous column number, including |m_offset|}
//! @!mm:integer; {the next column number, including |m_offset|}
//! @!ww:integer; {accumulated weight before culling}
//! @!prev_w:integer; {value of |w| before column |m|}
//! @!n,@!min_n,@!max_n:pointer; {current and extreme row numbers}
//! @!min_d,@!max_d:pointer; {extremes of the new edge-and-weight data}
//! begin min_d:=max_halfword; max_d:=min_halfword;
//! min_n:=max_halfword; max_n:=min_halfword;@/
//! p:=link(cur_edges); n:=n_min(cur_edges);
//! while p<>cur_edges do
//!   begin if unsorted(p)>void then sort_edges(p);
//!   if sorted(p)<>sentinel then
//!     @<Cull superfluous edge-weight entries from |sorted(p)|@>;
//!   p:=link(p); incr(n);
//!   end;
//! @<Delete empty rows at the top and/or bottom;
//!   update the boundary values in the header@>;
//! last_window_time(cur_edges):=0;
//! end;
//!
//! @ The entire |sorted| list is returned to available memory in this step;
//! a new list is built starting (temporarily) at |temp_head|.
//! Since several edges can occur at the same column, we need to be looking
//! ahead of where the actual culling takes place. This means that it's
//! slightly tricky to get the iteration started and stopped.
//!
//! @<Cull superfluous...@>=
//! begin r:=temp_head; q:=sorted(p); ww:=0; m:=1000000; prev_w:=0;
//! loop@+  begin if q=sentinel then mm:=1000000
//!   else  begin d:=ho(info(q)); mm:=d div 8; ww:=ww+(d mod 8)-zero_w;
//!     end;
//!   if mm>m then
//!     begin @<Insert an edge-weight for edge |m|, if the new pixel
//!       weight has changed@>;
//!     if q=sentinel then goto done;
//!     end;
//!   m:=mm;
//!   if ww>=w_lo then if ww<=w_hi then w:=w_in
//!     else w:=w_out
//!   else w:=w_out;
//!   s:=link(q); free_avail(q); q:=s;
//!   end;
//! done: link(r):=sentinel; sorted(p):=link(temp_head);
//! if r<>temp_head then @<Update the max/min amounts@>;
//! end
//!
//! @ @<Insert an edge-weight for edge |m|, if...@>=
//! if w<>prev_w then
//!   begin s:=get_avail; link(r):=s;
//!   info(s):=8*m+min_halfword+zero_w+w-prev_w;
//!   r:=s; prev_w:=w;
//!   end
//!
//! @ @<Update the max/min amounts@>=
//! begin if min_n=max_halfword then min_n:=n;
//! max_n:=n;
//! if min_d>info(link(temp_head)) then min_d:=info(link(temp_head));
//! if max_d<info(r) then max_d:=info(r);
//! end
//!
//! @ @<Delete empty rows at the top and/or bottom...@>=
//! if min_n>max_n then @<Delete all the row headers@>
//! else  begin n:=n_min(cur_edges); n_min(cur_edges):=min_n;
//!   while min_n>n do
//!     begin p:=link(cur_edges); link(cur_edges):=link(p);
//!     knil(link(p)):=cur_edges;
//!     free_node(p,row_node_size); incr(n);
//!     end;
//!   n:=n_max(cur_edges); n_max(cur_edges):=max_n;
//!   n_pos(cur_edges):=max_n+1; n_rover(cur_edges):=cur_edges;
//!   while max_n<n do
//!     begin p:=knil(cur_edges); knil(cur_edges):=knil(p);
//!     link(knil(p)):=cur_edges;
//!     free_node(p,row_node_size); decr(n);
//!     end;
//!   m_min(cur_edges):=((ho(min_d)) div 8)-m_offset(cur_edges)+zero_field;
//!   m_max(cur_edges):=((ho(max_d)) div 8)-m_offset(cur_edges)+zero_field;
//!   end
//!
//! @ We get here if the edges have been entirely culled away.
//!
//! @<Delete all the row headers@>=
//! begin p:=link(cur_edges);
//! while p<>cur_edges do
//!   begin q:=link(p); free_node(p,row_node_size); p:=q;
//!   end;
//! init_edges(cur_edges);
//! end
//!
//!
//! @ The last and most difficult routine for transforming an edge structure---and
//! the most interesting one!---is |xy_swap_edges|, which interchanges the
//! r\^^Doles of rows and columns. Its task can be viewed as the job of
//! creating an edge structure that contains only horizontal edges, linked
//! together in columns, given an edge structure that contains only
//! vertical edges linked together in rows; we must do this without changing
//! the implied pixel weights.
//!
//! Given any two adjacent rows of an edge structure, it is not difficult to
//! determine the horizontal edges that lie ``between'' them: We simply look
//! for vertically adjacent pixels that have different weight, and insert
//! a horizontal edge containing the difference in weights. Every horizontal
//! edge determined in this way should be put into an appropriate linked
//! list. Since random access to these linked lists is desirable, we use
//! the |move| array to hold the list heads. If we work through the given
//! edge structure from top to bottom, the constructed lists will not need
//! to be sorted, since they will already be in order.
//!
//! The following algorithm makes use of some ideas suggested by John Hobby.
//! @^Hobby, John Douglas@>
//! It assumes that the edge structure is non-null, i.e., that |link(cur_edges)
//! <>cur_edges|, hence |m_max(cur_edges)>=m_min(cur_edges)|.
//!
//! @p procedure xy_swap_edges; {interchange |x| and |y| in |cur_edges|}
//! label done;
//! var @!m_magic,@!n_magic:integer; {special values that account for offsets}
//! @!p,@!q,@!r,@!s:pointer; {pointers that traverse the given structure}
//! @<Other local variables for |xy_swap_edges|@>@;
//! begin @<Initialize the array of new edge list heads@>;
//! @<Insert blank rows at the top and bottom, and set |p| to the new top row@>;
//! @<Compute the magic offset values@>;
//! repeat q:=knil(p);@+if unsorted(q)>void then sort_edges(q);
//! @<Insert the horizontal edges defined by adjacent rows |p,q|,
//!   and destroy row~|p|@>;
//! p:=q; n_magic:=n_magic-8;
//! until knil(p)=cur_edges;
//! free_node(p,row_node_size); {now all original rows have been recycled}
//! @<Adjust the header to reflect the new edges@>;
//! end;
//!
//! @ Here we don't bother to keep the |link| entries up to date, since the
//! procedure looks only at the |knil| fields as it destroys the former
//! edge structure.
//!
//! @<Insert blank rows at the top and bottom...@>=
//! p:=get_node(row_node_size); sorted(p):=sentinel; unsorted(p):=null;@/
//! knil(p):=cur_edges; knil(link(cur_edges)):=p; {the new bottom row}
//! p:=get_node(row_node_size); sorted(p):=sentinel;
//! knil(p):=knil(cur_edges); {the new top row}
//!
//! @ The new lists will become |sorted| lists later, so we initialize
//! empty lists to |sentinel|.
//!
//! @<Initialize the array of new edge list heads@>=
//! m_spread:=m_max(cur_edges)-m_min(cur_edges); {this is |>=0| by assumption}
//! if m_spread>move_size then overflow("move table size",move_size);
//! @:METAFONT capacity exceeded move table size}{\quad move table size@>
//! for j:=0 to m_spread do move[j]:=sentinel
//!
//! @ @<Other local variables for |xy_swap_edges|@>=
//! @!m_spread:integer; {the difference between |m_max| and |m_min|}
//! @!j,@!jj:0..move_size; {indices into |move|}
//! @!m,@!mm:integer; {|m| values at vertical edges}
//! @!pd,@!rd:integer; {data fields from edge-and-weight nodes}
//! @!pm,@!rm:integer; {|m| values from edge-and-weight nodes}
//! @!w:integer; {the difference in accumulated weight}
//! @!ww:integer; {as much of |w| that can be stored in a single node}
//! @!dw:integer; {an increment to be added to |w|}
//!
//! @ At the point where we test |w<>0|, variable |w| contains
//! the accumulated weight from edges already passed in
//! row~|p| minus the accumulated weight from edges already passed in row~|q|.
//!
//! @<Insert the horizontal edges defined by adjacent rows |p,q|...@>=
//! r:=sorted(p); free_node(p,row_node_size); p:=r;@/
//! pd:=ho(info(p)); pm:=pd div 8;@/
//! r:=sorted(q); rd:=ho(info(r)); rm:=rd div 8; w:=0;
//! loop@+  begin if pm<rm then mm:=pm@+else mm:=rm;
//!   if w<>0 then
//!     @<Insert horizontal edges of weight |w| between |m| and~|mm|@>;
//!   if pd<rd then
//!     begin dw:=(pd mod 8)-zero_w;
//!     @<Advance pointer |p| to the next vertical edge,
//!       after destroying the previous one@>;
//!     end
//!   else  begin if r=sentinel then goto done; {|rd=pd=ho(max_halfword)|}
//!     dw:=-((rd mod 8)-zero_w);
//!     @<Advance pointer |r| to the next vertical edge@>;
//!     end;
//!   m:=mm; w:=w+dw;
//!   end;
//! done:
//!
//! @ @<Advance pointer |r| to the next vertical edge@>=
//! r:=link(r); rd:=ho(info(r)); rm:=rd div 8
//!
//! @ @<Advance pointer |p| to the next vertical edge...@>=
//! s:=link(p); free_avail(p); p:=s; pd:=ho(info(p)); pm:=pd div 8
//!
//! @ Certain ``magic'' values are needed to make the following code work,
//! because of the various offsets in our data structure. For now, let's not
//! worry about their precise values; we shall compute |m_magic| and |n_magic|
//! later, after we see what the code looks like.
//!
//! @ @<Insert horizontal edges of weight |w| between |m| and~|mm|@>=
//! if m<>mm then
//!   begin if mm-m_magic>=move_size then confusion("xy");
//! @:this can't happen xy}{\quad xy@>
//!   extras:=(abs(w)-1) div 3;
//!   if extras>0 then
//!     begin if w>0 then xw:=+3@+else xw:=-3;
//!     ww:=w-extras*xw;
//!     end
//!   else ww:=w;
//!   repeat j:=m-m_magic;
//!   for k:=1 to extras do
//!     begin s:=get_avail; info(s):=n_magic+xw;
//!     link(s):=move[j]; move[j]:=s;
//!     end;
//!   s:=get_avail; info(s):=n_magic+ww;
//!   link(s):=move[j]; move[j]:=s;@/
//!   incr(m);
//!   until m=mm;
//!   end
//!
//! @ @<Other local variables for |xy...@>=
//! @!extras:integer; {the number of additional nodes to make weights |>3|}
//! @!xw:-3..3; {the additional weight in extra nodes}
//! @!k:integer; {loop counter for inserting extra nodes}
//!
//! @ At the beginning of this step, |move[m_spread]=sentinel|, because no
//! horizontal edges will extend to the right of column |m_max(cur_edges)|.
//!
//! @<Adjust the header to reflect the new edges@>=
//! move[m_spread]:=0; j:=0;
//! while move[j]=sentinel do incr(j);
//! if j=m_spread then init_edges(cur_edges) {all edge weights are zero}
//! else  begin mm:=m_min(cur_edges);
//!   m_min(cur_edges):=n_min(cur_edges);
//!   m_max(cur_edges):=n_max(cur_edges)+1;
//!   m_offset(cur_edges):=zero_field;
//!   jj:=m_spread-1;
//!   while move[jj]=sentinel do decr(jj);
//!   n_min(cur_edges):=j+mm; n_max(cur_edges):=jj+mm; q:=cur_edges;
//!   repeat p:=get_node(row_node_size); link(q):=p; knil(p):=q;
//!   sorted(p):=move[j]; unsorted(p):=null; incr(j); q:=p;
//!   until j>jj;
//!   link(q):=cur_edges; knil(cur_edges):=q;
//!   n_pos(cur_edges):=n_max(cur_edges)+1; n_rover(cur_edges):=cur_edges;
//!   last_window_time(cur_edges):=0;
//!   end;
//!
//! @ The values of |m_magic| and |n_magic| can be worked out by trying the
//! code above on a small example; if they work correctly in simple cases,
//! they should work in general.
//!
//! @<Compute the magic offset values@>=
//! m_magic:=m_min(cur_edges)+m_offset(cur_edges)-zero_field;
//! n_magic:=8*n_max(cur_edges)+8+zero_w+min_halfword
//!
//! @ Now let's look at the subroutine that merges the edges from a given
//! edge structure into |cur_edges|. The given edge structure loses all its
//! edges.
//!
//! @p procedure merge_edges(@!h:pointer);
//! label done;
//! var @!p,@!q,@!r,@!pp,@!qq,@!rr:pointer; {list manipulation registers}
//! @!n:integer; {row number}
//! @!k:halfword; {key register that we compare to |info(q)|}
//! @!delta:integer; {change to the edge/weight data}
//! begin if link(h)<>h then
//!   begin if (m_min(h)<m_min(cur_edges))or(m_max(h)>m_max(cur_edges))or@|
//!     (n_min(h)<n_min(cur_edges))or(n_max(h)>n_max(cur_edges)) then
//!     edge_prep(m_min(h)-zero_field,m_max(h)-zero_field,
//!       n_min(h)-zero_field,n_max(h)-zero_field+1);
//!   if m_offset(h)<>m_offset(cur_edges) then
//!     @<Adjust the data of |h| to account for a difference of offsets@>;
//!   n:=n_min(cur_edges); p:=link(cur_edges); pp:=link(h);
//!   while n<n_min(h) do
//!     begin incr(n); p:=link(p);
//!     end;
//!   repeat @<Merge row |pp| into row |p|@>;
//!   pp:=link(pp); p:=link(p);
//!   until pp=h;
//!   end;
//! end;
//!
//! @ @<Adjust the data of |h| to account for a difference of offsets@>=
//! begin pp:=link(h); delta:=8*(m_offset(cur_edges)-m_offset(h));
//! repeat qq:=sorted(pp);
//! while qq<>sentinel do
//!   begin info(qq):=info(qq)+delta; qq:=link(qq);
//!   end;
//! qq:=unsorted(pp);
//! while qq>void do
//!   begin info(qq):=info(qq)+delta; qq:=link(qq);
//!   end;
//! pp:=link(pp);
//! until pp=h;
//! end
//!
//! @ The |sorted| and |unsorted| lists are merged separately. After this
//! step, row~|pp| will have no edges remaining, since they will all have
//! been merged into row~|p|.
//!
//! @<Merge row |pp|...@>=
//! qq:=unsorted(pp);
//! if qq>void then
//!   if unsorted(p)<=void then unsorted(p):=qq
//!   else  begin while link(qq)>void do qq:=link(qq);
//!     link(qq):=unsorted(p); unsorted(p):=unsorted(pp);
//!     end;
//! unsorted(pp):=null; qq:=sorted(pp);
//! if qq<>sentinel then
//!   begin if unsorted(p)=void then unsorted(p):=null;
//!   sorted(pp):=sentinel; r:=sorted_loc(p); q:=link(r); {|q=sorted(p)|}
//!   if q=sentinel then sorted(p):=qq
//!   else loop@+begin k:=info(qq);
//!     while k>info(q) do
//!       begin r:=q; q:=link(r);
//!       end;
//!     link(r):=qq; rr:=link(qq); link(qq):=q;
//!     if rr=sentinel then goto done;
//!     r:=qq; qq:=rr;
//!     end;
//!   end;
//! done:
//!
//! @ The |total_weight| routine computes the total of all pixel weights
//! in a given edge structure. It's not difficult to prove that this is
//! the sum of $(-w)$ times $x$ taken over all edges,
//! where $w$ and~$x$ are the weight and $x$~coordinates stored in an edge.
//! It's not necessary to worry that this quantity will overflow the
//! size of an |integer| register, because it will be less than~$2^{31}$
//! unless the edge structure has more than 174,762 edges. However, we had
//! better not try to compute it as a |scaled| integer, because a total
//! weight of almost $12\times 2^{12}$ can be produced by only four edges.
//!
//! @p function total_weight(@!h:pointer):integer; {|h| is an edge header}
//! var @!p,@!q:pointer; {variables that traverse the given structure}
//! @!n:integer; {accumulated total so far}
//! @!m:0..65535; {packed $x$ and $w$ values, including offsets}
//! begin n:=0; p:=link(h);
//! while p<>h do
//!   begin q:=sorted(p);
//!   while q<>sentinel do
//!     @<Add the contribution of node |q| to the total weight,
//!       and set |q:=link(q)|@>;
//!   q:=unsorted(p);
//!   while q>void do
//!     @<Add the contribution of node |q| to the total weight,
//!       and set |q:=link(q)|@>;
//!   p:=link(p);
//!   end;
//! total_weight:=n;
//! end;
//!
//! @ It's not necessary to add the offsets to the $x$ coordinates, because
//! an entire edge structure can be shifted without affecting its total weight.
//! Similarly, we don't need to subtract |zero_field|.
//!
//! @<Add the contribution of node |q| to the total weight...@>=
//! begin m:=ho(info(q)); n:=n-((m mod 8)-zero_w)*(m div 8);
//! q:=link(q);
//! end
//!
//! @ So far we've done lots of things to edge structures assuming that
//! edges are actually present, but we haven't seen how edges get created
//! in the first place. Let's turn now to the problem of generating new edges.
//!
//! \MF\ will display new edges as they are being computed, if |tracing_edges|
//! is positive. In order to keep such data reasonably compact, only the
//! points at which the path makes a $90^\circ$ or $180^\circ$ turn are listed.
//!
//! The tracing algorithm must remember some past history in order to suppress
//! unnecessary data. Three variables |trace_x|, |trace_y|, and |trace_yy|
//! provide this history: The last coordinates printed were |(trace_x,trace_y)|,
//! and the previous edge traced ended at |(trace_x,trace_yy)|. Before anything
//! at all has been traced, |trace_x=-4096|.
//!
//! @<Glob...@>=
//! @!trace_x:integer; {$x$~coordinate most recently shown in a trace}
//! @!trace_y:integer; {$y$~coordinate most recently shown in a trace}
//! @!trace_yy:integer; {$y$~coordinate most recently encountered}
//!
//! @ Edge tracing is initiated by the |begin_edge_tracing| routine,
//! continued by the |trace_a_corner| routine, and terminated by the
//! |end_edge_tracing| routine.
//!
//! @p procedure begin_edge_tracing;
//! begin print_diagnostic("Tracing edges","",true);
//! print(" (weight "); print_int(cur_wt); print_char(")"); trace_x:=-4096;
//! end;
//! @#
//! procedure trace_a_corner;
//! begin if file_offset>max_print_line-13 then print_nl("");
//! print_char("("); print_int(trace_x); print_char(","); print_int(trace_yy);
//! print_char(")"); trace_y:=trace_yy;
//! end;
//! @#
//! procedure end_edge_tracing;
//! begin if trace_x=-4096 then print_nl("(No new edges added.)")
//! @.No new edges added@>
//! else  begin trace_a_corner; print_char(".");
//!   end;
//! end_diagnostic(true);
//! end;
//!
//! @ Just after a new edge weight has been put into the |info| field of
//! node~|r|, in row~|n|, the following routine continues an ongoing trace.
//!
//! @p procedure trace_new_edge(@!r:pointer;@!n:integer);
//! var @!d:integer; {temporary data register}
//! @!w:-3..3; {weight associated with an edge transition}
//! @!m,@!n0,@!n1:integer; {column and row numbers}
//! begin d:=ho(info(r)); w:=(d mod 8)-zero_w; m:=(d div 8)-m_offset(cur_edges);
//! if w=cur_wt then
//!   begin n0:=n+1; n1:=n;
//!   end
//! else  begin n0:=n; n1:=n+1;
//!   end; {the edges run from |(m,n0)| to |(m,n1)|}
//! if m<>trace_x then
//!   begin if trace_x=-4096 then
//!     begin print_nl(""); trace_yy:=n0;
//!     end
//!   else if trace_yy<>n0 then print_char("?") {shouldn't happen}
//!   else trace_a_corner;
//!   trace_x:=m; trace_a_corner;
//!   end
//! else  begin if n0<>trace_yy then print_char("!"); {shouldn't happen}
//!   if ((n0<n1)and(trace_y>trace_yy))or((n0>n1)and(trace_y<trace_yy)) then
//!     trace_a_corner;
//!   end;
//! trace_yy:=n1;
//! end;
//!
//! @ One way to put new edge weights into an edge structure is to use the
//! following routine, which simply draws a straight line from |(x0,y0)| to
//! |(x1,y1)|. More precisely, it introduces weights for the edges of the
//! discrete path $\bigl(\lfloor t[x_0,x_1]+{1\over2}+\epsilon\rfloor,
//! \lfloor t[y_0,y_1]+{1\over2}+\epsilon\delta\rfloor\bigr)$,
//! as $t$ varies from 0 to~1, where $\epsilon$ and $\delta$ are extremely small
//! positive numbers.
//!
//! The structure header is assumed to be |cur_edges|; downward edge weights
//! will be |cur_wt|, while upward ones will be |-cur_wt|.
//!
//! Of course, this subroutine will be called only in connection with others
//! that eventually draw a complete cycle, so that the sum of the edge weights
//! in each row will be zero whenever the row is displayed.
//!
//! @p procedure line_edges(@!x0,@!y0,@!x1,@!y1:scaled);
//! label done,done1;
//! var @!m0,@!n0,@!m1,@!n1:integer; {rounded and unscaled coordinates}
//! @!delx,@!dely:scaled; {the coordinate differences of the line}
//! @!yt:scaled; {smallest |y| coordinate that rounds the same as |y0|}
//! @!tx:scaled; {tentative change in |x|}
//! @!p,@!r:pointer; {list manipulation registers}
//! @!base:integer; {amount added to edge-and-weight data}
//! @!n:integer; {current row number}
//! begin n0:=round_unscaled(y0);
//! n1:=round_unscaled(y1);
//! if n0<>n1 then
//!   begin m0:=round_unscaled(x0); m1:=round_unscaled(x1);
//!   delx:=x1-x0; dely:=y1-y0;
//!   yt:=n0*unity-half_unit; y0:=y0-yt; y1:=y1-yt;
//!   if n0<n1 then @<Insert upward edges for a line@>
//!   else @<Insert downward edges for a line@>;
//!   n_rover(cur_edges):=p; n_pos(cur_edges):=n+zero_field;
//!   end;
//! end;
//!
//! @ Here we are careful to cancel any effect of rounding error.
//!
//! @<Insert upward edges for a line@>=
//! begin base:=8*m_offset(cur_edges)+min_halfword+zero_w-cur_wt;
//! if m0<=m1 then edge_prep(m0,m1,n0,n1)@+else edge_prep(m1,m0,n0,n1);
//! @<Move to row |n0|, pointed to by |p|@>;
//! y0:=unity-y0;
//! loop@+  begin r:=get_avail; link(r):=unsorted(p); unsorted(p):=r;@/
//!   tx:=take_fraction(delx,make_fraction(y0,dely));
//!   if ab_vs_cd(delx,y0,dely,tx)<0 then decr(tx);
//!     {now $|tx|=\lfloor|y0|\cdot|delx|/|dely|\rfloor$}
//!   info(r):=8*round_unscaled(x0+tx)+base;@/
//!   y1:=y1-unity;
//!   if internal[tracing_edges]>0 then trace_new_edge(r,n);
//!   if y1<unity then goto done;
//!   p:=link(p); y0:=y0+unity; incr(n);
//!   end;
//! done: end
//!
//! @ @<Insert downward edges for a line@>=
//! begin base:=8*m_offset(cur_edges)+min_halfword+zero_w+cur_wt;
//! if m0<=m1 then edge_prep(m0,m1,n1,n0)@+else edge_prep(m1,m0,n1,n0);
//! decr(n0); @<Move to row |n0|, pointed to by |p|@>;
//! loop@+  begin r:=get_avail; link(r):=unsorted(p); unsorted(p):=r;@/
//!   tx:=take_fraction(delx,make_fraction(y0,dely));
//!   if ab_vs_cd(delx,y0,dely,tx)<0 then incr(tx);
//!     {now $|tx|=\lceil|y0|\cdot|delx|/|dely|\rceil$, since |dely<0|}
//!   info(r):=8*round_unscaled(x0-tx)+base;@/
//!   y1:=y1+unity;
//!   if internal[tracing_edges]>0 then trace_new_edge(r,n);
//!   if y1>=0 then goto done1;
//!   p:=knil(p); y0:=y0+unity; decr(n);
//!   end;
//! done1: end
//!
//! @ @<Move to row |n0|, pointed to by |p|@>=
//! n:=n_pos(cur_edges)-zero_field; p:=n_rover(cur_edges);
//! if n<>n0 then
//!   if n<n0 then
//!     repeat incr(n); p:=link(p);
//!     until n=n0
//!   else  repeat decr(n); p:=knil(p);
//!     until n=n0
//!
//! @ \MF\ inserts most of its edges into edge structures via the
//! |move_to_edges| subroutine, which uses the data stored in the |move| array
//! to specify a sequence of ``rook moves.'' The starting point |(m0,n0)|
//! and finishing point |(m1,n1)| of these moves, as seen from the standpoint
//! of the first octant, are supplied as parameters; the moves should, however,
//! be rotated into a given octant.  (We're going to study octant
//! transformations in great detail later; the reader may wish to come back to
//! this part of the program after mastering the mysteries of octants.)
//!
//! The rook moves themselves are defined as follows, from a |first_octant|
//! point of view: ``Go right |move[k]| steps, then go up one, for |0<=k<n1-n0|;
//! then go right |move[n1-n0]| steps and stop.'' The sum of |move[k]|
//! for |0<=k<=n1-n0| will be equal to |m1-m0|.
//!
//! As in the |line_edges| routine, we use |+cur_wt| as the weight of
//! all downward edges and |-cur_wt| as the weight of all upward edges,
//! after the moves have been rotated to the proper octant direction.
//!
//! There are two main cases to consider: \\{fast\_case} is for moves that
//! travel in the direction of octants 1, 4, 5, and~8, while \\{slow\_case}
//! is for moves that travel toward octants 2, 3, 6, and~7. The latter directions
//! are comparatively cumbersome because they generate more upward or downward
//! edges; a curve that travels horizontally doesn't produce any edges at all,
//! but a curve that travels vertically touches lots of rows.
//!
//! @d fast_case_up=60 {for octants 1 and 4}
//! @d fast_case_down=61 {for octants 5 and 8}
//! @d slow_case_up=62 {for octants 2 and 3}
//! @d slow_case_down=63 {for octants 6 and 7}
//!
//! @p procedure move_to_edges(@!m0,@!n0,@!m1,@!n1:integer);
//! label fast_case_up,fast_case_down,slow_case_up,slow_case_down,done;
//! var @!delta:0..move_size; {extent of |move| data}
//! @!k:0..move_size; {index into |move|}
//! @!p,@!r:pointer; {list manipulation registers}
//! @!dx:integer; {change in edge-weight |info| when |x| changes by 1}
//! @!edge_and_weight:integer; {|info| to insert}
//! @!j:integer; {number of consecutive vertical moves}
//! @!n:integer; {the current row pointed to by |p|}
//! debug @!sum:integer;@+gubed@;@/
//! begin delta:=n1-n0;
//! debug sum:=move[0]; for k:=1 to delta do sum:=sum+abs(move[k]);
//! if sum<>m1-m0 then confusion("0");@+gubed@;@/
//! @:this can't happen 0}{\quad 0@>
//! @<Prepare for and switch to the appropriate case, based on |octant|@>;
//! fast_case_up:@<Add edges for first or fourth octants, then |goto done|@>;
//! fast_case_down:@<Add edges for fifth or eighth octants, then |goto done|@>;
//! slow_case_up:@<Add edges for second or third octants, then |goto done|@>;
//! slow_case_down:@<Add edges for sixth or seventh octants, then |goto done|@>;
//! done: n_pos(cur_edges):=n+zero_field; n_rover(cur_edges):=p;
//! end;
//!
//! @ The current octant code appears in a global variable. If, for example,
//! we have |octant=third_octant|, it means that a curve traveling in a north to
//! north-westerly direction has been rotated for the purposes of internal
//! calculations so that the |move| data travels in an east to north-easterly
//! direction. We want to unrotate as we update the edge structure.
//!
//! @<Glob...@>=
//! @!octant:first_octant..sixth_octant; {the current octant of interest}
//!
//! @ @<Prepare for and switch to the appropriate case, based on |octant|@>=
//! case octant of
//! first_octant:begin dx:=8; edge_prep(m0,m1,n0,n1); goto fast_case_up;
//!   end;
//! second_octant:begin dx:=8; edge_prep(n0,n1,m0,m1); goto slow_case_up;
//!   end;
//! third_octant:begin dx:=-8; edge_prep(-n1,-n0,m0,m1); negate(n0);
//!   goto slow_case_up;
//!   end;
//! fourth_octant:begin dx:=-8; edge_prep(-m1,-m0,n0,n1); negate(m0);
//!   goto fast_case_up;
//!   end;
//! fifth_octant:begin dx:=-8; edge_prep(-m1,-m0,-n1,-n0); negate(m0);
//!   goto fast_case_down;
//!   end;
//! sixth_octant:begin dx:=-8; edge_prep(-n1,-n0,-m1,-m0); negate(n0);
//!   goto slow_case_down;
//!   end;
//! seventh_octant:begin dx:=8; edge_prep(n0,n1,-m1,-m0); goto slow_case_down;
//!   end;
//! eighth_octant:begin dx:=8; edge_prep(m0,m1,-n1,-n0); goto fast_case_down;
//!   end;
//! end; {there are only eight octants}
//!
//! @ @<Add edges for first or fourth octants, then |goto done|@>=
//! @<Move to row |n0|, pointed to by |p|@>;
//! if delta>0 then
//!   begin k:=0;
//!   edge_and_weight:=8*(m0+m_offset(cur_edges))+min_halfword+zero_w-cur_wt;
//!   repeat edge_and_weight:=edge_and_weight+dx*move[k];
//!   fast_get_avail(r); link(r):=unsorted(p); info(r):=edge_and_weight;
//!   if internal[tracing_edges]>0 then trace_new_edge(r,n);
//!   unsorted(p):=r; p:=link(p); incr(k); incr(n);
//!   until k=delta;
//!   end;
//! goto done
//!
//! @ @<Add edges for fifth or eighth octants, then |goto done|@>=
//! n0:=-n0-1; @<Move to row |n0|, pointed to by |p|@>;
//! if delta>0 then
//!   begin k:=0;
//!   edge_and_weight:=8*(m0+m_offset(cur_edges))+min_halfword+zero_w+cur_wt;
//!   repeat edge_and_weight:=edge_and_weight+dx*move[k];
//!   fast_get_avail(r); link(r):=unsorted(p); info(r):=edge_and_weight;
//!   if internal[tracing_edges]>0 then trace_new_edge(r,n);
//!   unsorted(p):=r; p:=knil(p); incr(k); decr(n);
//!   until k=delta;
//!   end;
//! goto done
//!
//! @ @<Add edges for second or third octants, then |goto done|@>=
//! edge_and_weight:=8*(n0+m_offset(cur_edges))+min_halfword+zero_w-cur_wt;
//! n0:=m0; k:=0; @<Move to row |n0|, pointed to by |p|@>;
//! repeat j:=move[k];
//! while j>0 do
//!   begin fast_get_avail(r); link(r):=unsorted(p); info(r):=edge_and_weight;
//!   if internal[tracing_edges]>0 then trace_new_edge(r,n);
//!   unsorted(p):=r; p:=link(p); decr(j); incr(n);
//!   end;
//! edge_and_weight:=edge_and_weight+dx; incr(k);
//! until k>delta;
//! goto done
//!
//! @ @<Add edges for sixth or seventh octants, then |goto done|@>=
//! edge_and_weight:=8*(n0+m_offset(cur_edges))+min_halfword+zero_w+cur_wt;
//! n0:=-m0-1; k:=0; @<Move to row |n0|, pointed to by |p|@>;
//! repeat j:=move[k];
//! while j>0 do
//!   begin fast_get_avail(r); link(r):=unsorted(p); info(r):=edge_and_weight;
//!   if internal[tracing_edges]>0 then trace_new_edge(r,n);
//!   unsorted(p):=r; p:=knil(p); decr(j); decr(n);
//!   end;
//! edge_and_weight:=edge_and_weight+dx; incr(k);
//! until k>delta;
//! goto done
//!
//! @ All the hard work of building an edge structure is undone by the following
//! subroutine.
//!
//! @<Declare the recycling subroutines@>=
//! procedure toss_edges(@!h:pointer);
//! var @!p,@!q:pointer; {for list manipulation}
//! begin q:=link(h);
//! while q<>h do
//!   begin flush_list(sorted(q));
//!   if unsorted(q)>void then flush_list(unsorted(q));
//!   p:=q; q:=link(q); free_node(p,row_node_size);
//!   end;
//! free_node(h,edge_header_size);
//! end;
//!
//! @* \[21] Subdivision into octants.
//! When \MF\ digitizes a path, it reduces the problem to the special
//! case of paths that travel in ``first octant'' directions; i.e.,
//! each cubic $z(t)=\bigl(x(t),y(t)\bigr)$ being digitized will have the property
//! that $0\L y'(t)\L x'(t)$. This assumption makes digitizing simpler
//! and faster than if the direction of motion has to be tested repeatedly.
//!
//! When $z(t)$ is cubic, $x'(t)$ and $y'(t)$ are quadratic, hence the four
//! polynomials $x'(t)$, $y'(t)$, $x'(t)-y'(t)$, and $x'(t)+y'(t)$ cross
//! through~0 at most twice each. If we subdivide the given cubic at these
//! places, we get at most nine subintervals in each of which
//! $x'(t)$, $y'(t)$, $x'(t)-y'(t)$, and $x'(t)+y'(t)$ all have a constant
//! sign. The curve can be transformed in each of these subintervals so that
//! it travels entirely in first octant directions, if we reflect $x\swap-x$,
//! $y\swap-y$, and/or $x\swap y$ as necessary. (Incidentally, it can be
//! shown that a cubic such that $x'(t)=16(2t-1)^2+2(2t-1)-1$ and
//! $y'(t)=8(2t-1)^2+4(2t-1)$ does indeed split into nine subintervals.)
//!
//! @ The transformation that rotates coordinates, so that first octant motion
//! can be assumed, is defined by the |skew| subroutine, which sets global
//! variables |cur_x| and |cur_y| to the values that are appropriate in a
//! given octant.  (Octants are encoded as they were in the |n_arg| subroutine.)
//!
//! This transformation is ``skewed'' by replacing |(x,y)| by |(x-y,y)|,
//! once first octant motion has been established. It turns out that
//! skewed coordinates are somewhat better to work with when curves are
//! actually digitized.
//!
//! @d set_two_end(#)==cur_y:=#;@+end
//! @d set_two(#)==begin cur_x:=#; set_two_end
//!
//! @p procedure skew(@!x,@!y:scaled;@!octant:small_number);
//! begin case octant of
//! first_octant: set_two(x-y)(y);
//! second_octant: set_two(y-x)(x);
//! third_octant: set_two(y+x)(-x);
//! fourth_octant: set_two(-x-y)(y);
//! fifth_octant: set_two(-x+y)(-y);
//! sixth_octant: set_two(-y+x)(-x);
//! seventh_octant: set_two(-y-x)(x);
//! eighth_octant: set_two(x+y)(-y);
//! end; {there are no other cases}
//! end;
//!
//! @ Conversely, the following subroutine sets |cur_x| and
//! |cur_y| to the original coordinate values of a point, given an octant
//! code and the point's coordinates |(x,y)| after they have been mapped into
//! the first octant and skewed.
//!
//! @<Declare subroutines for printing expressions@>=
//! procedure unskew(@!x,@!y:scaled;@!octant:small_number);
//! begin case octant of
//! first_octant: set_two(x+y)(y);
//! second_octant: set_two(y)(x+y);
//! third_octant: set_two(-y)(x+y);
//! fourth_octant: set_two(-x-y)(y);
//! fifth_octant: set_two(-x-y)(-y);
//! sixth_octant: set_two(-y)(-x-y);
//! seventh_octant: set_two(y)(-x-y);
//! eighth_octant: set_two(x+y)(-y);
//! end; {there are no other cases}
//! end;
//!
//! @ @<Glob...@>=
//! @!cur_x,@!cur_y:scaled;
//!   {outputs of |skew|, |unskew|, and a few other routines}
//!
//! @ The conversion to skewed and rotated coordinates takes place in
//! stages, and at one point in the transformation we will have negated the
//! $x$ and/or $y$ coordinates so as to make curves travel in the first
//! {\sl quadrant}. At this point the relevant ``octant'' code will be
//! either |first_octant| (when no transformation has been done),
//! or |fourth_octant=first_octant+negate_x| (when $x$ has been negated),
//! or |fifth_octant=first_octant+negate_x+negate_y| (when both have been
//! negated), or |eighth_octant=first_octant+negate_y| (when $y$ has been
//! negated). The |abnegate| routine is sometimes needed to convert
//! from one of these transformations to another.
//!
//! @p procedure abnegate(@!x,@!y:scaled;
//!   @!octant_before,@!octant_after:small_number);
//! begin if odd(octant_before)=odd(octant_after) then cur_x:=x
//!   else cur_x:=-x;
//! if (octant_before>negate_y)=(octant_after>negate_y) then cur_y:=y
//!   else cur_y:=-y;
//! end;
//!
//! @ Now here's a subroutine that's handy for subdivision: Given a
//! quadratic polynomial $B(a,b,c;t)$, the |crossing_point| function
//! returns the unique |fraction| value |t| between 0 and~1 at which
//! $B(a,b,c;t)$ changes from positive to negative, or returns
//! |t=fraction_one+1| if no such value exists. If |a<0| (so that $B(a,b,c;t)$
//! is already negative at |t=0|), |crossing_point| returns the value zero.
//!
//! @d no_crossing==begin crossing_point:=fraction_one+1; return;
//!   end
//! @d one_crossing==begin crossing_point:=fraction_one; return;
//!   end
//! @d zero_crossing==begin crossing_point:=0; return;
//!   end
//!
//! @p function crossing_point(@!a,@!b,@!c:integer):fraction;
//! label exit;
//! var @!d:integer; {recursive counter}
//! @!x,@!xx,@!x0,@!x1,@!x2:integer; {temporary registers for bisection}
//! begin if a<0 then zero_crossing;
//! if c>=0 then
//!   begin if b>=0 then
//!     if c>0 then no_crossing
//!     else if (a=0)and(b=0) then no_crossing
//!     else one_crossing;
//!   if a=0 then zero_crossing;
//!   end
//! else if a=0 then if b<=0 then zero_crossing;
//! @<Use bisection to find the crossing point, if one exists@>;
//! exit:end;
//!
//! @ The general bisection method is quite simple when $n=2$, hence
//! |crossing_point| does not take much time. At each stage in the
//! recursion we have a subinterval defined by |l| and~|j| such that
//! $B(a,b,c;2^{-l}(j+t))=B(x_0,x_1,x_2;t)$, and we want to ``zero in'' on
//! the subinterval where $x_0\G0$ and $\min(x_1,x_2)<0$.
//!
//! It is convenient for purposes of calculation to combine the values
//! of |l| and~|j| in a single variable $d=2^l+j$, because the operation
//! of bisection then corresponds simply to doubling $d$ and possibly
//! adding~1. Furthermore it proves to be convenient to modify
//! our previous conventions for bisection slightly, maintaining the
//! variables $X_0=2^lx_0$, $X_1=2^l(x_0-x_1)$, and $X_2=2^l(x_1-x_2)$.
//! With these variables the conditions $x_0\ge0$ and $\min(x_1,x_2)<0$ are
//! equivalent to $\max(X_1,X_1+X_2)>X_0\ge0$.
//!
//! The following code maintains the invariant relations
//! $0\L|x0|<\max(|x1|,|x1|+|x2|)$,
//! $\vert|x1|\vert<2^{30}$, $\vert|x2|\vert<2^{30}$;
//! it has been constructed in such a way that no arithmetic overflow
//! will occur if the inputs satisfy
//! $a<2^{30}$, $\vert a-b\vert<2^{30}$, and $\vert b-c\vert<2^{30}$.
//!
//! @<Use bisection to find the crossing point...@>=
//! d:=1; x0:=a; x1:=a-b; x2:=b-c;
//! repeat x:=half(x1+x2);
//! if x1-x0>x0 then
//!   begin x2:=x; double(x0); double(d);
//!   end
//! else  begin xx:=x1+x-x0;
//!   if xx>x0 then
//!     begin x2:=x; double(x0); double(d);
//!     end
//!   else  begin x0:=x0-xx;
//!     if x<=x0 then if x+x2<=x0 then no_crossing;
//!     x1:=x; d:=d+d+1;
//!     end;
//!   end;
//! until d>=fraction_one;
//! crossing_point:=d-fraction_one
//!
//! @ Octant subdivision is applied only to cycles, i.e., to closed paths.
//! A ``cycle spec'' is a data structure that contains specifications of
//! @!@^cycle spec@>
//! cubic curves and octant mappings for the cycle that has been subdivided
//! into segments belonging to single octants. It is composed entirely of
//! knot nodes, similar to those in the representation of paths; but the
//! |explicit| type indications have been replaced by positive numbers
//! that give further information. Additional |endpoint| data is also
//! inserted at the octant boundaries.
//!
//! Recall that a cubic polynomial is represented by four control points
//! that appear in adjacent nodes |p| and~|q| of a knot list. The |x|~coordinates
//! are |x_coord(p)|, |right_x(p)|, |left_x(q)|, and |x_coord(q)|; the
//! |y|~coordinates are similar. We shall call this ``the cubic following~|p|''
//! or ``the cubic between |p| and~|q|'' or ``the cubic preceding~|q|.''
//!
//! Cycle specs are circular lists of cubic curves mixed with octant
//! boundaries. Like cubics, the octant boundaries are represented in
//! consecutive knot nodes |p| and~|q|. In such cases |right_type(p)=
//! left_type(q)=endpoint|, and the fields |right_x(p)|, |right_y(p)|,
//! |left_x(q)|, and |left_y(q)| are replaced by other fields called
//! |right_octant(p)|, |right_transition(p)|, |left_octant(q)|, and
//! |left_transition(q)|, respectively. For example, when the curve direction
//! moves from the third octant to the fourth octant, the boundary nodes say
//! |right_octant(p)=third_octant|, |left_octant(q)=fourth_octant|,
//! and |right_transition(p)=left_transition(q)=diagonal|. A |diagonal|
//! transition occurs when moving between octants 1~\AM~2, 3~\AM~4, 5~\AM~6, or
//! 7~\AM~8; an |axis| transition occurs when moving between octants 8~\AM~1,
//! 2~\AM~3, 4~\AM~5, 6~\AM~7. (Such transition information is redundant
//! but convenient.) Fields |x_coord(p)| and |y_coord(p)| will contain
//! coordinates of the transition point after rotation from third octant
//! to first octant; i.e., if the true coordinates are $(x,y)$, the
//! coordinates $(y,-x)$ will appear in node~|p|. Similarly, a fourth-octant
//! transformation will have been applied after the transition, so
//! we will have |x_coord(q)=@t$-x$@>| and |y_coord(q)=y|.
//!
//! The cubic between |p| and |q| will contain positive numbers in the
//! fields |right_type(p)| and |left_type(q)|; this makes cubics
//! distinguishable from octant boundaries, because |endpoint=0|.
//! The value of |right_type(p)| will be the current octant code,
//! during the time that cycle specs are being constructed; it will
//! refer later to a pen offset position, if the envelope of a cycle is
//! being computed. A cubic that comes from some subinterval of the $k$th
//! step in the original cyclic path will have |left_type(q)=k|.
//!
//! @d right_octant==right_x {the octant code before a transition}
//! @d left_octant==left_x {the octant after a transition}
//! @d right_transition==right_y {the type of transition}
//! @d left_transition==left_y {ditto, either |axis| or |diagonal|}
//! @d axis=0 {a transition across the $x'$- or $y'$-axis}
//! @d diagonal=1 {a transition where $y'=\pm x'$}
//!
//! @ Here's a routine that prints a cycle spec in symbolic form, so that it
//! is possible to see what subdivision has been made.  The point coordinates
//! are converted back from \MF's internal ``rotated'' form to the external
//! ``true'' form. The global variable~|cur_spec| should point to a knot just
//! after the beginning of an octant boundary, i.e., such that
//! |left_type(cur_spec)=endpoint|.
//!
//! @d print_two_true(#)==unskew(#,octant); print_two(cur_x,cur_y)
//!
//! @p procedure print_spec(@!s:str_number);
//! label not_found,done;
//! var @!p,@!q:pointer; {for list traversal}
//! @!octant:small_number; {the current octant code}
//! begin print_diagnostic("Cycle spec",s,true);
//! @.Cycle spec at line...@>
//! p:=cur_spec; octant:=left_octant(p); print_ln;
//! print_two_true(x_coord(cur_spec),y_coord(cur_spec));
//! print(" % beginning in octant `");
//! loop@+  begin print(octant_dir[octant]); print_char("'");
//!   loop@+  begin q:=link(p);
//!     if right_type(p)=endpoint then goto not_found;
//!     @<Print the cubic between |p| and |q|@>;
//!     p:=q;
//!     end;
//! not_found: if q=cur_spec then goto done;
//!   p:=q; octant:=left_octant(p); print_nl("% entering octant `");
//!   end;
//! @.entering the nth octant@>
//! done: print_nl(" & cycle"); end_diagnostic(true);
//! end;
//!
//! @ Symbolic octant direction names are kept in the |octant_dir| array.
//!
//! @<Glob...@>=
//! @!octant_dir:array[first_octant..sixth_octant] of str_number;
//!
//! @ @<Set init...@>=
//! octant_dir[first_octant]:="ENE";
//! octant_dir[second_octant]:="NNE";
//! octant_dir[third_octant]:="NNW";
//! octant_dir[fourth_octant]:="WNW";
//! octant_dir[fifth_octant]:="WSW";
//! octant_dir[sixth_octant]:="SSW";
//! octant_dir[seventh_octant]:="SSE";
//! octant_dir[eighth_octant]:="ESE";
//!
//! @ @<Print the cubic between...@>=
//! begin print_nl("   ..controls ");
//! print_two_true(right_x(p),right_y(p));
//! print(" and ");
//! print_two_true(left_x(q),left_y(q));
//! print_nl(" ..");
//! print_two_true(x_coord(q),y_coord(q));
//! print(" % segment "); print_int(left_type(q)-1);
//! end
//!
//! @ A much more compact version of a spec is printed to help users identify
//! ``strange paths.''
//!
//! @p procedure print_strange(@!s:str_number);
//! var @!p:pointer; {for list traversal}
//! @!f:pointer; {starting point in the cycle}
//! @!q:pointer; {octant boundary to be printed}
//! @!t:integer; {segment number, plus 1}
//! begin if interaction=error_stop_mode then wake_up_terminal;
//! print_nl(">");
//! @.>\relax@>
//! @<Find the starting point, |f|@>;
//! @<Determine the octant boundary |q| that precedes |f|@>;
//! t:=0;
//! repeat if left_type(p)<>endpoint then
//!   begin if left_type(p)<>t then
//!     begin t:=left_type(p); print_char(" "); print_int(t-1);
//!     end;
//!   if q<>null then
//!     begin @<Print the turns, if any, that start at |q|, and advance |q|@>;
//!     print_char(" "); print(octant_dir[left_octant(q)]); q:=null;
//!     end;
//!   end
//! else if q=null then q:=p;
//! p:=link(p);
//! until p=f;
//! print_char(" "); print_int(left_type(p)-1);
//! if q<>null then @<Print the turns...@>;
//! print_err(s);
//! end;
//!
//! @ If the segment numbers on the cycle are $t_1$, $t_2$, \dots, $t_m$,
//! and if |m<=max_quarterword|,
//! we have $t_{k-1}\L t_k$ except for at most one value of~$k$. If there are
//! no exceptions, $f$ will point to $t_1$; otherwise it will point to the
//! exceptional~$t_k$.
//!
//! There is at least one segment number (i.e., we always have $m>0$), because
//! |print_strange| is never called upon to display an entirely ``dead'' cycle.
//!
//! @<Find the starting point, |f|@>=
//! p:=cur_spec; t:=max_quarterword+1;
//! repeat p:=link(p);
//! if left_type(p)<>endpoint then
//!   begin if left_type(p)<t then f:=p;
//!   t:=left_type(p);
//!   end;
//! until p=cur_spec
//!
//! @ @<Determine the octant boundary...@>=
//! p:=cur_spec; q:=p;
//! repeat p:=link(p);
//! if left_type(p)=endpoint then q:=p;
//! until p=f
//!
//! @ When two octant boundaries are adjacent, the path is simply changing direction
//! without moving. Such octant directions are shown in parentheses.
//!
//! @<Print the turns...@>=
//! if left_type(link(q))=endpoint then
//!   begin print(" ("); print(octant_dir[left_octant(q)]); q:=link(q);
//!   while left_type(link(q))=endpoint do
//!     begin print_char(" "); print(octant_dir[left_octant(q)]); q:=link(q);
//!     end;
//!   print_char(")");
//!   end
//!
//! @ The |make_spec| routine is what subdivides paths into octants:
//! Given a pointer |cur_spec| to a cyclic path, |make_spec| mungs the path data
//! and returns a pointer to the corresponding cyclic spec.
//! All ``dead'' cubics (i.e., cubics that don't move at all from
//! their starting points) will have been removed from the result.
//! @!@^dead cubics@>
//!
//! The idea of |make_spec| is fairly simple: Each cubic is first
//! subdivided, if necessary, into pieces belonging to single octants;
//! then the octant boundaries are inserted. But some of the details of
//! this transformation are not quite obvious.
//!
//! If |autorounding>0|, the path will be adjusted so that critical tangent
//! directions occur at ``good'' points with respect to the pen called |cur_pen|.
//!
//! The resulting spec will have all |x| and |y| coordinates at most
//! $2^{28}-|half_unit|-1-|safety_margin|$ in absolute value.  The pointer
//! that is returned will start some octant, as required by |print_spec|.
//!
//! @p @t\4@>@<Declare subroutines needed by |make_spec|@>@;
//! function make_spec(@!h:pointer;
//!   @!safety_margin:scaled;@!tracing:integer):pointer;
//!   {converts a path to a cycle spec}
//! label continue,done;
//! var @!p,@!q,@!r,@!s:pointer; {for traversing the lists}
//! @!k:integer; {serial number of path segment, or octant code}
//! @!chopped:integer; {positive if data truncated,
//!           negative if data dangerously large}
//! @<Other local variables for |make_spec|@>@;
//! begin cur_spec:=h;
//! if tracing>0 then
//!   print_path(cur_spec,", before subdivision into octants",true);
//! max_allowed:=fraction_one-half_unit-1-safety_margin;
//! @<Truncate the values of all coordinates that exceed |max_allowed|, and stamp
//!   segment numbers in each |left_type| field@>;
//! quadrant_subdivide; {subdivide each cubic into pieces belonging to quadrants}
//! if (internal[autorounding]>0)and(chopped=0) then xy_round;
//! octant_subdivide; {complete the subdivision}
//! if (internal[autorounding]>unity)and(chopped=0) then diag_round;
//! @<Remove dead cubics@>;
//! @<Insert octant boundaries and compute the turning number@>;
//! while left_type(cur_spec)<>endpoint do cur_spec:=link(cur_spec);
//! if tracing>0 then
//!   if (internal[autorounding]<=0)or(chopped<>0) then
//!     print_spec(", after subdivision")
//!   else if internal[autorounding]>unity then
//!     print_spec(", after subdivision and double autorounding")
//!   else print_spec(", after subdivision and autorounding");
//! make_spec:=cur_spec;
//! end;
//!
//! @ The |make_spec| routine has an interesting side effect, namely to set
//! the global variable |turning_number| to the number of times the tangent
//! vector of the given cyclic path winds around the origin.
//!
//! Another global variable |cur_spec| points to the specification as it is
//! being made, since several subroutines must go to work on it.
//!
//! And there are two global variables that affect the rounding
//! decisions, as we'll see later; they are called |cur_pen| and |cur_path_type|.
//! The latter will be |double_path_code| if |make_spec| is being
//! applied to a double path.
//!
//! @d double_path_code=0 {command modifier for `\&{doublepath}'}
//! @d contour_code=1 {command modifier for `\&{contour}'}
//! @d also_code=2 {command modifier for `\&{also}'}
//!
//! @<Glob...@>=
//! @!cur_spec:pointer; {the principal output of |make_spec|}
//! @!turning_number:integer; {another output of |make_spec|}
//! @!cur_pen:pointer; {an implicit input of |make_spec|, used in autorounding}
//! @!cur_path_type:double_path_code..contour_code; {likewise}
//! @!max_allowed:scaled; {coordinates must be at most this big}
//!
//! @ First we do a simple preprocessing step. The segment numbers inserted
//! here will propagate to all descendants of cubics that are split into
//! subintervals. These numbers must be nonzero, but otherwise they are
//! present merely for diagnostic purposes. The cubic from |p| to~|q|
//! that represents ``time interval'' |(t-1)..t| usually has |left_type(q)=t|,
//! except when |t| is too large to be stored in a quarterword.
//!
//! @d procrustes(#)==@+if abs(#)>=dmax then
//!   if abs(#)>max_allowed then
//!     begin chopped:=1;
//!     if #>0 then #:=max_allowed@+else #:=-max_allowed;
//!     end
//!   else if chopped=0 then chopped:=-1
//!
//! @<Truncate the values of all coordinates that exceed...@>=
//! p:=cur_spec; k:=1; chopped:=0; dmax:=half(max_allowed);
//! repeat procrustes(left_x(p)); procrustes(left_y(p));
//! procrustes(x_coord(p)); procrustes(y_coord(p));
//! procrustes(right_x(p)); procrustes(right_y(p));@/
//! p:=link(p); left_type(p):=k;
//! if k<max_quarterword then incr(k)@+else k:=1;
//! until p=cur_spec;
//! if chopped>0 then
//!   begin print_err("Curve out of range");
//! @.Curve out of range@>
//!   help4("At least one of the coordinates in the path I'm about to")@/
//!     ("digitize was really huge (potentially bigger than 4095).")@/
//!     ("So I've cut it back to the maximum size.")@/
//!     ("The results will probably be pretty wild.");
//!   put_get_error;
//!   end
//!
//! @ We may need to get rid of constant ``dead'' cubics that clutter up
//! the data structure and interfere with autorounding.
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! procedure remove_cubic(@!p:pointer); {removes the cubic following~|p|}
//! var @!q:pointer; {the node that disappears}
//! begin q:=link(p); right_type(p):=right_type(q); link(p):=link(q);@/
//! x_coord(p):=x_coord(q); y_coord(p):=y_coord(q);@/
//! right_x(p):=right_x(q); right_y(p):=right_y(q);@/
//! free_node(q,knot_node_size);
//! end;
//!
//! @ The subdivision process proceeds by first swapping $x\swap-x$, if
//! necessary, to ensure that $x'\G0$; then swapping $y\swap-y$, if necessary,
//! to ensure that $y'\G0$; and finally swapping $x\swap y$, if necessary,
//! to ensure that $x'\G y'$.
//!
//! Recall that the octant codes have been defined in such a way that, for
//! example, |third_octant=first_octant+negate_x+switch_x_and_y|. The program
//! uses the fact that |negate_x<negate_y<switch_x_and_y| to handle ``double
//! negation'': If |c| is an octant code that possibly involves |negate_x|
//! and/or |negate_y|, but not |switch_x_and_y|, then negating~|y| changes~|c|
//! either to |c+negate_y| or |c-negate_y|, depending on whether
//! |c<=negate_y| or |c>negate_y|. Octant codes are always greater than zero.
//!
//! The first step is to subdivide on |x| and |y| only, so that horizontal
//! and vertical autorounding can be done before we compare $x'$ to $y'$.
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! @t\4@>@<Declare the procedure called |split_cubic|@>@;
//! procedure quadrant_subdivide;
//! label continue,exit;
//! var @!p,@!q,@!r,@!s,@!pp,@!qq:pointer; {for traversing the lists}
//! @!first_x,@!first_y:scaled; {unnegated coordinates of node |cur_spec|}
//! @!del1,@!del2,@!del3,@!del,@!dmax:scaled; {proportional to the control
//!   points of a quadratic derived from a cubic}
//! @!t:fraction; {where a quadratic crosses zero}
//! @!dest_x,@!dest_y:scaled; {final values of |x| and |y| in the current cubic}
//! @!constant_x:boolean; {is |x| constant between |p| and |q|?}
//! begin p:=cur_spec; first_x:=x_coord(cur_spec); first_y:=y_coord(cur_spec);
//! repeat continue: q:=link(p);
//! @<Subdivide the cubic between |p| and |q| so that the results travel
//!   toward the right halfplane@>;
//! @<Subdivide all cubics between |p| and |q| so that the results travel
//!   toward the first quadrant; but |return| or |goto continue| if the
//!   cubic from |p| to |q| was dead@>;
//! p:=q;
//! until p=cur_spec;
//! exit:end;
//!
//! @ All three subdivision processes are similar, so it's possible to
//! get the general idea by studying the first one (which is the simplest).
//! The calculation makes use of the fact that the derivatives of
//! Bernshte{\u\i}n polynomials satisfy
//! $B'(z_0,z_1,\ldots,z_n;t)=nB(z_1-z_0,\ldots,z_n-z_{n-1};t)$.
//!
//! When this routine begins, |right_type(p)| is |explicit|; we should
//! set |right_type(p):=first_octant|. However, no assignment is made,
//! because |explicit=first_octant|. The author apologizes for using
//! such trickery here; it is really hard to do redundant computations
//! just for the sake of purity.
//!
//! @<Subdivide the cubic between |p| and |q| so that the results travel
//!   toward the right halfplane...@>=
//! if q=cur_spec then
//!   begin dest_x:=first_x; dest_y:=first_y;
//!   end
//! else  begin dest_x:=x_coord(q); dest_y:=y_coord(q);
//!   end;
//! del1:=right_x(p)-x_coord(p); del2:=left_x(q)-right_x(p);
//! del3:=dest_x-left_x(q);
//! @<Scale up |del1|, |del2|, and |del3| for greater accuracy;
//!   also set |del| to the first nonzero element of |(del1,del2,del3)|@>;
//! if del=0 then constant_x:=true
//! else  begin constant_x:=false;
//!   if del<0 then @<Complement the |x| coordinates of the
//!     cubic between |p| and~|q|@>;
//!   t:=crossing_point(del1,del2,del3);
//!   if t<fraction_one then
//!     @<Subdivide the cubic with respect to $x'$, possibly twice@>;
//!   end
//!
//! @ If |del1=del2=del3=0|, it's impossible to obey the title of this
//! section. We just set |del=0| in that case.
//! @^inner loop@>
//!
//! @<Scale up |del1|, |del2|, and |del3| for greater accuracy...@>=
//! if del1<>0 then del:=del1
//! else if del2<>0 then del:=del2
//! else del:=del3;
//! if del<>0 then
//!   begin dmax:=abs(del1);
//!   if abs(del2)>dmax then dmax:=abs(del2);
//!   if abs(del3)>dmax then dmax:=abs(del3);
//!   while dmax<fraction_half do
//!     begin double(dmax); double(del1); double(del2); double(del3);
//!     end;
//!   end
//!
//! @ During the subdivision phases of |make_spec|, the |x_coord| and |y_coord|
//! fields of node~|q| are not transformed to agree with the octant
//! stated in |right_type(p)|; they remain consistent with |right_type(q)|.
//! But |left_x(q)| and |left_y(q)| are governed by |right_type(p)|.
//!
//! @<Complement the |x| coordinates...@>=
//! begin negate(x_coord(p)); negate(right_x(p));
//! negate(left_x(q));@/
//! negate(del1); negate(del2); negate(del3);@/
//! negate(dest_x);
//! right_type(p):=first_octant+negate_x;
//! end
//!
//! @ When a cubic is split at a |fraction| value |t|, we obtain two cubics
//! whose B\'ezier control points are obtained by a generalization of the
//! bisection process: The formula
//! `$z_k^{(j+1)}={1\over2}(z_k^{(j)}+z\k^{(j)})$' becomes
//! `$z_k^{(j+1)}=t[z_k^{(j)},z\k^{(j)}]$'.
//!
//! It is convenient to define a \.{WEB} macro |t_of_the_way| such that
//! |t_of_the_way(a)(b)| expands to |a-(a-b)*t|, i.e., to |t[a,b]|.
//!
//! If |0<=t<=1|, the quantity |t[a,b]| is always between |a| and~|b|, even in
//! the presence of rounding errors. Our subroutines
//! also obey the identity |t[a,b]+t[b,a]=a+b|.
//!
//! @d t_of_the_way_end(#)==#,t@=)@>
//! @d t_of_the_way(#)==#-take_fraction@=(@>#-t_of_the_way_end
//!
//! @<Declare the procedure called |split_cubic|@>=
//! procedure split_cubic(@!p:pointer;@!t:fraction;
//!   @!xq,@!yq:scaled); {splits the cubic after |p|}
//! var @!v:scaled; {an intermediate value}
//! @!q,@!r:pointer; {for list manipulation}
//! begin q:=link(p); r:=get_node(knot_node_size); link(p):=r; link(r):=q;@/
//! left_type(r):=left_type(q); right_type(r):=right_type(p);@#
//! v:=t_of_the_way(right_x(p))(left_x(q));
//! right_x(p):=t_of_the_way(x_coord(p))(right_x(p));
//! left_x(q):=t_of_the_way(left_x(q))(xq);
//! left_x(r):=t_of_the_way(right_x(p))(v);
//! right_x(r):=t_of_the_way(v)(left_x(q));
//! x_coord(r):=t_of_the_way(left_x(r))(right_x(r));@#
//! v:=t_of_the_way(right_y(p))(left_y(q));
//! right_y(p):=t_of_the_way(y_coord(p))(right_y(p));
//! left_y(q):=t_of_the_way(left_y(q))(yq);
//! left_y(r):=t_of_the_way(right_y(p))(v);
//! right_y(r):=t_of_the_way(v)(left_y(q));
//! y_coord(r):=t_of_the_way(left_y(r))(right_y(r));
//! end;
//!
//! @ Since $x'(t)$ is a quadratic equation, it can cross through zero
//! at~most twice. When it does cross zero, we make doubly sure that the
//! derivative is really zero at the splitting point, in case rounding errors
//! have caused the split cubic to have an apparently nonzero derivative.
//! We also make sure that the split cubic is monotonic.
//!
//! @<Subdivide the cubic with respect to $x'$, possibly twice@>=
//! begin split_cubic(p,t,dest_x,dest_y); r:=link(p);
//! if right_type(r)>negate_x then right_type(r):=first_octant
//! else right_type(r):=first_octant+negate_x;
//! if x_coord(r)<x_coord(p) then x_coord(r):=x_coord(p);
//! left_x(r):=x_coord(r);
//! if right_x(p)>x_coord(r) then right_x(p):=x_coord(r);
//!  {we always have |x_coord(p)<=right_x(p)|}
//! negate(x_coord(r)); right_x(r):=x_coord(r);
//! negate(left_x(q)); negate(dest_x);@/
//! del2:=t_of_the_way(del2)(del3);
//!   {now |0,del2,del3| represent $x'$ on the remaining interval}
//! if del2>0 then del2:=0;
//! t:=crossing_point(0,-del2,-del3);
//! if t<fraction_one then @<Subdivide the cubic a second time
//!   with respect to $x'$@>
//! else begin if x_coord(r)>dest_x then
//!     begin x_coord(r):=dest_x; left_x(r):=-x_coord(r); right_x(r):=x_coord(r);
//!     end;
//!   if left_x(q)>dest_x then left_x(q):=dest_x
//!   else if left_x(q)<x_coord(r) then left_x(q):=x_coord(r);
//!   end;
//! end
//!
//! @ @<Subdivide the cubic a second time with respect to $x'$@>=
//! begin split_cubic(r,t,dest_x,dest_y); s:=link(r);
//! if x_coord(s)<dest_x then x_coord(s):=dest_x;
//! if x_coord(s)<x_coord(r) then x_coord(s):=x_coord(r);
//! right_type(s):=right_type(p);
//! left_x(s):=x_coord(s); {now |x_coord(r)=right_x(r)<=left_x(s)|}
//! if left_x(q)<dest_x then left_x(q):=-dest_x
//! else if left_x(q)>x_coord(s) then left_x(q):=-x_coord(s)
//! else negate(left_x(q));
//! negate(x_coord(s)); right_x(s):=x_coord(s);
//! end
//!
//! @ The process of subdivision with respect to $y'$ is like that with respect
//! to~$x'$, with the slight additional complication that two or three cubics
//! might now appear between |p| and~|q|.
//!
//! @<Subdivide all cubics between |p| and |q| so that the results travel
//!   toward the first quadrant...@>=
//! pp:=p;
//! repeat qq:=link(pp);
//! abnegate(x_coord(qq),y_coord(qq),right_type(qq),right_type(pp));
//! dest_x:=cur_x; dest_y:=cur_y;@/
//! del1:=right_y(pp)-y_coord(pp); del2:=left_y(qq)-right_y(pp);
//! del3:=dest_y-left_y(qq);
//! @<Scale up |del1|, |del2|, and |del3| for greater accuracy;
//!   also set |del| to the first nonzero element of |(del1,del2,del3)|@>;
//! if del<>0 then {they weren't all zero}
//!   begin if del<0 then @<Complement the |y| coordinates of the
//!     cubic between |pp| and~|qq|@>;
//!   t:=crossing_point(del1,del2,del3);
//!   if t<fraction_one then
//!     @<Subdivide the cubic with respect to $y'$, possibly twice@>;
//!   end
//! else @<Do any special actions needed when |y| is constant;
//!   |return| or |goto continue| if a dead cubic from |p| to |q| is removed@>;
//! pp:=qq;
//! until pp=q;
//! if constant_x then @<Correct the octant code in segments with decreasing |y|@>
//!
//! @ @<Complement the |y| coordinates...@>=
//! begin negate(y_coord(pp)); negate(right_y(pp));
//! negate(left_y(qq));@/
//! negate(del1); negate(del2); negate(del3);@/
//! negate(dest_y);
//! right_type(pp):=right_type(pp)+negate_y;
//! end
//!
//! @ @<Subdivide the cubic with respect to $y'$, possibly twice@>=
//! begin split_cubic(pp,t,dest_x,dest_y); r:=link(pp);
//! if right_type(r)>negate_y then right_type(r):=right_type(r)-negate_y
//! else right_type(r):=right_type(r)+negate_y;
//! if y_coord(r)<y_coord(pp) then y_coord(r):=y_coord(pp);
//! left_y(r):=y_coord(r);
//! if right_y(pp)>y_coord(r) then right_y(pp):=y_coord(r);
//!  {we always have |y_coord(pp)<=right_y(pp)|}
//! negate(y_coord(r)); right_y(r):=y_coord(r);
//! negate(left_y(qq)); negate(dest_y);@/
//! if x_coord(r)<x_coord(pp) then x_coord(r):=x_coord(pp)
//! else if x_coord(r)>dest_x then x_coord(r):=dest_x;
//! if left_x(r)>x_coord(r) then
//!   begin left_x(r):=x_coord(r);
//!   if right_x(pp)>x_coord(r) then right_x(pp):=x_coord(r);
//!   end;
//! if right_x(r)<x_coord(r) then
//!   begin right_x(r):=x_coord(r);
//!   if left_x(qq)<x_coord(r) then left_x(qq):=x_coord(r);
//!   end;
//! del2:=t_of_the_way(del2)(del3);
//!   {now |0,del2,del3| represent $y'$ on the remaining interval}
//! if del2>0 then del2:=0;
//! t:=crossing_point(0,-del2,-del3);
//! if t<fraction_one then @<Subdivide the cubic a second time
//!   with respect to $y'$@>
//! else begin if y_coord(r)>dest_y then
//!     begin y_coord(r):=dest_y; left_y(r):=-y_coord(r); right_y(r):=y_coord(r);
//!     end;
//!   if left_y(qq)>dest_y then left_y(qq):=dest_y
//!   else if left_y(qq)<y_coord(r) then left_y(qq):=y_coord(r);
//!   end;
//! end
//!
//! @ @<Subdivide the cubic a second time with respect to $y'$@>=
//! begin split_cubic(r,t,dest_x,dest_y); s:=link(r);@/
//! if y_coord(s)<dest_y then y_coord(s):=dest_y;
//! if y_coord(s)<y_coord(r) then y_coord(s):=y_coord(r);
//! right_type(s):=right_type(pp);
//! left_y(s):=y_coord(s); {now |y_coord(r)=right_y(r)<=left_y(s)|}
//! if left_y(qq)<dest_y then left_y(qq):=-dest_y
//! else if left_y(qq)>y_coord(s) then left_y(qq):=-y_coord(s)
//! else negate(left_y(qq));
//! negate(y_coord(s)); right_y(s):=y_coord(s);
//! if x_coord(s)<x_coord(r) then x_coord(s):=x_coord(r)
//! else if x_coord(s)>dest_x then x_coord(s):=dest_x;
//! if left_x(s)>x_coord(s) then
//!   begin left_x(s):=x_coord(s);
//!   if right_x(r)>x_coord(s) then right_x(r):=x_coord(s);
//!   end;
//! if right_x(s)<x_coord(s) then
//!   begin right_x(s):=x_coord(s);
//!   if left_x(qq)<x_coord(s) then left_x(qq):=x_coord(s);
//!   end;
//! end
//!
//! @ If the cubic is constant in $y$ and increasing in $x$, we have classified
//! it as traveling in the first octant. If the cubic is constant
//! in~$y$ and decreasing in~$x$, it is desirable to classify it as traveling
//! in the fifth octant (not the fourth), because autorounding will be consistent
//! with respect to doublepaths only if the octant number changes by four when
//! the path is reversed. Therefore we negate the $y$~coordinates
//! when they are constant but the curve is decreasing in~$x$; this gives
//! the desired result except in pathological paths.
//!
//! If the cubic is ``dead,'' i.e., constant in both |x| and |y|, we remove
//! it unless it is the only cubic in the entire path. We |goto continue|
//! if it wasn't the final cubic, so that the test |p=cur_spec| does not
//! falsely imply that all cubics have been processed.
//!
//! @<Do any special actions needed when |y| is constant...@>=
//! if constant_x then {|p=pp|, |q=qq|, and the cubic is dead}
//!   begin if q<>p then
//!     begin remove_cubic(p); {remove the dead cycle and recycle node |q|}
//!     if cur_spec<>q then goto continue
//!     else  begin cur_spec:=p; return;
//!       end; {the final cubic was dead and is gone}
//!     end;
//!   end
//! else if not odd(right_type(pp)) then {the $x$ coordinates were negated}
//!   @<Complement the |y| coordinates...@>
//!
//! @ A similar correction to octant codes deserves to be made when |x| is
//! constant and |y| is decreasing.
//!
//! @<Correct the octant code in segments with decreasing |y|@>=
//! begin pp:=p;
//! repeat qq:=link(pp);
//! if right_type(pp)>negate_y then {the $y$ coordinates were negated}
//!   begin right_type(pp):=right_type(pp)+negate_x;
//!   negate(x_coord(pp)); negate(right_x(pp)); negate(left_x(qq));
//!   end;
//! pp:=qq;
//! until pp=q;
//! end
//!
//! @ Finally, the process of subdividing to make $x'\G y'$ is like the other
//! two subdivisions, with a few new twists. We skew the coordinates at this time.
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! procedure octant_subdivide;
//! var @!p,@!q,@!r,@!s:pointer; {for traversing the lists}
//! @!del1,@!del2,@!del3,@!del,@!dmax:scaled; {proportional to the control
//!   points of a quadratic derived from a cubic}
//! @!t:fraction; {where a quadratic crosses zero}
//! @!dest_x,@!dest_y:scaled; {final values of |x| and |y| in the current cubic}
//! begin p:=cur_spec;
//! repeat q:=link(p);@/
//! x_coord(p):=x_coord(p)-y_coord(p);
//! right_x(p):=right_x(p)-right_y(p);
//! left_x(q):=left_x(q)-left_y(q);@/
//! @<Subdivide the cubic between |p| and |q| so that the results travel
//!   toward the first octant@>;
//! p:=q;
//! until p=cur_spec;
//! end;
//!
//! @ @<Subdivide the cubic between |p| and |q| so that the results travel
//!   toward the first octant@>=
//! @<Set up the variables |(del1,del2,del3)| to represent $x'-y'$@>;
//! @<Scale up |del1|, |del2|, and |del3| for greater accuracy;
//!   also set |del| to the first nonzero element of |(del1,del2,del3)|@>;
//! if del<>0 then {they weren't all zero}
//!   begin if del<0 then @<Swap the |x| and |y| coordinates of the
//!     cubic between |p| and~|q|@>;
//!   t:=crossing_point(del1,del2,del3);
//!   if t<fraction_one then
//!     @<Subdivide the cubic with respect to $x'-y'$, possibly twice@>;
//!   end
//!
//! @ @<Set up the variables |(del1,del2,del3)| to represent $x'-y'$@>=
//! if q=cur_spec then
//!   begin unskew(x_coord(q),y_coord(q),right_type(q));
//!   skew(cur_x,cur_y,right_type(p)); dest_x:=cur_x; dest_y:=cur_y;
//!   end
//! else  begin abnegate(x_coord(q),y_coord(q),right_type(q),right_type(p));
//!   dest_x:=cur_x-cur_y; dest_y:=cur_y;
//!   end;
//! del1:=right_x(p)-x_coord(p); del2:=left_x(q)-right_x(p);
//! del3:=dest_x-left_x(q)
//!
//! @ The swapping here doesn't simply interchange |x| and |y| values,
//! because the coordinates are skewed. It turns out that this is easier
//! than ordinary swapping, because it can be done in two assignment statements
//! rather than three.
//!
//! @ @<Swap the |x| and |y| coordinates...@>=
//! begin y_coord(p):=x_coord(p)+y_coord(p); negate(x_coord(p));@/
//! right_y(p):=right_x(p)+right_y(p); negate(right_x(p));@/
//! left_y(q):=left_x(q)+left_y(q); negate(left_x(q));@/
//! negate(del1); negate(del2); negate(del3);@/
//! dest_y:=dest_x+dest_y; negate(dest_x);@/
//! right_type(p):=right_type(p)+switch_x_and_y;
//! end
//!
//! @ A somewhat tedious case analysis is carried out here to make sure that
//! nasty rounding errors don't destroy our assumptions of monotonicity.
//!
//! @<Subdivide the cubic with respect to $x'-y'$, possibly twice@>=
//! begin split_cubic(p,t,dest_x,dest_y); r:=link(p);
//! if right_type(r)>switch_x_and_y then right_type(r):=right_type(r)-switch_x_and_y
//! else right_type(r):=right_type(r)+switch_x_and_y;
//! if y_coord(r)<y_coord(p) then y_coord(r):=y_coord(p)
//! else if y_coord(r)>dest_y then y_coord(r):=dest_y;
//! if x_coord(p)+y_coord(r)>dest_x+dest_y then
//!   y_coord(r):=dest_x+dest_y-x_coord(p);
//! if left_y(r)>y_coord(r) then
//!   begin left_y(r):=y_coord(r);
//!   if right_y(p)>y_coord(r) then right_y(p):=y_coord(r);
//!   end;
//! if right_y(r)<y_coord(r) then
//!   begin right_y(r):=y_coord(r);
//!   if left_y(q)<y_coord(r) then left_y(q):=y_coord(r);
//!   end;
//! if x_coord(r)<x_coord(p) then x_coord(r):=x_coord(p)
//! else if x_coord(r)+y_coord(r)>dest_x+dest_y then
//!   x_coord(r):=dest_x+dest_y-y_coord(r);
//! left_x(r):=x_coord(r);
//! if right_x(p)>x_coord(r) then right_x(p):=x_coord(r);
//!  {we always have |x_coord(p)<=right_x(p)|}
//! y_coord(r):=y_coord(r)+x_coord(r); right_y(r):=right_y(r)+x_coord(r);@/
//! negate(x_coord(r)); right_x(r):=x_coord(r);@/
//! left_y(q):=left_y(q)+left_x(q); negate(left_x(q));@/
//! dest_y:=dest_y+dest_x; negate(dest_x);
//! if right_y(r)<y_coord(r) then
//!   begin right_y(r):=y_coord(r);
//!   if left_y(q)<y_coord(r) then left_y(q):=y_coord(r);
//!   end;
//! del2:=t_of_the_way(del2)(del3);
//!   {now |0,del2,del3| represent $x'-y'$ on the remaining interval}
//! if del2>0 then del2:=0;
//! t:=crossing_point(0,-del2,-del3);
//! if t<fraction_one then
//!   @<Subdivide the cubic a second time with respect to $x'-y'$@>
//! else begin if x_coord(r)>dest_x then
//!     begin x_coord(r):=dest_x; left_x(r):=-x_coord(r); right_x(r):=x_coord(r);
//!     end;
//!   if left_x(q)>dest_x then left_x(q):=dest_x
//!   else if left_x(q)<x_coord(r) then left_x(q):=x_coord(r);
//!   end;
//! end
//!
//! @ @<Subdivide the cubic a second time with respect to $x'-y'$@>=
//! begin split_cubic(r,t,dest_x,dest_y); s:=link(r);@/
//! if y_coord(s)<y_coord(r) then y_coord(s):=y_coord(r)
//! else if y_coord(s)>dest_y then y_coord(s):=dest_y;
//! if x_coord(r)+y_coord(s)>dest_x+dest_y then
//!   y_coord(s):=dest_x+dest_y-x_coord(r);
//! if left_y(s)>y_coord(s) then
//!   begin left_y(s):=y_coord(s);
//!   if right_y(r)>y_coord(s) then right_y(r):=y_coord(s);
//!   end;
//! if right_y(s)<y_coord(s) then
//!   begin right_y(s):=y_coord(s);
//!   if left_y(q)<y_coord(s) then left_y(q):=y_coord(s);
//!   end;
//! if x_coord(s)+y_coord(s)>dest_x+dest_y then x_coord(s):=dest_x+dest_y-y_coord(s)
//! else begin if x_coord(s)<dest_x then x_coord(s):=dest_x;
//!   if x_coord(s)<x_coord(r) then x_coord(s):=x_coord(r);
//!   end;
//! right_type(s):=right_type(p);
//! left_x(s):=x_coord(s); {now |x_coord(r)=right_x(r)<=left_x(s)|}
//! if left_x(q)<dest_x then
//!   begin left_y(q):=left_y(q)+dest_x; left_x(q):=-dest_x;@+end
//! else if left_x(q)>x_coord(s) then
//!   begin left_y(q):=left_y(q)+x_coord(s); left_x(q):=-x_coord(s);@+end
//! else begin left_y(q):=left_y(q)+left_x(q); negate(left_x(q));@+end;
//! y_coord(s):=y_coord(s)+x_coord(s); right_y(s):=right_y(s)+x_coord(s);@/
//! negate(x_coord(s)); right_x(s):=x_coord(s);@/
//! if right_y(s)<y_coord(s) then
//!   begin right_y(s):=y_coord(s);
//!   if left_y(q)<y_coord(s) then left_y(q):=y_coord(s);
//!   end;
//! end
//!
//! @ It's time now to consider ``autorounding,'' which tries to make horizontal,
//! vertical, and diagonal tangents occur at places that will produce appropriate
//! images after the curve is digitized.
//!
//! The first job is to fix things so that |x(t)| plus the horizontal pen offset
//! is an integer multiple of the
//! current ``granularity'' when the derivative $x'(t)$ crosses through zero.
//! The given cyclic path contains regions where $x'(t)\G0$ and regions
//! where $x'(t)\L0$. The |quadrant_subdivide| routine is called into action
//! before any of the path coordinates have been skewed, but some of them
//! may have been negated. In regions where $x'(t)\G0$ we have |right_type=
//! first_octant| or |right_type=eighth_octant|; in regions where $x'(t)\L0$,
//! we have |right_type=fifth_octant| or |right_type=fourth_octant|.
//!
//! Within any such region the transformed $x$ values increase monotonically
//! from, say, $x_0$ to~$x_1$. We want to modify things by applying a linear
//! transformation to all $x$ coordinates in the region, after which
//! the $x$ values will increase monotonically from round$(x_0)$ to round$(x_1)$.
//!
//! This rounding scheme sounds quite simple, and it usually is. But several
//! complications can arise that might make the task more difficult. In the
//! first place, autorounding is inappropriate at cusps where $x'$ jumps
//! discontinuously past zero without ever being zero. In the second place,
//! the current pen might be unsymmetric in such a way that $x$ coordinates
//! should round differently in different parts of the curve.
//! These considerations imply that round$(x_0)$ might be greater
//! than round$(x_1)$, even though $x_0\L x_1$; in such cases we do not want
//! to carry out the linear transformation. Furthermore, it's possible to have
//! round$(x_1)-\hbox{round} (x_0)$ positive but much greater than $x_1-x_0$;
//! then the transformation might distort the curve drastically, and again we
//! want to avoid it. Finally, the rounded points must be consistent between
//! adjacent regions, hence we can't transform one region without knowing
//! about its neighbors.
//!
//! To handle all these complications, we must first look at the whole
//! cycle and choose rounded $x$ values that are ``safe.'' The following
//! procedure does this: Given $m$~values $(b_0,b_1,\ldots,b_{m-1})$ before
//! rounding and $m$~corresponding values $(a_0,a_1,\ldots,a_{m-1})$ that would
//! be desirable after rounding, the |make_safe| routine sets $a$'s to $b$'s
//! if necessary so that $0\L(a\k-a_k)/(b\k-b_k)\L2$ afterwards. It is
//! symmetric under cyclic permutation, reversal, and/or negation of the inputs.
//! (Instead of |a|, |b|, and~|m|, the program uses the names |after|,
//! |before|, and |cur_rounding_ptr|.)
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! procedure make_safe;
//! var @!k:0..max_wiggle; {runs through the list of inputs}
//! @!all_safe:boolean; {does everything look OK so far?}
//! @!next_a:scaled; {|after[k]| before it might have changed}
//! @!delta_a,@!delta_b:scaled; {|after[k+1]-after[k]| and |before[k+1]-before[k]|}
//! begin before[cur_rounding_ptr]:=before[0]; {wrap around}
//! node_to_round[cur_rounding_ptr]:=node_to_round[0];
//! repeat after[cur_rounding_ptr]:=after[0]; all_safe:=true; next_a:=after[0];
//! for k:=0 to cur_rounding_ptr-1 do
//!   begin delta_b:=before[k+1]-before[k];
//!   if delta_b>=0 then delta_a:=after[k+1]-next_a
//!   else delta_a:=next_a-after[k+1];
//!   next_a:=after[k+1];
//!   if (delta_a<0)or(delta_a>abs(delta_b+delta_b)) then
//!     begin all_safe:=false; after[k]:=before[k];
//!     if k=cur_rounding_ptr-1 then after[0]:=before[0]
//!     else after[k+1]:=before[k+1];
//!     end;
//!   end;
//! until all_safe;
//! end;
//!
//! @ The global arrays used by |make_safe| are accompanied by an array of
//! pointers into the current knot list.
//!
//! @<Glob...@>=
//! @!before,@!after:array[0..max_wiggle] of scaled; {data for |make_safe|}
//! @!node_to_round:array[0..max_wiggle] of pointer; {reference back to the path}
//! @!cur_rounding_ptr:0..max_wiggle; {how many are being used}
//! @!max_rounding_ptr:0..max_wiggle; {how many have been used}
//!
//! @ @<Set init...@>=
//! max_rounding_ptr:=0;
//!
//! @ New entries go into the tables via the |before_and_after| routine:
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! procedure before_and_after(@!b,@!a:scaled;@!p:pointer);
//! begin if cur_rounding_ptr=max_rounding_ptr then
//!   if max_rounding_ptr<max_wiggle then incr(max_rounding_ptr)
//!   else overflow("rounding table size",max_wiggle);
//! @:METAFONT capacity exceeded rounding table size}{\quad rounding table size@>
//! after[cur_rounding_ptr]:=a; before[cur_rounding_ptr]:=b;
//! node_to_round[cur_rounding_ptr]:=p; incr(cur_rounding_ptr);
//! end;
//!
//! @ A global variable called |cur_gran| is used instead of |internal[
//! granularity]|, because we want to work with a number that's guaranteed to
//! be positive.
//!
//! @<Glob...@>=
//! @!cur_gran:scaled; {the current granularity (which normally is |unity|)}
//!
//! @ The |good_val| function computes a number |a| that's as close as
//! possible to~|b|, with the property that |a+o| is a multiple of
//! |cur_gran|.
//!
//! If we assume that |cur_gran| is even (since it will in fact be a multiple
//! of |unity| in all reasonable applications), we have the identity
//! |good_val(-b-1,-o)=-good_val(b,o)|.
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! function good_val(@!b,@!o:scaled):scaled;
//! var @!a:scaled; {accumulator}
//! begin a:=b+o;
//! if a>=0 then a:=a-(a mod cur_gran)-o
//! else a:=a+((-(a+1)) mod cur_gran)-cur_gran+1-o;
//! if b-a<a+cur_gran-b then good_val:=a
//! else good_val:=a+cur_gran;
//! end;
//!
//! @ When we're rounding a doublepath, we might need to compromise between
//! two opposing tendencies, if the pen thickness is not a multiple of the
//! granularity. The following ``compromise'' adjustment, suggested by
//! John Hobby, finds the best way out of the dilemma. (Only the value
//! @^Hobby, John Douglas@>
//! modulo |cur_gran| is relevant in our applications, so the result turns
//! out to be essentially symmetric in |u| and~|v|.)
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! function compromise(@!u,@!v:scaled):scaled;
//! begin compromise:=half(good_val(u+u,-u-v));
//! end;
//!
//! @ Here, then, is the procedure that rounds $x$ coordinates as described;
//! it does the same for $y$ coordinates too, independently.
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! procedure xy_round;
//! var @!p,@!q:pointer; {list manipulation registers}
//! @!b,@!a:scaled; {before and after values}
//! @!pen_edge:scaled; {offset that governs rounding}
//! @!alpha:fraction; {coefficient of linear transformation}
//! begin cur_gran:=abs(internal[granularity]);
//! if cur_gran=0 then cur_gran:=unity;
//! p:=cur_spec; cur_rounding_ptr:=0;
//! repeat q:=link(p);
//! @<If node |q| is a transition point for |x| coordinates,
//!   compute and save its before-and-after coordinates@>;
//! p:=q;
//! until p=cur_spec;
//! if cur_rounding_ptr>0 then @<Transform the |x| coordinates@>;
//! p:=cur_spec; cur_rounding_ptr:=0;
//! repeat q:=link(p);
//! @<If node |q| is a transition point for |y| coordinates,
//!   compute and save its before-and-after coordinates@>;
//! p:=q;
//! until p=cur_spec;
//! if cur_rounding_ptr>0 then @<Transform the |y| coordinates@>;
//! end;
//!
//! @ When |x| has been negated, the |octant| codes are even. We allow
//! for an error of up to .01 pixel (i.e., 655 |scaled| units) in the
//! derivative calculations at transition nodes.
//!
//! @<If node |q| is a transition point for |x| coordinates...@>=
//! if odd(right_type(p))<>odd(right_type(q)) then
//!   begin if odd(right_type(q)) then b:=x_coord(q)@+else b:=-x_coord(q);
//!   if (abs(x_coord(q)-right_x(q))<655)or@|
//!     (abs(x_coord(q)+left_x(q))<655) then
//!     @<Compute before-and-after |x| values based on the current pen@>
//!   else a:=b;
//!   if abs(a)>max_allowed then
//!     if a>0 then a:=max_allowed@+else a:=-max_allowed;
//!   before_and_after(b,a,q);
//!   end
//!
//! @ When we study the data representation for pens, we'll learn that the
//! |x|~coordinate of the current pen's west edge is
//! $$\hbox{|y_coord(link(cur_pen+seventh_octant))|},$$
//! and that there are similar ways to address other important offsets.
//!
//! @d north_edge(#)==y_coord(link(#+fourth_octant))
//! @d south_edge(#)==y_coord(link(#+first_octant))
//! @d east_edge(#)==y_coord(link(#+second_octant))
//! @d west_edge(#)==y_coord(link(#+seventh_octant))
//!
//! @<Compute before-and-after |x| values based on the current pen@>=
//! begin if cur_pen=null_pen then pen_edge:=0
//! else if cur_path_type=double_path_code then
//!   pen_edge:=compromise(east_edge(cur_pen),west_edge(cur_pen))
//! else if odd(right_type(q)) then pen_edge:=west_edge(cur_pen)
//! else pen_edge:=east_edge(cur_pen);
//! a:=good_val(b,pen_edge);
//! end
//!
//! @  The monotone transformation computed here with fixed-point arithmetic is
//! guaranteed to take consecutive |before| values $(b,b')$ into consecutive
//! |after| values $(a,a')$, even in the presence of rounding errors,
//! as long as $\vert b-b'\vert<2^{28}$.
//!
//! @<Transform the |x| coordinates@>=
//! begin make_safe;
//! repeat decr(cur_rounding_ptr);
//! if (after[cur_rounding_ptr]<>before[cur_rounding_ptr])or@|
//!  (after[cur_rounding_ptr+1]<>before[cur_rounding_ptr+1]) then
//!   begin p:=node_to_round[cur_rounding_ptr];
//!   if odd(right_type(p)) then
//!     begin b:=before[cur_rounding_ptr]; a:=after[cur_rounding_ptr];
//!     end
//!   else  begin b:=-before[cur_rounding_ptr]; a:=-after[cur_rounding_ptr];
//!     end;
//!   if before[cur_rounding_ptr]=before[cur_rounding_ptr+1] then
//!     alpha:=fraction_one
//!   else alpha:=make_fraction(after[cur_rounding_ptr+1]-after[cur_rounding_ptr],@|
//!     before[cur_rounding_ptr+1]-before[cur_rounding_ptr]);
//!   repeat x_coord(p):=take_fraction(alpha,x_coord(p)-b)+a;
//!   right_x(p):=take_fraction(alpha,right_x(p)-b)+a;
//!   p:=link(p); left_x(p):=take_fraction(alpha,left_x(p)-b)+a;
//!   until p=node_to_round[cur_rounding_ptr+1];
//!   end;
//! until cur_rounding_ptr=0;
//! end
//!
//! @ When |y| has been negated, the |octant| codes are |>negate_y|. Otherwise
//! these routines are essentially identical to the routines for |x| coordinates
//! that we have just seen.
//!
//! @<If node |q| is a transition point for |y| coordinates...@>=
//! if (right_type(p)>negate_y)<>(right_type(q)>negate_y) then
//!   begin if right_type(q)<=negate_y then b:=y_coord(q)@+else b:=-y_coord(q);
//!   if (abs(y_coord(q)-right_y(q))<655)or@|
//!     (abs(y_coord(q)+left_y(q))<655) then
//!     @<Compute before-and-after |y| values based on the current pen@>
//!   else a:=b;
//!   if abs(a)>max_allowed then
//!     if a>0 then a:=max_allowed@+else a:=-max_allowed;
//!   before_and_after(b,a,q);
//!   end
//!
//! @ @<Compute before-and-after |y| values based on the current pen@>=
//! begin if cur_pen=null_pen then pen_edge:=0
//! else if cur_path_type=double_path_code then
//!   pen_edge:=compromise(north_edge(cur_pen),south_edge(cur_pen))
//! else if right_type(q)<=negate_y then pen_edge:=south_edge(cur_pen)
//! else pen_edge:=north_edge(cur_pen);
//! a:=good_val(b,pen_edge);
//! end
//!
//! @ @<Transform the |y| coordinates@>=
//! begin make_safe;
//! repeat decr(cur_rounding_ptr);
//! if (after[cur_rounding_ptr]<>before[cur_rounding_ptr])or@|
//!  (after[cur_rounding_ptr+1]<>before[cur_rounding_ptr+1]) then
//!   begin p:=node_to_round[cur_rounding_ptr];
//!   if right_type(p)<=negate_y then
//!     begin b:=before[cur_rounding_ptr]; a:=after[cur_rounding_ptr];
//!     end
//!   else  begin b:=-before[cur_rounding_ptr]; a:=-after[cur_rounding_ptr];
//!     end;
//!   if before[cur_rounding_ptr]=before[cur_rounding_ptr+1] then
//!     alpha:=fraction_one
//!   else alpha:=make_fraction(after[cur_rounding_ptr+1]-after[cur_rounding_ptr],@|
//!     before[cur_rounding_ptr+1]-before[cur_rounding_ptr]);
//!   repeat y_coord(p):=take_fraction(alpha,y_coord(p)-b)+a;
//!   right_y(p):=take_fraction(alpha,right_y(p)-b)+a;
//!   p:=link(p); left_y(p):=take_fraction(alpha,left_y(p)-b)+a;
//!   until p=node_to_round[cur_rounding_ptr+1];
//!   end;
//! until cur_rounding_ptr=0;
//! end
//!
//! @ Rounding at diagonal tangents takes place after the subdivision into
//! octants is complete, hence after the coordinates have been skewed.
//! The details are somewhat tricky, because we want to round to points
//! whose skewed coordinates are halfway between integer multiples of
//! the granularity. Furthermore, both coordinates change when they are
//! rounded; this means we need a generalization of the |make_safe| routine,
//! ensuring safety in both |x| and |y|.
//!
//! In spite of these extra complications, we can take comfort in the fact
//! that the basic structure of the routine is the same as before.
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! procedure diag_round;
//! var @!p,@!q,@!pp:pointer; {list manipulation registers}
//! @!b,@!a,@!bb,@!aa,@!d,@!c,@!dd,@!cc:scaled; {before and after values}
//! @!pen_edge:scaled; {offset that governs rounding}
//! @!alpha,@!beta:fraction; {coefficients of linear transformation}
//! @!next_a:scaled; {|after[k]| before it might have changed}
//! @!all_safe:boolean; {does everything look OK so far?}
//! @!k:0..max_wiggle; {runs through before-and-after values}
//! @!first_x,@!first_y:scaled; {coordinates before rounding}
//! begin p:=cur_spec; cur_rounding_ptr:=0;
//! repeat q:=link(p);
//! @<If node |q| is a transition point between octants,
//!   compute and save its before-and-after coordinates@>;
//! p:=q;
//! until p=cur_spec;
//! if cur_rounding_ptr>0 then @<Transform the skewed coordinates@>;
//! end;
//!
//! @ We negate the skewed |x| coordinates in the before-and-after table when
//! the octant code is greater than |switch_x_and_y|.
//!
//! @<If node |q| is a transition point between octants...@>=
//! if right_type(p)<>right_type(q) then
//!   begin if right_type(q)>switch_x_and_y then b:=-x_coord(q)
//!   else b:=x_coord(q);
//!   if abs(right_type(q)-right_type(p))=switch_x_and_y then
//!     if (abs(x_coord(q)-right_x(q))<655)or(abs(x_coord(q)+left_x(q))<655) then
//!       @<Compute a good coordinate at a diagonal transition@>
//!     else a:=b
//!   else a:=b;
//!   before_and_after(b,a,q);
//!   end
//!
//! @ In octants whose code number is even, $x$~has been
//! negated; we want to round ambiguous cases downward instead of upward,
//! so that the rounding will be consistent with octants whose code
//! number is odd. This downward bias can be achieved by
//! subtracting~1 from the first argument of |good_val|.
//!
//! @d diag_offset(#)==x_coord(knil(link(cur_pen+#)))
//!
//! @<Compute a good coordinate at a diagonal transition@>=
//! begin if cur_pen=null_pen then pen_edge:=0
//! else if cur_path_type=double_path_code then @<Compute a compromise |pen_edge|@>
//! else if right_type(q)<=switch_x_and_y then pen_edge:=diag_offset(right_type(q))
//! else pen_edge:=-diag_offset(right_type(q));
//! if odd(right_type(q)) then a:=good_val(b,pen_edge+half(cur_gran))
//! else a:=good_val(b-1,pen_edge+half(cur_gran));
//! end
//!
//! @ (It seems a shame to compute these compromise offsets repeatedly. The
//! author would have stored them directly in the pen data structure, if the
//! granularity had been constant.)
//!
//! @<Compute a compromise...@>=
//! case right_type(q) of
//! first_octant,second_octant:pen_edge:=compromise(diag_offset(first_octant),@|
//!     -diag_offset(fifth_octant));
//! fifth_octant,sixth_octant:pen_edge:=-compromise(diag_offset(first_octant),@|
//!     -diag_offset(fifth_octant));
//! third_octant,fourth_octant:pen_edge:=compromise(diag_offset(fourth_octant),@|
//!     -diag_offset(eighth_octant));
//! seventh_octant,eighth_octant:pen_edge:=-compromise(diag_offset(fourth_octant),@|
//!     -diag_offset(eighth_octant));
//! end {there are no other cases}
//!
//! @ @<Transform the skewed coordinates@>=
//! begin p:=node_to_round[0]; first_x:=x_coord(p); first_y:=y_coord(p);
//! @<Make sure that all the diagonal roundings are safe@>;
//! for k:=0 to cur_rounding_ptr-1 do
//!   begin a:=after[k]; b:=before[k];
//!   aa:=after[k+1]; bb:=before[k+1];
//!   if (a<>b)or(aa<>bb) then
//!     begin p:=node_to_round[k]; pp:=node_to_round[k+1];
//!     @<Determine the before-and-after values of both coordinates@>;
//!     if b=bb then alpha:=fraction_one
//!     else alpha:=make_fraction(aa-a,bb-b);
//!     if d=dd then beta:=fraction_one
//!     else beta:=make_fraction(cc-c,dd-d);
//!     repeat x_coord(p):=take_fraction(alpha,x_coord(p)-b)+a;
//!     y_coord(p):=take_fraction(beta,y_coord(p)-d)+c;
//!     right_x(p):=take_fraction(alpha,right_x(p)-b)+a;
//!     right_y(p):=take_fraction(beta,right_y(p)-d)+c;
//!     p:=link(p); left_x(p):=take_fraction(alpha,left_x(p)-b)+a;
//!     left_y(p):=take_fraction(beta,left_y(p)-d)+c;
//!     until p=pp;
//!     end;
//!   end;
//! end
//!
//! @ In node |p|, the coordinates |(b,d)| will be rounded to |(a,c)|;
//! in node |pp|, the coordinates |(bb,dd)| will be rounded to |(aa,cc)|.
//! (We transform the values from node |pp| so that they agree with the
//! conventions of node |p|.)
//!
//! If |aa<>bb|, we know that |abs(right_type(p)-right_type(pp))=switch_x_and_y|.
//!
//! @<Determine the before-and-after values of both coordinates@>=
//! if aa=bb then
//!   begin if pp=node_to_round[0] then
//!     unskew(first_x,first_y,right_type(pp))
//!   else unskew(x_coord(pp),y_coord(pp),right_type(pp));
//!   skew(cur_x,cur_y,right_type(p));
//!   bb:=cur_x; aa:=bb; dd:=cur_y; cc:=dd;
//!   if right_type(p)>switch_x_and_y then
//!     begin b:=-b; a:=-a;
//!     end;
//!   end
//! else  begin if right_type(p)>switch_x_and_y then
//!     begin bb:=-bb; aa:=-aa; b:=-b; a:=-a;
//!     end;
//!   if pp=node_to_round[0] then dd:=first_y-bb@+else dd:=y_coord(pp)-bb;
//!   if odd(aa-bb) then
//!     if right_type(p)>switch_x_and_y then cc:=dd-half(aa-bb+1)
//!     else cc:=dd-half(aa-bb-1)
//!   else cc:=dd-half(aa-bb);
//!   end;
//! d:=y_coord(p);
//! if odd(a-b) then
//!   if right_type(p)>switch_x_and_y then c:=d-half(a-b-1)
//!   else c:=d-half(a-b+1)
//! else c:=d-half(a-b)
//!
//! @ @<Make sure that all the diagonal roundings are safe@>=
//! before[cur_rounding_ptr]:=before[0]; {cf.~|make_safe|}
//! node_to_round[cur_rounding_ptr]:=node_to_round[0];
//! repeat after[cur_rounding_ptr]:=after[0]; all_safe:=true; next_a:=after[0];
//! for k:=0 to cur_rounding_ptr-1 do
//!   begin a:=next_a; b:=before[k]; next_a:=after[k+1];
//!   aa:=next_a; bb:=before[k+1];
//!   if (a<>b)or(aa<>bb) then
//!     begin p:=node_to_round[k]; pp:=node_to_round[k+1];
//!     @<Determine the before-and-after values of both coordinates@>;
//!     if (aa<a)or(cc<c)or(aa-a>2*(bb-b))or(cc-c>2*(dd-d)) then
//!       begin all_safe:=false; after[k]:=before[k];
//!       if k=cur_rounding_ptr-1 then after[0]:=before[0]
//!       else after[k+1]:=before[k+1];
//!       end;
//!     end;
//!   end;
//! until all_safe
//!
//! @ Here we get rid of ``dead'' cubics, i.e., polynomials that don't move at
//! all when |t|~changes, since the subdivision process might have introduced
//! such things.  If the cycle reduces to a single point, however, we are left
//! with a single dead cubic that will not be removed until later.
//!
//! @<Remove dead cubics@>=
//! p:=cur_spec;
//! repeat continue: q:=link(p);
//! if p<>q then
//!   begin if x_coord(p)=right_x(p) then
//!    if y_coord(p)=right_y(p) then
//!     if x_coord(p)=left_x(q) then
//!      if y_coord(p)=left_y(q) then
//!     begin unskew(x_coord(q),y_coord(q),right_type(q));
//!     skew(cur_x,cur_y,right_type(p));
//!     if x_coord(p)=cur_x then if y_coord(p)=cur_y then
//!       begin remove_cubic(p); {remove the cubic following |p|}
//!       if q<>cur_spec then goto continue;
//!       cur_spec:=p; q:=p;
//!       end;
//!     end;
//!   end;
//! p:=q;
//! until p=cur_spec;
//!
//! @ Finally we come to the last steps of |make_spec|, when boundary nodes
//! are inserted between cubics that move in different octants. The main
//! complication remaining arises from consecutive cubics whose octants
//! are not adjacent; we should insert more than one octant boundary
//! at such sharp turns, so that the envelope-forming routine will work.
//!
//! For this purpose, conversion tables between numeric and Gray codes for
//! octants are desirable.
//!
//! @<Glob...@>=
//! @!octant_number:array[first_octant..sixth_octant] of 1..8;
//! @!octant_code:array[1..8] of first_octant..sixth_octant;
//!
//! @ @<Set init...@>=
//! octant_code[1]:=first_octant;
//! octant_code[2]:=second_octant;
//! octant_code[3]:=third_octant;
//! octant_code[4]:=fourth_octant;
//! octant_code[5]:=fifth_octant;
//! octant_code[6]:=sixth_octant;
//! octant_code[7]:=seventh_octant;
//! octant_code[8]:=eighth_octant;
//! for k:=1 to 8 do octant_number[octant_code[k]]:=k;
//!
//! @ The main loop for boundary insertion deals with three consecutive
//! nodes |p,q,r|.
//!
//! @<Insert octant boundaries and compute the turning number@>=
//! turning_number:=0;
//! p:=cur_spec; q:=link(p);
//! repeat r:=link(q);
//! if (right_type(p)<>right_type(q))or(q=r) then
//!   @<Insert one or more octant boundary nodes just before~|q|@>;
//! p:=q; q:=r;
//! until p=cur_spec;
//!
//! @ The |new_boundary| subroutine comes in handy at this point. It inserts
//! a new boundary node just after a given node |p|, using a given octant code
//! to transform the new node's coordinates. The ``transition'' fields are
//! not computed here.
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! procedure new_boundary(@!p:pointer;@!octant:small_number);
//! var @!q,@!r:pointer; {for list manipulation}
//! begin q:=link(p); {we assume that |right_type(q)<>endpoint|}
//! r:=get_node(knot_node_size); link(r):=q; link(p):=r;
//! left_type(r):=left_type(q); {but possibly |left_type(q)=endpoint|}
//! left_x(r):=left_x(q); left_y(r):=left_y(q);
//! right_type(r):=endpoint; left_type(q):=endpoint;
//! right_octant(r):=octant; left_octant(q):=right_type(q);
//! unskew(x_coord(q),y_coord(q),right_type(q));
//! skew(cur_x,cur_y,octant); x_coord(r):=cur_x; y_coord(r):=cur_y;
//! end;
//!
//! @ The case |q=r| occurs if and only if |p=q=r=cur_spec|, when we want to turn
//! $360^\circ$ in eight steps and then remove a solitary dead cubic.
//! The program below happens to work in that case, but the reader isn't
//! expected to understand why.
//!
//! @<Insert one or more octant boundary nodes just before~|q|@>=
//! begin new_boundary(p,right_type(p)); s:=link(p);
//! o1:=octant_number[right_type(p)]; o2:=octant_number[right_type(q)];
//! case o2-o1 of
//! 1,-7,7,-1: goto done;
//! 2,-6: clockwise:=false;
//! 3,-5,4,-4,5,-3: @<Decide whether or not to go clockwise@>;
//! 6,-2: clockwise:=true;
//! 0:clockwise:=rev_turns;
//! end; {there are no other cases}
//! @<Insert additional boundary nodes, then |goto done|@>;
//! done: if q=r then
//!   begin q:=link(q); r:=q; p:=s; link(s):=q; left_octant(q):=right_octant(q);
//!   left_type(q):=endpoint; free_node(cur_spec,knot_node_size); cur_spec:=q;
//!   end;
//! @<Fix up the transition fields and adjust the turning number@>;
//! end
//!
//! @ @<Other local variables for |make_spec|@>=
//! @!o1,@!o2:small_number; {octant numbers}
//! @!clockwise:boolean; {should we turn clockwise?}
//! @!dx1,@!dy1,@!dx2,@!dy2:integer; {directions of travel at a cusp}
//! @!dmax,@!del:integer; {temporary registers}
//!
//! @ A tricky question arises when a path jumps four octants. We want the
//! direction of turning to be counterclockwise if the curve has changed
//! direction by $180^\circ$, or by something so close to $180^\circ$ that
//! the difference is probably due to rounding errors; otherwise we want to
//! turn through an angle of less than $180^\circ$. This decision needs to
//! be made even when a curve seems to have jumped only three octants, since
//! a curve may approach direction $(-1,0)$ from the fourth octant, then
//! it might leave from direction $(+1,0)$ into the first.
//!
//! The following code solves the problem by analyzing the incoming
//! direction |(dx1,dy1)| and the outgoing direction |(dx2,dy2)|.
//!
//! @<Decide whether or not to go clockwise@>=
//! begin @<Compute the incoming and outgoing directions@>;
//! unskew(dx1,dy1,right_type(p)); del:=pyth_add(cur_x,cur_y);@/
//! dx1:=make_fraction(cur_x,del); dy1:=make_fraction(cur_y,del);
//!   {$\cos\theta_1$ and $\sin\theta_1$}
//! unskew(dx2,dy2,right_type(q)); del:=pyth_add(cur_x,cur_y);@/
//! dx2:=make_fraction(cur_x,del); dy2:=make_fraction(cur_y,del);
//!   {$\cos\theta_2$ and $\sin\theta_2$}
//! del:=take_fraction(dx1,dy2)-take_fraction(dx2,dy1); {$\sin(\theta_2-\theta_1)$}
//! if del>4684844 then clockwise:=false
//! else if del<-4684844 then clockwise:=true
//!   {$2^{28}\cdot\sin 1^\circ\approx4684844.68$}
//! else clockwise:=rev_turns;
//! end
//!
//! @ Actually the turnarounds just computed will be clockwise,
//! not counterclockwise, if
//! the global variable |rev_turns| is |true|; it is usually |false|.
//!
//! @<Glob...@>=
//! @!rev_turns:boolean; {should we make U-turns in the English manner?}
//!
//! @ @<Set init...@>=
//! rev_turns:=false;
//!
//! @ @<Compute the incoming and outgoing directions@>=
//! dx1:=x_coord(s)-left_x(s); dy1:=y_coord(s)-left_y(s);
//! if dx1=0 then if dy1=0 then
//!   begin dx1:=x_coord(s)-right_x(p); dy1:=y_coord(s)-right_y(p);
//!   if dx1=0 then if dy1=0 then
//!     begin dx1:=x_coord(s)-x_coord(p); dy1:=y_coord(s)-y_coord(p);
//!     end;  {and they {\sl can't} both be zero}
//!   end;
//! dmax:=abs(dx1);@+if abs(dy1)>dmax then dmax:=abs(dy1);
//! while dmax<fraction_one do
//!   begin double(dmax); double(dx1); double(dy1);
//!   end;
//! dx2:=right_x(q)-x_coord(q); dy2:=right_y(q)-y_coord(q);
//! if dx2=0 then if dy2=0 then
//!   begin dx2:=left_x(r)-x_coord(q); dy2:=left_y(r)-y_coord(q);
//!   if dx2=0 then if dy2=0 then
//!     begin if right_type(r)=endpoint then
//!       begin cur_x:=x_coord(r); cur_y:=y_coord(r);
//!       end
//!     else  begin unskew(x_coord(r),y_coord(r),right_type(r));
//!       skew(cur_x,cur_y,right_type(q));
//!       end;
//!     dx2:=cur_x-x_coord(q); dy2:=cur_y-y_coord(q);
//!     end;  {and they {\sl can't} both be zero}
//!   end;
//! dmax:=abs(dx2);@+if abs(dy2)>dmax then dmax:=abs(dy2);
//! while dmax<fraction_one do
//!   begin double(dmax); double(dx2); double(dy2);
//!   end
//!
//! @ @<Insert additional boundary nodes...@>=
//! loop@+  begin if clockwise then
//!     if o1=1 then o1:=8@+else decr(o1)
//!   else if o1=8 then o1:=1@+else incr(o1);
//!   if o1=o2 then goto done;
//!   new_boundary(s,octant_code[o1]);
//!   s:=link(s); left_octant(s):=right_octant(s);
//!   end
//!
//! @ Now it remains to insert the redundant
//! transition information into the |left_transition|
//! and |right_transition| fields between adjacent octants, in the octant
//! boundary nodes that have just been inserted between |link(p)| and~|q|.
//! The turning number is easily computed from these transitions.
//!
//! @<Fix up the transition fields and adjust the turning number@>=
//! p:=link(p);
//! repeat s:=link(p);
//! o1:=octant_number[right_octant(p)]; o2:=octant_number[left_octant(s)];
//! if abs(o1-o2)=1 then
//!   begin if o2<o1 then o2:=o1;
//!   if odd(o2) then right_transition(p):=axis
//!   else right_transition(p):=diagonal;
//!   end
//! else  begin if o1=8 then incr(turning_number)@+else decr(turning_number);
//!   right_transition(p):=axis;
//!   end;
//! left_transition(s):=right_transition(p);
//! p:=s;
//! until p=q
//!
