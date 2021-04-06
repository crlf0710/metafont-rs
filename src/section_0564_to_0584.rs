//! @* \[27] Online graphic output.
//! \MF\ displays images on the user's screen by means of a few primitive
//! operations that are defined below. These operations have deliberately been
//! kept simple so that they can be implemented without great difficulty on a
//! wide variety of machines. Since \PASCAL\ has no traditional standards for
//! graphic output, some system-dependent code needs to be written in order to
//! support this aspect of \MF; but the necessary routines are usually quite
//! easy to write.
//! @^system dependencies@>
//!
//! In fact, there are exactly four such routines:
//!
//! \yskip\hang
//! |init_screen| does whatever initialization is necessary to
//! support the other operations; it is a boolean function that returns
//! |false| if graphic output cannot be supported (e.g., if the other three
//! routines have not been written, or if the user doesn't have the
//! right kind of terminal).
//!
//! \yskip\hang
//! |blank_rectangle| updates a buffer area in memory so that
//! all pixels in a specified rectangle will be set to the background color.
//!
//! \yskip\hang
//! |paint_row| assigns values to specified pixels in a row of
//! the buffer just mentioned, based on ``transition'' indices explained below.
//!
//! \yskip\hang
//! |update_screen| displays the current screen buffer; the
//! effects of |blank_rectangle| and |paint_row| commands may or may not
//! become visible until the next |update_screen| operation is performed.
//! (Thus, |update_screen| is analogous to |update_terminal|.)
//!
//! \yskip\noindent
//! The \PASCAL\ code here is a minimum version of |init_screen| and
//! |update_screen|, usable on \MF\ installations that don't
//! support screen output. If |init_screen| is changed to return |true|
//! instead of |false|, the other routines will simply log the fact
//! that they have been called; they won't really display anything.
//! The standard test routines for \MF\ use this log information to check
//! that \MF\ is working properly, but the |wlog| instructions should be
//! removed from production versions of \MF.
//!
//! @p function init_screen:boolean;
//! begin init_screen:=false;
//! end;
//! @#
//! procedure update_screen; {will be called only if |init_screen| returns |true|}
//! begin @!init wlog_ln('Calling UPDATESCREEN');@+tini {for testing only}
//! end;
//!
//! @ The user's screen is assumed to be a rectangular area, |screen_width|
//! pixels wide and |screen_depth| pixels deep. The pixel in the upper left
//! corner is said to be in column~0 of row~0; the pixel in the lower right
//! corner is said to be in column |screen_width-1| of row |screen_depth-1|.
//! Notice that row numbers increase from top to bottom, contrary to \MF's
//! other coordinates.
//!
//! Each pixel is assumed to have two states, referred to in this documentation
//! as |black| and |white|. The background color is called |white| and the
//! other color is called |black|; but any two distinct pixel values
//! can actually be used. For example, the author developed \MF\ on a
//! system for which |white| was black and |black| was bright green.
//!
//! @d white=0 {background pixels}
//! @d black=1 {visible pixels}
//!
//! @<Types...@>=
//! @!screen_row=0..screen_depth; {a row number on the screen}
//! @!screen_col=0..screen_width; {a column number on the screen}
//! @!trans_spec=array[screen_col] of screen_col; {a transition spec, see below}
//! @!pixel_color=white..black; {specifies one of the two pixel values}
//!
//! @ We'll illustrate the |blank_rectangle| and |paint_row| operations by
//! pretending to declare a screen buffer called |screen_pixel|. This code
//! is actually commented out, but it does specify the intended effects.
//!
//! @<Glob...@>=
//! @{@+@!screen_pixel:array[screen_row,screen_col] of pixel_color@t; @>@}
//!
//! @ The |blank_rectangle| routine simply whitens all pixels that lie in
//! columns |left_col| through |right_col-1|, inclusive, of rows
//! |top_row| through |bot_row-1|, inclusive, given four parameters that satisfy
//! the relations
//! $$\hbox{|0<=left_col<=right_col<=screen_width|,\quad
//!   |0<=top_row<=bot_row<=screen_depth|.}$$
//! If |left_col=right_col| or |top_row=bot_row|, nothing happens.
//!
//! The commented-out code in the following procedure is for illustrative
//! purposes only.
//! @^system dependencies@>
//!
//! @p procedure blank_rectangle(@!left_col,@!right_col:screen_col;
//!   @!top_row,@!bot_row:screen_row);
//! var @!r:screen_row;
//! @!c:screen_col;
//! begin @{@+for r:=top_row to bot_row-1 do
//!   for c:=left_col to right_col-1 do
//!     screen_pixel[r,c]:=white;@+@}@/
//! @!init wlog_cr; {this will be done only after |init_screen=true|}
//! wlog_ln('Calling BLANKRECTANGLE(',left_col:1,',',
//!   right_col:1,',',top_row:1,',',bot_row:1,')');@+tini
//! end;
//!
//! @ The real work of screen display is done by |paint_row|. But it's not
//! hard work, because the operation affects only
//! one of the screen rows, and it affects only a contiguous set of columns
//! in that row. There are four parameters: |r|~(the row),
//! |b|~(the initial color),
//! |a|~(the array of transition specifications),
//! and |n|~(the number of transitions). The elements of~|a| will satisfy
//! $$0\L a[0]<a[1]<\cdots<a[n]\L |screen_width|;$$
//! the value of |r| will satisfy |0<=r<screen_depth|; and |n| will be positive.
//!
//! The general idea is to paint blocks of pixels in alternate colors;
//! the precise details are best conveyed by means of a \PASCAL\
//! program (see the commented-out code below).
//! @^system dependencies@>
//!
//! @p procedure paint_row(@!r:screen_row;@!b:pixel_color;var @!a:trans_spec;
//!   @!n:screen_col);
//! var @!k:screen_col; {an index into |a|}
//! @!c:screen_col; {an index into |screen_pixel|}
//! begin @{@+k:=0; c:=a[0];
//! repeat incr(k);
//!   repeat screen_pixel[r,c]:=b; incr(c);
//!   until c=a[k];
//!   b:=black-b; {$|black|\swap|white|$}
//!   until k=n;@+@}@/
//! @!init wlog('Calling PAINTROW(',r:1,',',b:1,';');
//!   {this is done only after |init_screen=true|}
//! for k:=0 to n do
//!   begin wlog(a[k]:1); if k<>n then wlog(',');
//!   end;
//! wlog_ln(')');@+tini
//! end;
//!
//! @ The remainder of \MF's screen routines are system-independent calls
//! on the four primitives just defined.
//!
//! First we have a global boolean variable that tells if |init_screen|
//! has been called, and another one that tells if |init_screen| has
//! given a |true| response.
//!
//! @<Glob...@>=
//! @!screen_started:boolean; {have the screen primitives been initialized?}
//! @!screen_OK:boolean; {is it legitimate to call |blank_rectangle|,
//!   |paint_row|, and |update_screen|?}
//!
//! @ @d start_screen==begin if not screen_started then
//!     begin screen_OK:=init_screen; screen_started:=true;
//!     end;
//!   end
//!
//! @<Set init...@>=
//! screen_started:=false; screen_OK:=false;
//!
//! @ \MF\ provides the user with 16 ``window'' areas on the screen, in each
//! of which it is possible to produce independent displays.
//!
//! It should be noted that \MF's windows aren't really independent
//! ``clickable'' entities in the sense of multi-window graphic workstations;
//! \MF\ simply maps them into subsets of a single screen image that is
//! controlled by |init_screen|, |blank_rectangle|, |paint_row|, and
//! |update_screen| as described above. Implementations of \MF\ on a
//! multi-window workstation probably therefore make use of only two
//! windows in the other sense: one for the terminal output and another
//! for the screen with \MF's 16 areas. Henceforth we shall
//! use the term window only in \MF's sense.
//!
//! @<Types...@>=
//! @!window_number=0..15;
//!
//! @ A user doesn't have to use any of the 16 windows. But when a window is
//! ``opened,'' it is allocated to a specific rectangular portion of the screen
//! and to a specific rectangle with respect to \MF's coordinates. The relevant
//! data is stored in global arrays |window_open|, |left_col|, |right_col|,
//! |top_row|, |bot_row|, |m_window|, and |n_window|.
//!
//! The |window_open| array is boolean, and its significance is obvious. The
//! |left_col|, \dots, |bot_row| arrays contain screen coordinates that
//! can be used to blank the entire window with |blank_rectangle|. And the
//! other two arrays just mentioned handle the conversion between
//! actual coordinates and screen coordinates: \MF's pixel in column~$m$
//! of row~$n$ will appear in screen column |m_window+m| and in screen row
//! |n_window-n|, provided that these lie inside the boundaries of the window.
//!
//! Another array |window_time| holds the number of times this window has
//! been updated.
//!
//! @<Glob...@>=
//! @!window_open:array[window_number] of boolean;
//!   {has this window been opened?}
//! @!left_col:array[window_number] of screen_col;
//!   {leftmost column position on screen}
//! @!right_col:array[window_number] of screen_col;
//!   {rightmost column position, plus~1}
//! @!top_row:array[window_number] of screen_row;
//!   {topmost row position on screen}
//! @!bot_row:array[window_number] of screen_row;
//!   {bottommost row position, plus~1}
//! @!m_window:array[window_number] of integer;
//!   {offset between user and screen columns}
//! @!n_window:array[window_number] of integer;
//!   {offset between user and screen rows}
//! @!window_time:array[window_number] of integer;
//!   {it has been updated this often}
//!
//! @ @<Set init...@>=
//! for k:=0 to 15 do
//!   begin window_open[k]:=false; window_time[k]:=0;
//!   end;
//!
//! @ Opening a window isn't like opening a file, because you can open it
//! as often as you like, and you never have to close it again. The idea is
//! simply to define special points on the current screen display.
//!
//! Overlapping window specifications may cause complex effects that can
//! be understood only by scrutinizing \MF's display algorithms; thus it
//! has been left undefined in the \MF\ user manual, although the behavior
//! @:METAFONTbook}{\sl The {\logos METAFONT\/}book@>
//! is in fact predictable.
//!
//! Here is a subroutine that implements the command `\&{openwindow}~|k|
//! \&{from}~$(\\{r0},\\{c0})$ \&{to}~$(\\{r1},\\{c1})$ \&{at}~$(x,y)$'.
//!
//! @p procedure open_a_window(@!k:window_number;@!r0,@!c0,@!r1,@!c1:scaled;
//!     @!x,@!y:scaled);
//! var @!m,@!n:integer; {pixel coordinates}
//! begin @<Adjust the coordinates |(r0,c0)| and |(r1,c1)| so that
//!   they lie in the proper range@>;
//! window_open[k]:=true; incr(window_time[k]);@/
//! left_col[k]:=c0; right_col[k]:=c1; top_row[k]:=r0; bot_row[k]:=r1;@/
//! @<Compute the offsets between screen coordinates and actual coordinates@>;
//! start_screen;
//! if screen_OK then
//!   begin blank_rectangle(c0,c1,r0,r1); update_screen;
//!   end;
//! end;
//!
//! @ A window whose coordinates don't fit the existing screen size will be
//! truncated until they do.
//!
//! @<Adjust the coordinates |(r0,c0)| and |(r1,c1)|...@>=
//! if r0<0 then r0:=0@+else r0:=round_unscaled(r0);
//! r1:=round_unscaled(r1);
//! if r1>screen_depth then r1:=screen_depth;
//! if r1<r0 then
//!   if r0>screen_depth then r0:=r1@+else r1:=r0;
//! if c0<0 then c0:=0@+else c0:=round_unscaled(c0);
//! c1:=round_unscaled(c1);
//! if c1>screen_width then c1:=screen_width;
//! if c1<c0 then
//!   if c0>screen_width then c0:=c1@+else c1:=c0
//!
//! @ Three sets of coordinates are rampant, and they must be kept straight!
//! (i)~\MF's main coordinates refer to the edges between pixels. (ii)~\MF's
//! pixel coordinates (within edge structures) say that the pixel bounded by
//! $(m,n)$, $(m,n+1)$, $(m+1,n)$, and~$(m+1,n+1)$ is in pixel row number~$n$
//! and pixel column number~$m$. (iii)~Screen coordinates, on the other hand,
//! have rows numbered in increasing order from top to bottom, as mentioned
//! above.
//! @^coordinates, explained@>
//!
//! The program here first computes integers $m$ and $n$ such that
//! pixel column~$m$ of pixel row~$n$ will be at the upper left corner
//! of the window. Hence pixel column |m-c0| of pixel row |n+r0|
//! will be at the upper left corner of the screen.
//!
//! @<Compute the offsets between screen coordinates and actual coordinates@>=
//! m:=round_unscaled(x); n:=round_unscaled(y)-1;@/
//! m_window[k]:=c0-m; n_window[k]:=r0+n
//!
//! @ Now here comes \MF's most complicated operation related to window
//! display: Given the number~|k| of an open window, the pixels of positive
//! weight in |cur_edges| will be shown as |black| in the window; all other
//! pixels will be shown as |white|.
//!
//! @p procedure disp_edges(@!k:window_number);
//! label done,found;
//! var @!p,@!q:pointer; {for list manipulation}
//! @!already_there:boolean; {is a previous incarnation in the window?}
//! @!r:integer; {row number}
//! @<Other local variables for |disp_edges|@>@;
//! begin if screen_OK then
//!  if left_col[k]<right_col[k] then if top_row[k]<bot_row[k] then
//!   begin already_there:=false;
//!   if last_window(cur_edges)=k then
//!    if last_window_time(cur_edges)=window_time[k] then
//!     already_there:=true;
//!   if not already_there then
//!     blank_rectangle(left_col[k],right_col[k],top_row[k],bot_row[k]);
//!   @<Initialize for the display computations@>;
//!   p:=link(cur_edges); r:=n_window[k]-(n_min(cur_edges)-zero_field);
//!   while (p<>cur_edges)and(r>=top_row[k]) do
//!     begin if r<bot_row[k] then
//!       @<Display the pixels of edge row |p| in screen row |r|@>;
//!     p:=link(p); decr(r);
//!     end;
//!   update_screen;
//!   incr(window_time[k]);
//!   last_window(cur_edges):=k; last_window_time(cur_edges):=window_time[k];
//!   end;
//! end;
//!
//! @ Since it takes some work to display a row, we try to avoid recomputation
//! whenever we can.
//!
//! @<Display the pixels of edge row |p| in screen row |r|@>=
//! begin if unsorted(p)>void then sort_edges(p)
//! else if unsorted(p)=void then if already_there then goto done;
//! unsorted(p):=void; {this time we'll paint, but maybe not next time}
//! @<Set up the parameters needed for |paint_row|;
//!   but |goto done| if no painting is needed after all@>;
//! paint_row(r,b,row_transition,n);
//! done: end
//!
//! @ The transition-specification parameter to |paint_row| is always the same
//! array.
//!
//! @<Glob...@>=
//! @!row_transition:trans_spec; {an array of |black|/|white| transitions}
//!
//! @ The job remaining is to go through the list |sorted(p)|, unpacking the
//! |info| fields into |m| and weight, then making |black| the pixels whose
//! accumulated weight~|w| is positive.
//!
//! @<Other local variables for |disp_edges|@>=
//! @!n:screen_col; {the highest active index in |row_transition|}
//! @!w,@!ww:integer; {old and new accumulated weights}
//! @!b:pixel_color; {status of first pixel in the row transitions}
//! @!m,@!mm:integer; {old and new screen column positions}
//! @!d:integer; {edge-and-weight without |min_halfword| compensation}
//! @!m_adjustment:integer; {conversion between edge and screen coordinates}
//! @!right_edge:integer; {largest edge-and-weight that could affect the window}
//! @!min_col:screen_col; {the smallest screen column number in the window}
//!
//! @ Some precomputed constants make the display calculations faster.
//!
//! @<Initialize for the display computations@>=
//! m_adjustment:=m_window[k]-m_offset(cur_edges);@/
//! right_edge:=8*(right_col[k]-m_adjustment);@/
//! min_col:=left_col[k]
//!
//! @ @<Set up the parameters needed for |paint_row|...@>=
//! n:=0; ww:=0; m:=-1; w:=0;
//! q:=sorted(p); row_transition[0]:=min_col;
//! loop@+  begin if q=sentinel then d:=right_edge
//!   else d:=ho(info(q));
//!   mm:=(d div 8)+m_adjustment;
//!   if mm<>m then
//!     begin @<Record a possible transition in column |m|@>;
//!     m:=mm; w:=ww;
//!     end;
//!   if d>=right_edge then goto found;
//!   ww:=ww+(d mod 8)-zero_w;
//!   q:=link(q);
//!   end;
//! found:@<Wind up the |paint_row| parameter calculation by inserting the
//!   final transition; |goto done| if no painting is needed@>;
//!
//! @ Now |m| is a screen column |<right_col[k]|.
//!
//! @<Record a possible transition in column |m|@>=
//! if w<=0 then
//!   begin if ww>0 then if m>min_col then
//!     begin if n=0 then
//!       if already_there then
//!         begin b:=white; incr(n);
//!         end
//!       else b:=black
//!     else incr(n);
//!     row_transition[n]:=m;
//!     end;
//!   end
//! else if ww<=0 then if m>min_col then
//!   begin if n=0 then b:=black;
//!   incr(n); row_transition[n]:=m;
//!   end
//!
//! @ If the entire row is |white| in the window area, we can omit painting it
//! when |already_there| is false, since it has already been blanked out in
//! that case.
//!
//! When the following code is invoked, |row_transition[n]| will be
//! strictly less than |right_col[k]|.
//!
//! @<Wind up the |paint_row|...@>=
//! if already_there or(ww>0) then
//!   begin if n=0 then
//!     if ww>0 then b:=black
//!     else b:=white;
//!   incr(n); row_transition[n]:=right_col[k];
//!   end
//! else if n=0 then goto done
//!
