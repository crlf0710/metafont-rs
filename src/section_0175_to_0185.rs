//! @* \[11] Memory layout.
//! Some areas of |mem| are dedicated to fixed usage, since static allocation is
//! more efficient than dynamic allocation when we can get away with it. For
//! example, locations |mem_min| to |mem_min+2| are always used to store the
//! specification for null pen coordinates that are `$(0,0)$'. The
//! following macro definitions accomplish the static allocation by giving
//! symbolic names to the fixed positions. Static variable-size nodes appear
//! in locations |mem_min| through |lo_mem_stat_max|, and static single-word nodes
//! appear in locations |hi_mem_stat_min| through |mem_top|, inclusive.
//!
//! @d null_coords==mem_min {specification for pen offsets of $(0,0)$}
//! @d null_pen==null_coords+3 {we will define |coord_node_size=3|}
//! @d dep_head==null_pen+10 {and |pen_node_size=10|}
//! @d zero_val==dep_head+2 {two words for a permanently zero value}
//! @d temp_val==zero_val+2 {two words for a temporary value node}
//! @d end_attr==temp_val {we use |end_attr+2| only}
//! @d inf_val==end_attr+2 {and |inf_val+1| only}
//! @d bad_vardef==inf_val+2 {two words for \&{vardef} error recovery}
//! @d lo_mem_stat_max==bad_vardef+1  {largest statically
//!   allocated word in the variable-size |mem|}
//! @#
//! @d sentinel==mem_top {end of sorted lists}
//! @d temp_head==mem_top-1 {head of a temporary list of some kind}
//! @d hold_head==mem_top-2 {head of a temporary list of another kind}
//! @d hi_mem_stat_min==mem_top-2 {smallest statically allocated word in
//!   the one-word |mem|}
//!
//! @ The following code gets the dynamic part of |mem| off to a good start,
//! when \MF\ is initializing itself the slow way.
//!
//! @<Initialize table entries (done by \.{INIMF} only)@>=
//! rover:=lo_mem_stat_max+1; {initialize the dynamic memory}
//! link(rover):=empty_flag;
//! node_size(rover):=1000; {which is a 1000-word available node}
//! llink(rover):=rover; rlink(rover):=rover;@/
//! lo_mem_max:=rover+1000; link(lo_mem_max):=null; info(lo_mem_max):=null;@/
//! for k:=hi_mem_stat_min to mem_top do
//!   mem[k]:=mem[lo_mem_max]; {clear list heads}
//! avail:=null; mem_end:=mem_top;
//! hi_mem_min:=hi_mem_stat_min; {initialize the one-word memory}
//! var_used:=lo_mem_stat_max+1-mem_min; dyn_used:=mem_top+1-hi_mem_min;
//!   {initialize statistics}
//!
//! @ The procedure |flush_list(p)| frees an entire linked list of one-word
//! nodes that starts at a given position, until coming to |sentinel| or a
//! pointer that is not in the one-word region. Another procedure,
//! |flush_node_list|, frees an entire linked list of one-word and two-word
//! nodes, until coming to a |null| pointer.
//! @^inner loop@>
//!
//! @p procedure flush_list(@!p:pointer); {makes list of single-word nodes
//!   available}
//! label done;
//! var @!q,@!r:pointer; {list traversers}
//! begin if p>=hi_mem_min then if p<>sentinel then
//!   begin r:=p;
//!   repeat q:=r; r:=link(r); @!stat decr(dyn_used);@+tats@/
//!   if r<hi_mem_min then goto done;
//!   until r=sentinel;
//!   done: {now |q| is the last node on the list}
//!   link(q):=avail; avail:=p;
//!   end;
//! end;
//! @#
//! procedure flush_node_list(@!p:pointer);
//! var @!q:pointer; {the node being recycled}
//! begin while p<>null do
//!   begin q:=p; p:=link(p);
//!   if q<hi_mem_min then free_node(q,2)@+else free_avail(q);
//!   end;
//! end;
//!
//! @ If \MF\ is extended improperly, the |mem| array might get screwed up.
//! For example, some pointers might be wrong, or some ``dead'' nodes might not
//! have been freed when the last reference to them disappeared. Procedures
//! |check_mem| and |search_mem| are available to help diagnose such
//! problems. These procedures make use of two arrays called |free| and
//! |was_free| that are present only if \MF's debugging routines have
//! been included. (You may want to decrease the size of |mem| while you
//! @^debugging@>
//! are debugging.)
//!
//! @<Glob...@>=
//! @!debug @!free: packed array [mem_min..mem_max] of boolean; {free cells}
//! @t\hskip1em@>@!was_free: packed array [mem_min..mem_max] of boolean;
//!   {previously free cells}
//! @t\hskip1em@>@!was_mem_end,@!was_lo_max,@!was_hi_min: pointer;
//!   {previous |mem_end|, |lo_mem_max|, and |hi_mem_min|}
//! @t\hskip1em@>@!panicking:boolean; {do we want to check memory constantly?}
//! gubed
//!
//! @ @<Set initial...@>=
//! @!debug was_mem_end:=mem_min; {indicate that everything was previously free}
//! was_lo_max:=mem_min; was_hi_min:=mem_max;
//! panicking:=false;
//! gubed
//!
//! @ Procedure |check_mem| makes sure that the available space lists of
//! |mem| are well formed, and it optionally prints out all locations
//! that are reserved now but were free the last time this procedure was called.
//!
//! @p @!debug procedure check_mem(@!print_locs : boolean);
//! label done1,done2; {loop exits}
//! var @!p,@!q,@!r:pointer; {current locations of interest in |mem|}
//! @!clobbered:boolean; {is something amiss?}
//! begin for p:=mem_min to lo_mem_max do free[p]:=false; {you can probably
//!   do this faster}
//! for p:=hi_mem_min to mem_end do free[p]:=false; {ditto}
//! @<Check single-word |avail| list@>;
//! @<Check variable-size |avail| list@>;
//! @<Check flags of unavailable nodes@>;
//! @<Check the list of linear dependencies@>;
//! if print_locs then @<Print newly busy locations@>;
//! for p:=mem_min to lo_mem_max do was_free[p]:=free[p];
//! for p:=hi_mem_min to mem_end do was_free[p]:=free[p];
//!   {|was_free:=free| might be faster}
//! was_mem_end:=mem_end; was_lo_max:=lo_mem_max; was_hi_min:=hi_mem_min;
//! end;
//! gubed
//!
//! @ @<Check single-word...@>=
//! p:=avail; q:=null; clobbered:=false;
//! while p<>null do
//!   begin if (p>mem_end)or(p<hi_mem_min) then clobbered:=true
//!   else if free[p] then clobbered:=true;
//!   if clobbered then
//!     begin print_nl("AVAIL list clobbered at ");
//! @.AVAIL list clobbered...@>
//!     print_int(q); goto done1;
//!     end;
//!   free[p]:=true; q:=p; p:=link(q);
//!   end;
//! done1:
//!
//! @ @<Check variable-size...@>=
//! p:=rover; q:=null; clobbered:=false;
//! repeat if (p>=lo_mem_max)or(p<mem_min) then clobbered:=true
//!   else if (rlink(p)>=lo_mem_max)or(rlink(p)<mem_min) then clobbered:=true
//!   else if  not(is_empty(p))or(node_size(p)<2)or@|
//!    (p+node_size(p)>lo_mem_max)or@| (llink(rlink(p))<>p) then clobbered:=true;
//!   if clobbered then
//!   begin print_nl("Double-AVAIL list clobbered at ");
//! @.Double-AVAIL list clobbered...@>
//!   print_int(q); goto done2;
//!   end;
//! for q:=p to p+node_size(p)-1 do {mark all locations free}
//!   begin if free[q] then
//!     begin print_nl("Doubly free location at ");
//! @.Doubly free location...@>
//!     print_int(q); goto done2;
//!     end;
//!   free[q]:=true;
//!   end;
//! q:=p; p:=rlink(p);
//! until p=rover;
//! done2:
//!
//! @ @<Check flags...@>=
//! p:=mem_min;
//! while p<=lo_mem_max do {node |p| should not be empty}
//!   begin if is_empty(p) then
//!     begin print_nl("Bad flag at "); print_int(p);
//! @.Bad flag...@>
//!     end;
//!   while (p<=lo_mem_max) and not free[p] do incr(p);
//!   while (p<=lo_mem_max) and free[p] do incr(p);
//!   end
//!
//! @ @<Print newly busy...@>=
//! begin print_nl("New busy locs:");
//! @.New busy locs@>
//! for p:=mem_min to lo_mem_max do
//!   if not free[p] and ((p>was_lo_max) or was_free[p]) then
//!     begin print_char(" "); print_int(p);
//!     end;
//! for p:=hi_mem_min to mem_end do
//!   if not free[p] and
//!    ((p<was_hi_min) or (p>was_mem_end) or was_free[p]) then
//!     begin print_char(" "); print_int(p);
//!     end;
//! end
//!
//! @ The |search_mem| procedure attempts to answer the question ``Who points
//! to node~|p|?'' In doing so, it fetches |link| and |info| fields of |mem|
//! that might not be of type |two_halves|. Strictly speaking, this is
//! @^dirty \PASCAL@>
//! undefined in \PASCAL, and it can lead to ``false drops'' (words that seem to
//! point to |p| purely by coincidence). But for debugging purposes, we want
//! to rule out the places that do {\sl not\/} point to |p|, so a few false
//! drops are tolerable.
//!
//! @p @!debug procedure search_mem(@!p:pointer); {look for pointers to |p|}
//! var @!q:integer; {current position being searched}
//! begin for q:=mem_min to lo_mem_max do
//!   begin if link(q)=p then
//!     begin print_nl("LINK("); print_int(q); print_char(")");
//!     end;
//!   if info(q)=p then
//!     begin print_nl("INFO("); print_int(q); print_char(")");
//!     end;
//!   end;
//! for q:=hi_mem_min to mem_end do
//!   begin if link(q)=p then
//!     begin print_nl("LINK("); print_int(q); print_char(")");
//!     end;
//!   if info(q)=p then
//!     begin print_nl("INFO("); print_int(q); print_char(")");
//!     end;
//!   end;
//! @<Search |eqtb| for equivalents equal to |p|@>;
//! end;
//! gubed
//!
