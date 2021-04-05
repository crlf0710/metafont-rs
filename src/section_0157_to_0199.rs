//! @ When debugging, we may want to print a |memory_word| without knowing
//! what type it is; so we print it in all modes.
//! @^dirty \PASCAL@>@^debugging@>
//!
//! @p @!debug procedure print_word(@!w:memory_word);
//!   {prints |w| in all ways}
//! begin print_int(w.int); print_char(" ");@/
//! print_scaled(w.sc); print_char(" "); print_scaled(w.sc div @'10000); print_ln;@/
//! print_int(w.hh.lh); print_char("="); print_int(w.hh.b0); print_char(":");
//! print_int(w.hh.b1); print_char(";"); print_int(w.hh.rh); print_char(" ");@/
//! print_int(w.qqqq.b0); print_char(":"); print_int(w.qqqq.b1); print_char(":");
//! print_int(w.qqqq.b2); print_char(":"); print_int(w.qqqq.b3);
//! end;
//! gubed
//!
//! @* \[10] Dynamic memory allocation.
//! The \MF\ system does nearly all of its own memory allocation, so that it
//! can readily be transported into environments that do not have automatic
//! facilities for strings, garbage collection, etc., and so that it can be in
//! control of what error messages the user receives. The dynamic storage
//! requirements of \MF\ are handled by providing a large array |mem| in
//! which consecutive blocks of words are used as nodes by the \MF\ routines.
//!
//! Pointer variables are indices into this array, or into another array
//! called |eqtb| that will be explained later. A pointer variable might
//! also be a special flag that lies outside the bounds of |mem|, so we
//! allow pointers to assume any |halfword| value. The minimum memory
//! index represents a null pointer.
//!
//! @d pointer==halfword {a flag or a location in |mem| or |eqtb|}
//! @d null==mem_min {the null pointer}
//!
//! @ The |mem| array is divided into two regions that are allocated separately,
//! but the dividing line between these two regions is not fixed; they grow
//! together until finding their ``natural'' size in a particular job.
//! Locations less than or equal to |lo_mem_max| are used for storing
//! variable-length records consisting of two or more words each. This region
//! is maintained using an algorithm similar to the one described in exercise
//! 2.5--19 of {\sl The Art of Computer Programming}. However, no size field
//! appears in the allocated nodes; the program is responsible for knowing the
//! relevant size when a node is freed. Locations greater than or equal to
//! |hi_mem_min| are used for storing one-word records; a conventional
//! \.{AVAIL} stack is used for allocation in this region.
//!
//! Locations of |mem| between |mem_min| and |mem_top| may be dumped as part
//! of preloaded base files, by the \.{INIMF} preprocessor.
//! @.INIMF@>
//! Production versions of \MF\ may extend the memory at the top end in order to
//! provide more space; these locations, between |mem_top| and |mem_max|,
//! are always used for single-word nodes.
//!
//! The key pointers that govern |mem| allocation have a prescribed order:
//! $$\hbox{|null=mem_min<lo_mem_max<hi_mem_min<mem_top<=mem_end<=mem_max|.}$$
//!
//! @<Glob...@>=
//! @!mem : array[mem_min..mem_max] of memory_word; {the big dynamic storage area}
//! @!lo_mem_max : pointer; {the largest location of variable-size memory in use}
//! @!hi_mem_min : pointer; {the smallest location of one-word memory in use}
//!
//! @ Users who wish to study the memory requirements of specific applications can
//! use optional special features that keep track of current and
//! maximum memory usage. When code between the delimiters |@!stat| $\ldots$
//! |tats| is not ``commented out,'' \MF\ will run a bit slower but it will
//! report these statistics when |tracing_stats| is positive.
//!
//! @<Glob...@>=
//! @!var_used, @!dyn_used : integer; {how much memory is in use}
//!
//! @ Let's consider the one-word memory region first, since it's the
//! simplest. The pointer variable |mem_end| holds the highest-numbered location
//! of |mem| that has ever been used. The free locations of |mem| that
//! occur between |hi_mem_min| and |mem_end|, inclusive, are of type
//! |two_halves|, and we write |info(p)| and |link(p)| for the |lh|
//! and |rh| fields of |mem[p]| when it is of this type. The single-word
//! free locations form a linked list
//! $$|avail|,\;\hbox{|link(avail)|},\;\hbox{|link(link(avail))|},\;\ldots$$
//! terminated by |null|.
//!
//! @d link(#) == mem[#].hh.rh {the |link| field of a memory word}
//! @d info(#) == mem[#].hh.lh {the |info| field of a memory word}
//!
//! @<Glob...@>=
//! @!avail : pointer; {head of the list of available one-word nodes}
//! @!mem_end : pointer; {the last one-word node used in |mem|}
//!
//! @ If one-word memory is exhausted, it might mean that the user has forgotten
//! a token like `\&{enddef}' or `\&{endfor}'. We will define some procedures
//! later that try to help pinpoint the trouble.
//!
//! @p @t\4@>@<Declare the procedure called |show_token_list|@>@;
//! @t\4@>@<Declare the procedure called |runaway|@>
//!
//! @ The function |get_avail| returns a pointer to a new one-word node whose
//! |link| field is null. However, \MF\ will halt if there is no more room left.
//! @^inner loop@>
//!
//! @p function get_avail : pointer; {single-word node allocation}
//! var @!p:pointer; {the new node being got}
//! begin p:=avail; {get top location in the |avail| stack}
//! if p<>null then avail:=link(avail) {and pop it off}
//! else if mem_end<mem_max then {or go into virgin territory}
//!   begin incr(mem_end); p:=mem_end;
//!   end
//! else   begin decr(hi_mem_min); p:=hi_mem_min;
//!   if hi_mem_min<=lo_mem_max then
//!     begin runaway; {if memory is exhausted, display possible runaway text}
//!     overflow("main memory size",mem_max+1-mem_min);
//!       {quit; all one-word nodes are busy}
//! @:METAFONT capacity exceeded main memory size}{\quad main memory size@>
//!     end;
//!   end;
//! link(p):=null; {provide an oft-desired initialization of the new node}
//! @!stat incr(dyn_used);@+tats@;{maintain statistics}
//! get_avail:=p;
//! end;
//!
//! @ Conversely, a one-word node is recycled by calling |free_avail|.
//!
//! @d free_avail(#)== {single-word node liberation}
//!   begin link(#):=avail; avail:=#;
//!   @!stat decr(dyn_used);@+tats@/
//!   end
//!
//! @ There's also a |fast_get_avail| routine, which saves the procedure-call
//! overhead at the expense of extra programming. This macro is used in
//! the places that would otherwise account for the most calls of |get_avail|.
//! @^inner loop@>
//!
//! @d fast_get_avail(#)==@t@>@;@/
//!   begin #:=avail; {avoid |get_avail| if possible, to save time}
//!   if #=null then #:=get_avail
//!   else  begin avail:=link(#); link(#):=null;
//!     @!stat incr(dyn_used);@+tats@/
//!     end;
//!   end
//!
//! @ The available-space list that keeps track of the variable-size portion
//! of |mem| is a nonempty, doubly-linked circular list of empty nodes,
//! pointed to by the roving pointer |rover|.
//!
//! Each empty node has size 2 or more; the first word contains the special
//! value |max_halfword| in its |link| field and the size in its |info| field;
//! the second word contains the two pointers for double linking.
//!
//! Each nonempty node also has size 2 or more. Its first word is of type
//! |two_halves|\kern-1pt, and its |link| field is never equal to |max_halfword|.
//! Otherwise there is complete flexibility with respect to the contents
//! of its other fields and its other words.
//!
//! (We require |mem_max<max_halfword| because terrible things can happen
//! when |max_halfword| appears in the |link| field of a nonempty node.)
//!
//! @d empty_flag == max_halfword {the |link| of an empty variable-size node}
//! @d is_empty(#) == (link(#)=empty_flag) {tests for empty node}
//! @d node_size == info {the size field in empty variable-size nodes}
//! @d llink(#) == info(#+1) {left link in doubly-linked list of empty nodes}
//! @d rlink(#) == link(#+1) {right link in doubly-linked list of empty nodes}
//!
//! @<Glob...@>=
//! @!rover : pointer; {points to some node in the list of empties}
//!
//! @ A call to |get_node| with argument |s| returns a pointer to a new node
//! of size~|s|, which must be 2~or more. The |link| field of the first word
//! of this new node is set to null. An overflow stop occurs if no suitable
//! space exists.
//!
//! If |get_node| is called with $s=2^{30}$, it simply merges adjacent free
//! areas and returns the value |max_halfword|.
//!
//! @p function get_node(@!s:integer):pointer; {variable-size node allocation}
//! label found,exit,restart;
//! var @!p:pointer; {the node currently under inspection}
//! @!q:pointer; {the node physically after node |p|}
//! @!r:integer; {the newly allocated node, or a candidate for this honor}
//! @!t,@!tt:integer; {temporary registers}
//! @^inner loop@>
//! begin restart: p:=rover; {start at some free node in the ring}
//! repeat @<Try to allocate within node |p| and its physical successors,
//!   and |goto found| if allocation was possible@>;
//! p:=rlink(p); {move to the next node in the ring}
//! until p=rover; {repeat until the whole list has been traversed}
//! if s=@'10000000000 then
//!   begin get_node:=max_halfword; return;
//!   end;
//! if lo_mem_max+2<hi_mem_min then if lo_mem_max+2<=mem_min+max_halfword then
//!   @<Grow more variable-size memory and |goto restart|@>;
//! overflow("main memory size",mem_max+1-mem_min);
//!   {sorry, nothing satisfactory is left}
//! @:METAFONT capacity exceeded main memory size}{\quad main memory size@>
//! found: link(r):=null; {this node is now nonempty}
//! @!stat var_used:=var_used+s; {maintain usage statistics}
//! tats@;@/
//! get_node:=r;
//! exit:end;
//!
//! @ The lower part of |mem| grows by 1000 words at a time, unless
//! we are very close to going under. When it grows, we simply link
//! a new node into the available-space list. This method of controlled
//! growth helps to keep the |mem| usage consecutive when \MF\ is
//! implemented on ``virtual memory'' systems.
//! @^virtual memory@>
//!
//! @<Grow more variable-size memory and |goto restart|@>=
//! begin if hi_mem_min-lo_mem_max>=1998 then t:=lo_mem_max+1000
//! else t:=lo_mem_max+1+(hi_mem_min-lo_mem_max) div 2;
//!   {|lo_mem_max+2<=t<hi_mem_min|}
//! if t>mem_min+max_halfword then t:=mem_min+max_halfword;
//! p:=llink(rover); q:=lo_mem_max; rlink(p):=q; llink(rover):=q;@/
//! rlink(q):=rover; llink(q):=p; link(q):=empty_flag; node_size(q):=t-lo_mem_max;@/
//! lo_mem_max:=t; link(lo_mem_max):=null; info(lo_mem_max):=null;
//! rover:=q; goto restart;
//! end
//!
//! @ @<Try to allocate...@>=
//! q:=p+node_size(p); {find the physical successor}
//! while is_empty(q) do {merge node |p| with node |q|}
//!   begin t:=rlink(q); tt:=llink(q);
//! @^inner loop@>
//!   if q=rover then rover:=t;
//!   llink(t):=tt; rlink(tt):=t;@/
//!   q:=q+node_size(q);
//!   end;
//! r:=q-s;
//! if r>p+1 then @<Allocate from the top of node |p| and |goto found|@>;
//! if r=p then if rlink(p)<>p then
//!   @<Allocate entire node |p| and |goto found|@>;
//! node_size(p):=q-p {reset the size in case it grew}
//!
//! @ @<Allocate from the top...@>=
//! begin node_size(p):=r-p; {store the remaining size}
//! rover:=p; {start searching here next time}
//! goto found;
//! end
//!
//! @ Here we delete node |p| from the ring, and let |rover| rove around.
//!
//! @<Allocate entire...@>=
//! begin rover:=rlink(p); t:=llink(p);
//! llink(rover):=t; rlink(t):=rover;
//! goto found;
//! end
//!
//! @ Conversely, when some variable-size node |p| of size |s| is no longer needed,
//! the operation |free_node(p,s)| will make its words available, by inserting
//! |p| as a new empty node just before where |rover| now points.
//!
//! @p procedure free_node(@!p:pointer; @!s:halfword); {variable-size node
//!   liberation}
//! var @!q:pointer; {|llink(rover)|}
//! begin node_size(p):=s; link(p):=empty_flag;
//! @^inner loop@>
//! q:=llink(rover); llink(p):=q; rlink(p):=rover; {set both links}
//! llink(rover):=p; rlink(q):=p; {insert |p| into the ring}
//! @!stat var_used:=var_used-s;@+tats@;{maintain statistics}
//! end;
//!
//! @ Just before \.{INIMF} writes out the memory, it sorts the doubly linked
//! available space list. The list is probably very short at such times, so a
//! simple insertion sort is used. The smallest available location will be
//! pointed to by |rover|, the next-smallest by |rlink(rover)|, etc.
//!
//! @p @!init procedure sort_avail; {sorts the available variable-size nodes
//!   by location}
//! var @!p,@!q,@!r: pointer; {indices into |mem|}
//! @!old_rover:pointer; {initial |rover| setting}
//! begin p:=get_node(@'10000000000); {merge adjacent free areas}
//! p:=rlink(rover); rlink(rover):=max_halfword; old_rover:=rover;
//! while p<>old_rover do @<Sort |p| into the list starting at |rover|
//!   and advance |p| to |rlink(p)|@>;
//! p:=rover;
//! while rlink(p)<>max_halfword do
//!   begin llink(rlink(p)):=p; p:=rlink(p);
//!   end;
//! rlink(p):=rover; llink(rover):=p;
//! end;
//! tini
//!
//! @ The following |while| loop is guaranteed to
//! terminate, since the list that starts at
//! |rover| ends with |max_halfword| during the sorting procedure.
//!
//! @<Sort |p|...@>=
//! if p<rover then
//!   begin q:=p; p:=rlink(q); rlink(q):=rover; rover:=q;
//!   end
//! else  begin q:=rover;
//!   while rlink(q)<p do q:=rlink(q);
//!   r:=rlink(p); rlink(p):=rlink(q); rlink(q):=p; p:=r;
//!   end
//!
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
//! @* \[12] The command codes.
//! Before we can go much further, we need to define symbolic names for the internal
//! code numbers that represent the various commands obeyed by \MF. These codes
//! are somewhat arbitrary, but not completely so. For example,
//! some codes have been made adjacent so that |case| statements in the
//! program need not consider cases that are widely spaced, or so that |case|
//! statements can be replaced by |if| statements. A command can begin an
//! expression if and only if its code lies between |min_primary_command| and
//! |max_primary_command|, inclusive. The first token of a statement that doesn't
//! begin with an expression has a command code between |min_command| and
//! |max_statement_command|, inclusive. The ordering of the highest-numbered
//! commands (|comma<semicolon<end_group<stop|) is crucial for the parsing
//! and error-recovery methods of this program.
//!
//! At any rate, here is the list, for future reference.
//!
//! @d if_test=1 {conditional text (\&{if})}
//! @d fi_or_else=2 {delimiters for conditionals (\&{elseif}, \&{else}, \&{fi})}
//! @d input=3 {input a source file (\&{input}, \&{endinput})}
//! @d iteration=4 {iterate (\&{for}, \&{forsuffixes}, \&{forever}, \&{endfor})}
//! @d repeat_loop=5 {special command substituted for \&{endfor}}
//! @d exit_test=6 {premature exit from a loop (\&{exitif})}
//! @d relax=7 {do nothing (\.{\char`\\})}
//! @d scan_tokens=8 {put a string into the input buffer}
//! @d expand_after=9 {look ahead one token}
//! @d defined_macro=10 {a macro defined by the user}
//! @d min_command=defined_macro+1
//! @d display_command=11 {online graphic output (\&{display})}
//! @d save_command=12 {save a list of tokens (\&{save})}
//! @d interim_command=13 {save an internal quantity (\&{interim})}
//! @d let_command=14 {redefine a symbolic token (\&{let})}
//! @d new_internal=15 {define a new internal quantity (\&{newinternal})}
//! @d macro_def=16 {define a macro (\&{def}, \&{vardef}, etc.)}
//! @d ship_out_command=17 {output a character (\&{shipout})}
//! @d add_to_command=18 {add to edges (\&{addto})}
//! @d cull_command=19 {cull and normalize edges (\&{cull})}
//! @d tfm_command=20 {command for font metric info (\&{ligtable}, etc.)}
//! @d protection_command=21 {set protection flag (\&{outer}, \&{inner})}
//! @d show_command=22 {diagnostic output (\&{show}, \&{showvariable}, etc.)}
//! @d mode_command=23 {set interaction level (\&{batchmode}, etc.)}
//! @d random_seed=24 {initialize random number generator (\&{randomseed})}
//! @d message_command=25 {communicate to user (\&{message}, \&{errmessage})}
//! @d every_job_command=26 {designate a starting token (\&{everyjob})}
//! @d delimiters=27 {define a pair of delimiters (\&{delimiters})}
//! @d open_window=28 {define a window on the screen (\&{openwindow})}
//! @d special_command=29 {output special info (\&{special}, \&{numspecial})}
//! @d type_name=30 {declare a type (\&{numeric}, \&{pair}, etc.)}
//! @d max_statement_command=type_name
//! @d min_primary_command=type_name
//! @d left_delimiter=31 {the left delimiter of a matching pair}
//! @d begin_group=32 {beginning of a group (\&{begingroup})}
//! @d nullary=33 {an operator without arguments (e.g., \&{normaldeviate})}
//! @d unary=34 {an operator with one argument (e.g., \&{sqrt})}
//! @d str_op=35 {convert a suffix to a string (\&{str})}
//! @d cycle=36 {close a cyclic path (\&{cycle})}
//! @d primary_binary=37 {binary operation taking `\&{of}' (e.g., \&{point})}
//! @d capsule_token=38 {a value that has been put into a token list}
//! @d string_token=39 {a string constant (e.g., |"hello"|)}
//! @d internal_quantity=40 {internal numeric parameter (e.g., \&{pausing})}
//! @d min_suffix_token=internal_quantity
//! @d tag_token=41 {a symbolic token without a primitive meaning}
//! @d numeric_token=42 {a numeric constant (e.g., \.{3.14159})}
//! @d max_suffix_token=numeric_token
//! @d plus_or_minus=43 {either `\.+' or `\.-'}
//! @d max_primary_command=plus_or_minus {should also be |numeric_token+1|}
//! @d min_tertiary_command=plus_or_minus
//! @d tertiary_secondary_macro=44 {a macro defined by \&{secondarydef}}
//! @d tertiary_binary=45 {an operator at the tertiary level (e.g., `\.{++}')}
//! @d max_tertiary_command=tertiary_binary
//! @d left_brace=46 {the operator `\.{\char`\{}'}
//! @d min_expression_command=left_brace
//! @d path_join=47 {the operator `\.{..}'}
//! @d ampersand=48 {the operator `\.\&'}
//! @d expression_tertiary_macro=49 {a macro defined by \&{tertiarydef}}
//! @d expression_binary=50 {an operator at the expression level (e.g., `\.<')}
//! @d equals=51 {the operator `\.='}
//! @d max_expression_command=equals
//! @d and_command=52 {the operator `\&{and}'}
//! @d min_secondary_command=and_command
//! @d secondary_primary_macro=53 {a macro defined by \&{primarydef}}
//! @d slash=54 {the operator `\./'}
//! @d secondary_binary=55 {an operator at the binary level (e.g., \&{shifted})}
//! @d max_secondary_command=secondary_binary
//! @d param_type=56 {type of parameter (\&{primary}, \&{expr}, \&{suffix}, etc.)}
//! @d controls=57 {specify control points explicitly (\&{controls})}
//! @d tension=58 {specify tension between knots (\&{tension})}
//! @d at_least=59 {bounded tension value (\&{atleast})}
//! @d curl_command=60 {specify curl at an end knot (\&{curl})}
//! @d macro_special=61 {special macro operators (\&{quote}, \.{\#\AT!}, etc.)}
//! @d right_delimiter=62 {the right delimiter of a matching pair}
//! @d left_bracket=63 {the operator `\.['}
//! @d right_bracket=64 {the operator `\.]'}
//! @d right_brace=65 {the operator `\.{\char`\}}'}
//! @d with_option=66 {option for filling (\&{withpen}, \&{withweight})}
//! @d cull_op=67 {the operator `\&{keeping}' or `\&{dropping}'}
//! @d thing_to_add=68
//!   {variant of \&{addto} (\&{contour}, \&{doublepath}, \&{also})}
//! @d of_token=69 {the operator `\&{of}'}
//! @d from_token=70 {the operator `\&{from}'}
//! @d to_token=71 {the operator `\&{to}'}
//! @d at_token=72 {the operator `\&{at}'}
//! @d in_window=73 {the operator `\&{inwindow}'}
//! @d step_token=74 {the operator `\&{step}'}
//! @d until_token=75 {the operator `\&{until}'}
//! @d lig_kern_token=76
//!   {the operators `\&{kern}' and `\.{=:}' and `\.{=:\char'174}', etc.}
//! @d assignment=77 {the operator `\.{:=}'}
//! @d skip_to=78 {the operation `\&{skipto}'}
//! @d bchar_label=79 {the operator `\.{\char'174\char'174:}'}
//! @d double_colon=80 {the operator `\.{::}'}
//! @d colon=81 {the operator `\.:'}
//! @#
//! @d comma=82 {the operator `\.,', must be |colon+1|}
//! @d end_of_statement==cur_cmd>comma
//! @d semicolon=83 {the operator `\.;', must be |comma+1|}
//! @d end_group=84 {end a group (\&{endgroup}), must be |semicolon+1|}
//! @d stop=85 {end a job (\&{end}, \&{dump}), must be |end_group+1|}
//! @d max_command_code=stop
//! @d outer_tag=max_command_code+1 {protection code added to command code}
//!
//! @<Types...@>=
//! @!command_code=1..max_command_code;
//!
//! @ Variables and capsules in \MF\ have a variety of ``types,''
//! distinguished by the following code numbers:
//!
//! @d undefined=0 {no type has been declared}
//! @d unknown_tag=1 {this constant is added to certain type codes below}
//! @d vacuous=1 {no expression was present}
//! @d boolean_type=2 {\&{boolean} with a known value}
//! @d unknown_boolean=boolean_type+unknown_tag
//! @d string_type=4 {\&{string} with a known value}
//! @d unknown_string=string_type+unknown_tag
//! @d pen_type=6 {\&{pen} with a known value}
//! @d unknown_pen=pen_type+unknown_tag
//! @d future_pen=8 {subexpression that will become a \&{pen} at a higher level}
//! @d path_type=9 {\&{path} with a known value}
//! @d unknown_path=path_type+unknown_tag
//! @d picture_type=11 {\&{picture} with a known value}
//! @d unknown_picture=picture_type+unknown_tag
//! @d transform_type=13 {\&{transform} variable or capsule}
//! @d pair_type=14 {\&{pair} variable or capsule}
//! @d numeric_type=15 {variable that has been declared \&{numeric} but not used}
//! @d known=16 {\&{numeric} with a known value}
//! @d dependent=17 {a linear combination with |fraction| coefficients}
//! @d proto_dependent=18 {a linear combination with |scaled| coefficients}
//! @d independent=19 {\&{numeric} with unknown value}
//! @d token_list=20 {variable name or suffix argument or text argument}
//! @d structured=21 {variable with subscripts and attributes}
//! @d unsuffixed_macro=22 {variable defined with \&{vardef} but no \.{\AT!\#}}
//! @d suffixed_macro=23 {variable defined with \&{vardef} and \.{\AT!\#}}
//! @#
//! @d unknown_types==unknown_boolean,unknown_string,
//!   unknown_pen,unknown_picture,unknown_path
//!
//! @<Basic printing procedures@>=
//! procedure print_type(@!t:small_number);
//! begin case t of
//! vacuous:print("vacuous");
//! boolean_type:print("boolean");
//! unknown_boolean:print("unknown boolean");
//! string_type:print("string");
//! unknown_string:print("unknown string");
//! pen_type:print("pen");
//! unknown_pen:print("unknown pen");
//! future_pen:print("future pen");
//! path_type:print("path");
//! unknown_path:print("unknown path");
//! picture_type:print("picture");
//! unknown_picture:print("unknown picture");
//! transform_type:print("transform");
//! pair_type:print("pair");
//! known:print("known numeric");
//! dependent:print("dependent");
//! proto_dependent:print("proto-dependent");
//! numeric_type:print("numeric");
//! independent:print("independent");
//! token_list:print("token list");
//! structured:print("structured");
//! unsuffixed_macro:print("unsuffixed macro");
//! suffixed_macro:print("suffixed macro");
//! othercases print("undefined")
//! endcases;
//! end;
//!
//! @ Values inside \MF\ are stored in two-word nodes that have a |name_type|
//! as well as a |type|. The possibilities for |name_type| are defined
//! here; they will be explained in more detail later.
//!
//! @d root=0 {|name_type| at the top level of a variable}
//! @d saved_root=1 {same, when the variable has been saved}
//! @d structured_root=2 {|name_type| where a |structured| branch occurs}
//! @d subscr=3 {|name_type| in a subscript node}
//! @d attr=4 {|name_type| in an attribute node}
//! @d x_part_sector=5 {|name_type| in the \&{xpart} of a node}
//! @d y_part_sector=6 {|name_type| in the \&{ypart} of a node}
//! @d xx_part_sector=7 {|name_type| in the \&{xxpart} of a node}
//! @d xy_part_sector=8 {|name_type| in the \&{xypart} of a node}
//! @d yx_part_sector=9 {|name_type| in the \&{yxpart} of a node}
//! @d yy_part_sector=10 {|name_type| in the \&{yypart} of a node}
//! @d capsule=11 {|name_type| in stashed-away subexpressions}
//! @d token=12 {|name_type| in a numeric token or string token}
//!
//! @ Primitive operations that produce values have a secondary identification
//! code in addition to their command code; it's something like genera and species.
//! For example, `\.*' has the command code |primary_binary|, and its
//! secondary identification is |times|. The secondary codes start at 30 so that
//! they don't overlap with the type codes; some type codes (e.g., |string_type|)
//! are used as operators as well as type identifications.
//!
//! @d true_code=30 {operation code for \.{true}}
//! @d false_code=31 {operation code for \.{false}}
//! @d null_picture_code=32 {operation code for \.{nullpicture}}
//! @d null_pen_code=33 {operation code for \.{nullpen}}
//! @d job_name_op=34 {operation code for \.{jobname}}
//! @d read_string_op=35 {operation code for \.{readstring}}
//! @d pen_circle=36 {operation code for \.{pencircle}}
//! @d normal_deviate=37 {operation code for \.{normaldeviate}}
//! @d odd_op=38 {operation code for \.{odd}}
//! @d known_op=39 {operation code for \.{known}}
//! @d unknown_op=40 {operation code for \.{unknown}}
//! @d not_op=41 {operation code for \.{not}}
//! @d decimal=42 {operation code for \.{decimal}}
//! @d reverse=43 {operation code for \.{reverse}}
//! @d make_path_op=44 {operation code for \.{makepath}}
//! @d make_pen_op=45 {operation code for \.{makepen}}
//! @d total_weight_op=46 {operation code for \.{totalweight}}
//! @d oct_op=47 {operation code for \.{oct}}
//! @d hex_op=48 {operation code for \.{hex}}
//! @d ASCII_op=49 {operation code for \.{ASCII}}
//! @d char_op=50 {operation code for \.{char}}
//! @d length_op=51 {operation code for \.{length}}
//! @d turning_op=52 {operation code for \.{turningnumber}}
//! @d x_part=53 {operation code for \.{xpart}}
//! @d y_part=54 {operation code for \.{ypart}}
//! @d xx_part=55 {operation code for \.{xxpart}}
//! @d xy_part=56 {operation code for \.{xypart}}
//! @d yx_part=57 {operation code for \.{yxpart}}
//! @d yy_part=58 {operation code for \.{yypart}}
//! @d sqrt_op=59 {operation code for \.{sqrt}}
//! @d m_exp_op=60 {operation code for \.{mexp}}
//! @d m_log_op=61 {operation code for \.{mlog}}
//! @d sin_d_op=62 {operation code for \.{sind}}
//! @d cos_d_op=63 {operation code for \.{cosd}}
//! @d floor_op=64 {operation code for \.{floor}}
//! @d uniform_deviate=65 {operation code for \.{uniformdeviate}}
//! @d char_exists_op=66 {operation code for \.{charexists}}
//! @d angle_op=67 {operation code for \.{angle}}
//! @d cycle_op=68 {operation code for \.{cycle}}
//! @d plus=69 {operation code for \.+}
//! @d minus=70 {operation code for \.-}
//! @d times=71 {operation code for \.*}
//! @d over=72 {operation code for \./}
//! @d pythag_add=73 {operation code for \.{++}}
//! @d pythag_sub=74 {operation code for \.{+-+}}
//! @d or_op=75 {operation code for \.{or}}
//! @d and_op=76 {operation code for \.{and}}
//! @d less_than=77 {operation code for \.<}
//! @d less_or_equal=78 {operation code for \.{<=}}
//! @d greater_than=79 {operation code for \.>}
//! @d greater_or_equal=80 {operation code for \.{>=}}
//! @d equal_to=81 {operation code for \.=}
//! @d unequal_to=82 {operation code for \.{<>}}
//! @d concatenate=83 {operation code for \.\&}
//! @d rotated_by=84 {operation code for \.{rotated}}
//! @d slanted_by=85 {operation code for \.{slanted}}
//! @d scaled_by=86 {operation code for \.{scaled}}
//! @d shifted_by=87 {operation code for \.{shifted}}
//! @d transformed_by=88 {operation code for \.{transformed}}
//! @d x_scaled=89 {operation code for \.{xscaled}}
//! @d y_scaled=90 {operation code for \.{yscaled}}
//! @d z_scaled=91 {operation code for \.{zscaled}}
//! @d intersect=92 {operation code for \.{intersectiontimes}}
//! @d double_dot=93 {operation code for improper \.{..}}
//! @d substring_of=94 {operation code for \.{substring}}
//! @d min_of=substring_of
//! @d subpath_of=95 {operation code for \.{subpath}}
//! @d direction_time_of=96 {operation code for \.{directiontime}}
//! @d point_of=97 {operation code for \.{point}}
//! @d precontrol_of=98 {operation code for \.{precontrol}}
//! @d postcontrol_of=99 {operation code for \.{postcontrol}}
//! @d pen_offset_of=100 {operation code for \.{penoffset}}
//!
//! @p procedure print_op(@!c:quarterword);
//! begin if c<=numeric_type then print_type(c)
//! else case c of
//! true_code:print("true");
//! false_code:print("false");
//! null_picture_code:print("nullpicture");
//! null_pen_code:print("nullpen");
//! job_name_op:print("jobname");
//! read_string_op:print("readstring");
//! pen_circle:print("pencircle");
//! normal_deviate:print("normaldeviate");
//! odd_op:print("odd");
//! known_op:print("known");
//! unknown_op:print("unknown");
//! not_op:print("not");
//! decimal:print("decimal");
//! reverse:print("reverse");
//! make_path_op:print("makepath");
//! make_pen_op:print("makepen");
//! total_weight_op:print("totalweight");
//! oct_op:print("oct");
//! hex_op:print("hex");
//! ASCII_op:print("ASCII");
//! char_op:print("char");
//! length_op:print("length");
//! turning_op:print("turningnumber");
//! x_part:print("xpart");
//! y_part:print("ypart");
//! xx_part:print("xxpart");
//! xy_part:print("xypart");
//! yx_part:print("yxpart");
//! yy_part:print("yypart");
//! sqrt_op:print("sqrt");
//! m_exp_op:print("mexp");
//! m_log_op:print("mlog");
//! sin_d_op:print("sind");
//! cos_d_op:print("cosd");
//! floor_op:print("floor");
//! uniform_deviate:print("uniformdeviate");
//! char_exists_op:print("charexists");
//! angle_op:print("angle");
//! cycle_op:print("cycle");
//! plus:print_char("+");
//! minus:print_char("-");
//! times:print_char("*");
//! over:print_char("/");
//! pythag_add:print("++");
//! pythag_sub:print("+-+");
//! or_op:print("or");
//! and_op:print("and");
//! less_than:print_char("<");
//! less_or_equal:print("<=");
//! greater_than:print_char(">");
//! greater_or_equal:print(">=");
//! equal_to:print_char("=");
//! unequal_to:print("<>");
//! concatenate:print("&");
//! rotated_by:print("rotated");
//! slanted_by:print("slanted");
//! scaled_by:print("scaled");
//! shifted_by:print("shifted");
//! transformed_by:print("transformed");
//! x_scaled:print("xscaled");
//! y_scaled:print("yscaled");
//! z_scaled:print("zscaled");
//! intersect:print("intersectiontimes");
//! substring_of:print("substring");
//! subpath_of:print("subpath");
//! direction_time_of:print("directiontime");
//! point_of:print("point");
//! precontrol_of:print("precontrol");
//! postcontrol_of:print("postcontrol");
//! pen_offset_of:print("penoffset");
//! othercases print("..")
//! endcases;
//! end;
//!
//! @ \MF\ also has a bunch of internal parameters that a user might want to
//! fuss with. Every such parameter has an identifying code number, defined here.
//!
//! @d tracing_titles=1 {show titles online when they appear}
//! @d tracing_equations=2 {show each variable when it becomes known}
//! @d tracing_capsules=3 {show capsules too}
//! @d tracing_choices=4 {show the control points chosen for paths}
//! @d tracing_specs=5 {show subdivision of paths into octants before digitizing}
//! @d tracing_pens=6 {show details of pens that are made}
//! @d tracing_commands=7 {show commands and operations before they are performed}
//! @d tracing_restores=8 {show when a variable or internal is restored}
//! @d tracing_macros=9 {show macros before they are expanded}
//! @d tracing_edges=10 {show digitized edges as they are computed}
//! @d tracing_output=11 {show digitized edges as they are output}
//! @d tracing_stats=12 {show memory usage at end of job}
//! @d tracing_online=13 {show long diagnostics on terminal and in the log file}
//! @d year=14 {the current year (e.g., 1984)}
//! @d month=15 {the current month (e.g., 3 $\equiv$ March)}
//! @d day=16 {the current day of the month}
//! @d time=17 {the number of minutes past midnight when this job started}
//! @d char_code=18 {the number of the next character to be output}
//! @d char_ext=19 {the extension code of the next character to be output}
//! @d char_wd=20 {the width of the next character to be output}
//! @d char_ht=21 {the height of the next character to be output}
//! @d char_dp=22 {the depth of the next character to be output}
//! @d char_ic=23 {the italic correction of the next character to be output}
//! @d char_dx=24 {the device's $x$ movement for the next character, in pixels}
//! @d char_dy=25 {the device's $y$ movement for the next character, in pixels}
//! @d design_size=26 {the unit of measure used for |char_wd..char_ic|, in points}
//! @d hppp=27 {the number of horizontal pixels per point}
//! @d vppp=28 {the number of vertical pixels per point}
//! @d x_offset=29 {horizontal displacement of shipped-out characters}
//! @d y_offset=30 {vertical displacement of shipped-out characters}
//! @d pausing=31 {positive to display lines on the terminal before they are read}
//! @d showstopping=32 {positive to stop after each \&{show} command}
//! @d fontmaking=33 {positive if font metric output is to be produced}
//! @d proofing=34 {positive for proof mode, negative to suppress output}
//! @d smoothing=35 {positive if moves are to be ``smoothed''}
//! @d autorounding=36 {controls path modification to ``good'' points}
//! @d granularity=37 {autorounding uses this pixel size}
//! @d fillin=38 {extra darkness of diagonal lines}
//! @d turning_check=39 {controls reorientation of clockwise paths}
//! @d warning_check=40 {controls error message when variable value is large}
//! @d boundary_char=41 {the boundary character for ligatures}
//! @d max_given_internal=41
//!
//! @<Glob...@>=
//! @!internal:array[1..max_internal] of scaled;
//!   {the values of internal quantities}
//! @!int_name:array[1..max_internal] of str_number;
//!   {their names}
//! @!int_ptr:max_given_internal..max_internal;
//!   {the maximum internal quantity defined so far}
//!
//! @ @<Set init...@>=
//! for k:=1 to max_given_internal do internal[k]:=0;
//! int_ptr:=max_given_internal;
//!
//! @ The symbolic names for internal quantities are put into \MF's hash table
//! by using a routine called |primitive|, which will be defined later. Let us
//! enter them now, so that we don't have to list all those names again
//! anywhere else.
//!
//! @<Put each of \MF's primitives into the hash table@>=
//! primitive("tracingtitles",internal_quantity,tracing_titles);@/
//! @!@:tracingtitles_}{\&{tracingtitles} primitive@>
//! primitive("tracingequations",internal_quantity,tracing_equations);@/
//! @!@:tracing_equations_}{\&{tracingequations} primitive@>
//! primitive("tracingcapsules",internal_quantity,tracing_capsules);@/
//! @!@:tracing_capsules_}{\&{tracingcapsules} primitive@>
//! primitive("tracingchoices",internal_quantity,tracing_choices);@/
//! @!@:tracing_choices_}{\&{tracingchoices} primitive@>
//! primitive("tracingspecs",internal_quantity,tracing_specs);@/
//! @!@:tracing_specs_}{\&{tracingspecs} primitive@>
//! primitive("tracingpens",internal_quantity,tracing_pens);@/
//! @!@:tracing_pens_}{\&{tracingpens} primitive@>
//! primitive("tracingcommands",internal_quantity,tracing_commands);@/
//! @!@:tracing_commands_}{\&{tracingcommands} primitive@>
//! primitive("tracingrestores",internal_quantity,tracing_restores);@/
//! @!@:tracing_restores_}{\&{tracingrestores} primitive@>
//! primitive("tracingmacros",internal_quantity,tracing_macros);@/
//! @!@:tracing_macros_}{\&{tracingmacros} primitive@>
//! primitive("tracingedges",internal_quantity,tracing_edges);@/
//! @!@:tracing_edges_}{\&{tracingedges} primitive@>
//! primitive("tracingoutput",internal_quantity,tracing_output);@/
//! @!@:tracing_output_}{\&{tracingoutput} primitive@>
//! primitive("tracingstats",internal_quantity,tracing_stats);@/
//! @!@:tracing_stats_}{\&{tracingstats} primitive@>
//! primitive("tracingonline",internal_quantity,tracing_online);@/
//! @!@:tracing_online_}{\&{tracingonline} primitive@>
//! primitive("year",internal_quantity,year);@/
//! @!@:year_}{\&{year} primitive@>
//! primitive("month",internal_quantity,month);@/
//! @!@:month_}{\&{month} primitive@>
//! primitive("day",internal_quantity,day);@/
//! @!@:day_}{\&{day} primitive@>
//! primitive("time",internal_quantity,time);@/
//! @!@:time_}{\&{time} primitive@>
//! primitive("charcode",internal_quantity,char_code);@/
//! @!@:char_code_}{\&{charcode} primitive@>
//! primitive("charext",internal_quantity,char_ext);@/
//! @!@:char_ext_}{\&{charext} primitive@>
//! primitive("charwd",internal_quantity,char_wd);@/
//! @!@:char_wd_}{\&{charwd} primitive@>
//! primitive("charht",internal_quantity,char_ht);@/
//! @!@:char_ht_}{\&{charht} primitive@>
//! primitive("chardp",internal_quantity,char_dp);@/
//! @!@:char_dp_}{\&{chardp} primitive@>
//! primitive("charic",internal_quantity,char_ic);@/
//! @!@:char_ic_}{\&{charic} primitive@>
//! primitive("chardx",internal_quantity,char_dx);@/
//! @!@:char_dx_}{\&{chardx} primitive@>
//! primitive("chardy",internal_quantity,char_dy);@/
//! @!@:char_dy_}{\&{chardy} primitive@>
//! primitive("designsize",internal_quantity,design_size);@/
//! @!@:design_size_}{\&{designsize} primitive@>
//! primitive("hppp",internal_quantity,hppp);@/
//! @!@:hppp_}{\&{hppp} primitive@>
//! primitive("vppp",internal_quantity,vppp);@/
//! @!@:vppp_}{\&{vppp} primitive@>
//! primitive("xoffset",internal_quantity,x_offset);@/
//! @!@:x_offset_}{\&{xoffset} primitive@>
//! primitive("yoffset",internal_quantity,y_offset);@/
//! @!@:y_offset_}{\&{yoffset} primitive@>
//! primitive("pausing",internal_quantity,pausing);@/
//! @!@:pausing_}{\&{pausing} primitive@>
//! primitive("showstopping",internal_quantity,showstopping);@/
//! @!@:showstopping_}{\&{showstopping} primitive@>
//! primitive("fontmaking",internal_quantity,fontmaking);@/
//! @!@:fontmaking_}{\&{fontmaking} primitive@>
//! primitive("proofing",internal_quantity,proofing);@/
//! @!@:proofing_}{\&{proofing} primitive@>
//! primitive("smoothing",internal_quantity,smoothing);@/
//! @!@:smoothing_}{\&{smoothing} primitive@>
//! primitive("autorounding",internal_quantity,autorounding);@/
//! @!@:autorounding_}{\&{autorounding} primitive@>
//! primitive("granularity",internal_quantity,granularity);@/
//! @!@:granularity_}{\&{granularity} primitive@>
//! primitive("fillin",internal_quantity,fillin);@/
//! @!@:fillin_}{\&{fillin} primitive@>
//! primitive("turningcheck",internal_quantity,turning_check);@/
//! @!@:turning_check_}{\&{turningcheck} primitive@>
//! primitive("warningcheck",internal_quantity,warning_check);@/
//! @!@:warning_check_}{\&{warningcheck} primitive@>
//! primitive("boundarychar",internal_quantity,boundary_char);@/
//! @!@:boundary_char_}{\&{boundarychar} primitive@>
//!
//! @ Well, we do have to list the names one more time, for use in symbolic
//! printouts.
//!
//! @<Initialize table...@>=
//! int_name[tracing_titles]:="tracingtitles";
//! int_name[tracing_equations]:="tracingequations";
//! int_name[tracing_capsules]:="tracingcapsules";
//! int_name[tracing_choices]:="tracingchoices";
//! int_name[tracing_specs]:="tracingspecs";
//! int_name[tracing_pens]:="tracingpens";
//! int_name[tracing_commands]:="tracingcommands";
//! int_name[tracing_restores]:="tracingrestores";
//! int_name[tracing_macros]:="tracingmacros";
//! int_name[tracing_edges]:="tracingedges";
//! int_name[tracing_output]:="tracingoutput";
//! int_name[tracing_stats]:="tracingstats";
//! int_name[tracing_online]:="tracingonline";
//! int_name[year]:="year";
//! int_name[month]:="month";
//! int_name[day]:="day";
//! int_name[time]:="time";
//! int_name[char_code]:="charcode";
//! int_name[char_ext]:="charext";
//! int_name[char_wd]:="charwd";
//! int_name[char_ht]:="charht";
//! int_name[char_dp]:="chardp";
//! int_name[char_ic]:="charic";
//! int_name[char_dx]:="chardx";
//! int_name[char_dy]:="chardy";
//! int_name[design_size]:="designsize";
//! int_name[hppp]:="hppp";
//! int_name[vppp]:="vppp";
//! int_name[x_offset]:="xoffset";
//! int_name[y_offset]:="yoffset";
//! int_name[pausing]:="pausing";
//! int_name[showstopping]:="showstopping";
//! int_name[fontmaking]:="fontmaking";
//! int_name[proofing]:="proofing";
//! int_name[smoothing]:="smoothing";
//! int_name[autorounding]:="autorounding";
//! int_name[granularity]:="granularity";
//! int_name[fillin]:="fillin";
//! int_name[turning_check]:="turningcheck";
//! int_name[warning_check]:="warningcheck";
//! int_name[boundary_char]:="boundarychar";
//!
//! @ The following procedure, which is called just before \MF\ initializes its
//! input and output, establishes the initial values of the date and time.
//! @^system dependencies@>
//! Since standard \PASCAL\ cannot provide such information, something special
//! is needed. The program here simply assumes that suitable values appear in
//! the global variables \\{sys\_time}, \\{sys\_day}, \\{sys\_month}, and
//! \\{sys\_year} (which are initialized to noon on 4 July 1776,
//! in case the implementor is careless).
//!
//! Note that the values are |scaled| integers. Hence \MF\ can no longer
//! be used after the year 32767.
//!
//! @p procedure fix_date_and_time;
//! begin sys_time:=12*60;
//! sys_day:=4; sys_month:=7; sys_year:=1776;  {self-evident truths}
//! internal[time]:=sys_time*unity; {minutes since midnight}
//! internal[day]:=sys_day*unity; {day of the month}
//! internal[month]:=sys_month*unity; {month of the year}
//! internal[year]:=sys_year*unity; {Anno Domini}
//! end;
//!
//! @ \MF\ is occasionally supposed to print diagnostic information that
//! goes only into the transcript file, unless |tracing_online| is positive.
//! Now that we have defined |tracing_online| we can define
//! two routines that adjust the destination of print commands:
//!
//! @<Basic printing...@>=
//! procedure begin_diagnostic; {prepare to do some tracing}
//! begin old_setting:=selector;
//! if(internal[tracing_online]<=0)and(selector=term_and_log) then
//!   begin decr(selector);
//!   if history=spotless then history:=warning_issued;
//!   end;
//! end;
//! @#
//! procedure end_diagnostic(@!blank_line:boolean);
//!   {restore proper conditions after tracing}
//! begin print_nl("");
//! if blank_line then print_ln;
//! selector:=old_setting;
//! end;
//!
//! @ Of course we had better declare a few more global variables, if the previous
//! routines are going to work.
//!
//! @<Glob...@>=
//! @!old_setting:0..max_selector;
//! @!sys_time,@!sys_day,@!sys_month,@!sys_year:integer;
//!     {date and time supplied by external system}
//!
//! @ We will occasionally use |begin_diagnostic| in connection with line-number
//! printing, as follows. (The parameter |s| is typically |"Path"| or
//! |"Cycle spec"|, etc.)
//!
//! @<Basic printing...@>=
//! procedure print_diagnostic(@!s,@!t:str_number;@!nuline:boolean);
//! begin begin_diagnostic;
//! if nuline then print_nl(s)@+else print(s);
//! print(" at line "); print_int(line);
//! print(t); print_char(":");
//! end;
//!
//! @ The 256 |ASCII_code| characters are grouped into classes by means of
//! the |char_class| table. Individual class numbers have no semantic
//! or syntactic significance, except in a few instances defined here.
//! There's also |max_class|, which can be used as a basis for additional
//! class numbers in nonstandard extensions of \MF.
//!
//! @d digit_class=0 {the class number of \.{0123456789}}
//! @d period_class=1 {the class number of `\..'}
//! @d space_class=2 {the class number of spaces and nonstandard characters}
//! @d percent_class=3 {the class number of `\.\%'}
//! @d string_class=4 {the class number of `\."'}
//! @d right_paren_class=8 {the class number of `\.)'}
//! @d isolated_classes==5,6,7,8 {characters that make length-one tokens only}
//! @d letter_class=9 {letters and the underline character}
//! @d left_bracket_class=17 {`\.['}
//! @d right_bracket_class=18 {`\.]'}
//! @d invalid_class=20 {bad character in the input}
//! @d max_class=20 {the largest class number}
//!
//! @<Glob...@>=
//! @!char_class:array[ASCII_code] of 0..max_class; {the class numbers}
//!
//! @ If changes are made to accommodate non-ASCII character sets, they should
//! follow the guidelines in Appendix~C of {\sl The {\logos METAFONT\/}book}.
//! @:METAFONTbook}{\sl The {\logos METAFONT\/}book@>
//! @^system dependencies@>
//!
//! @<Set init...@>=
//! for k:="0" to "9" do char_class[k]:=digit_class;
//! char_class["."]:=period_class;
//! char_class[" "]:=space_class;
//! char_class["%"]:=percent_class;
//! char_class[""""]:=string_class;@/
//! char_class[","]:=5;
//! char_class[";"]:=6;
//! char_class["("]:=7;
//! char_class[")"]:=right_paren_class;
//! for k:="A" to "Z" do char_class[k]:=letter_class;
//! for k:="a" to "z" do char_class[k]:=letter_class;
//! char_class["_"]:=letter_class;@/
//! char_class["<"]:=10;
//! char_class["="]:=10;
//! char_class[">"]:=10;
//! char_class[":"]:=10;
//! char_class["|"]:=10;@/
//! char_class["`"]:=11;
//! char_class["'"]:=11;@/
//! char_class["+"]:=12;
//! char_class["-"]:=12;@/
//! char_class["/"]:=13;
//! char_class["*"]:=13;
//! char_class["\"]:=13;@/
//! char_class["!"]:=14;
//! char_class["?"]:=14;@/
//! char_class["#"]:=15;
//! char_class["&"]:=15;
//! char_class["@@"]:=15;
//! char_class["$"]:=15;@/
//! char_class["^"]:=16;
//! char_class["~"]:=16;@/
//! char_class["["]:=left_bracket_class;
//! char_class["]"]:=right_bracket_class;@/
//! char_class["{"]:=19;
//! char_class["}"]:=19;@/
//! for k:=0 to " "-1 do char_class[k]:=invalid_class;
//! for k:=127 to 255 do char_class[k]:=invalid_class;
//!
