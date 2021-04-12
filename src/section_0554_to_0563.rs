//! @ Computation of the min and max is a tedious but fairly fast sequence of
//! instructions; exactly four comparisons are made in each branch.
//!
//! @d set_min_max(#)==
//!   if stack_1(#)<0 then
//!     if stack_3(#)>=0 then
//!       begin if stack_2(#)<0 then stack_min(#):=stack_1(#)+stack_2(#)
//!         else stack_min(#):=stack_1(#);
//!       stack_max(#):=stack_1(#)+stack_2(#)+stack_3(#);
//!       if stack_max(#)<0 then stack_max(#):=0;
//!       end
//!     else  begin stack_min(#):=stack_1(#)+stack_2(#)+stack_3(#);
//!       if stack_min(#)>stack_1(#) then stack_min(#):=stack_1(#);
//!       stack_max(#):=stack_1(#)+stack_2(#);
//!       if stack_max(#)<0 then stack_max(#):=0;
//!       end
//!   else if stack_3(#)<=0 then
//!     begin if stack_2(#)>0 then stack_max(#):=stack_1(#)+stack_2(#)
//!       else stack_max(#):=stack_1(#);
//!     stack_min(#):=stack_1(#)+stack_2(#)+stack_3(#);
//!     if stack_min(#)>0 then stack_min(#):=0;
//!     end
//!   else  begin stack_max(#):=stack_1(#)+stack_2(#)+stack_3(#);
//!     if stack_max(#)<stack_1(#) then stack_max(#):=stack_1(#);
//!     stack_min(#):=stack_1(#)+stack_2(#);
//!     if stack_min(#)>0 then stack_min(#):=0;
//!     end
//!
//! @ It's convenient to keep the current values of $l$, $t_1$, and $t_2$ in
//! the integer form $2^l+2^lt_1$ and $2^l+2^lt_2$. The |cubic_intersection|
//! routine uses global variables |cur_t| and |cur_tt| for this purpose;
//! after successful completion, |cur_t| and |cur_tt| will contain |unity|
//! plus the |scaled| values of $t_1$ and~$t_2$.
//!
//! The values of |cur_t| and |cur_tt| will be set to zero if |cubic_intersection|
//! finds no intersection. The routine gives up and gives an approximate answer
//! if it has backtracked
//! more than 5000 times (otherwise there are cases where several minutes
//! of fruitless computation would be possible).
//!
//! @d max_patience=5000
//!
//! @<Glob...@>=
//! @!cur_t,@!cur_tt:integer; {controls and results of |cubic_intersection|}
//! @!time_to_go:integer; {this many backtracks before giving up}
//! @!max_t:integer; {maximum of $2^{l+1}$ so far achieved}
//!
//! @ The given cubics $B(w_0,w_1,w_2,w_3;t)$ and
//! $B(z_0,z_1,z_2,z_3;t)$ are specified in adjacent knot nodes |(p,link(p))|
//! and |(pp,link(pp))|, respectively.
//!
//! @p procedure cubic_intersection(@!p,@!pp:pointer);
//! label continue, not_found, exit;
//! var @!q,@!qq:pointer; {|link(p)|, |link(pp)|}
//! begin time_to_go:=max_patience; max_t:=2;
//! @<Initialize for intersections at level zero@>;
//! loop@+  begin continue:
//!   if delx-tol<=stack_max(x_packet(xy))-stack_min(u_packet(uv)) then
//!    if delx+tol>=stack_min(x_packet(xy))-stack_max(u_packet(uv)) then
//!    if dely-tol<=stack_max(y_packet(xy))-stack_min(v_packet(uv)) then
//!    if dely+tol>=stack_min(y_packet(xy))-stack_max(v_packet(uv)) then
//!     begin if cur_t>=max_t then
//!       begin if max_t=two then {we've done 17 bisections}
//!         begin cur_t:=half(cur_t+1); cur_tt:=half(cur_tt+1); return;
//!         end;
//!       double(max_t); appr_t:=cur_t; appr_tt:=cur_tt;
//!       end;
//!     @<Subdivide for a new level of intersection@>;
//!     goto continue;
//!     end;
//!   if time_to_go>0 then decr(time_to_go)
//!   else  begin while appr_t<unity do
//!       begin double(appr_t); double(appr_tt);
//!       end;
//!     cur_t:=appr_t; cur_tt:=appr_tt; return;
//!     end;
//!   @<Advance to the next pair |(cur_t,cur_tt)|@>;
//!   end;
//! exit:end;
//!
//! @ The following variables are global, although they are used only by
//! |cubic_intersection|, because it is necessary on some machines to
//! split |cubic_intersection| up into two procedures.
//!
//! @<Glob...@>=
//! @!delx,@!dely:integer; {the components of $\Delta=2^l(w_0-z_0)$}
//! @!tol:integer; {bound on the uncertainty in the overlap test}
//! @!uv,@!xy:0..bistack_size; {pointers to the current packets of interest}
//! @!three_l:integer; {|tol_step| times the bisection level}
//! @!appr_t,@!appr_tt:integer; {best approximations known to the answers}
//!
//! @ We shall assume that the coordinates are sufficiently non-extreme that
//! integer overflow will not occur.
//! @^overflow in arithmetic@>
//!
//! @<Initialize for intersections at level zero@>=
//! q:=link(p); qq:=link(pp); bisect_ptr:=int_packets;@/
//! u1r:=right_x(p)-x_coord(p); u2r:=left_x(q)-right_x(p);
//! u3r:=x_coord(q)-left_x(q); set_min_max(ur_packet);@/
//! v1r:=right_y(p)-y_coord(p); v2r:=left_y(q)-right_y(p);
//! v3r:=y_coord(q)-left_y(q); set_min_max(vr_packet);@/
//! x1r:=right_x(pp)-x_coord(pp); x2r:=left_x(qq)-right_x(pp);
//! x3r:=x_coord(qq)-left_x(qq); set_min_max(xr_packet);@/
//! y1r:=right_y(pp)-y_coord(pp); y2r:=left_y(qq)-right_y(pp);
//! y3r:=y_coord(qq)-left_y(qq); set_min_max(yr_packet);@/
//! delx:=x_coord(p)-x_coord(pp); dely:=y_coord(p)-y_coord(pp);@/
//! tol:=0; uv:=r_packets; xy:=r_packets; three_l:=0; cur_t:=1; cur_tt:=1
//!
//! @ @<Subdivide for a new level of intersection@>=
//! stack_dx:=delx; stack_dy:=dely; stack_tol:=tol; stack_uv:=uv; stack_xy:=xy;
//! bisect_ptr:=bisect_ptr+int_increment;@/
//! double(cur_t); double(cur_tt);@/
//! u1l:=stack_1(u_packet(uv)); u3r:=stack_3(u_packet(uv));
//! u2l:=half(u1l+stack_2(u_packet(uv)));
//! u2r:=half(u3r+stack_2(u_packet(uv)));
//! u3l:=half(u2l+u2r); u1r:=u3l;
//! set_min_max(ul_packet); set_min_max(ur_packet);@/
//! v1l:=stack_1(v_packet(uv)); v3r:=stack_3(v_packet(uv));
//! v2l:=half(v1l+stack_2(v_packet(uv)));
//! v2r:=half(v3r+stack_2(v_packet(uv)));
//! v3l:=half(v2l+v2r); v1r:=v3l;
//! set_min_max(vl_packet); set_min_max(vr_packet);@/
//! x1l:=stack_1(x_packet(xy)); x3r:=stack_3(x_packet(xy));
//! x2l:=half(x1l+stack_2(x_packet(xy)));
//! x2r:=half(x3r+stack_2(x_packet(xy)));
//! x3l:=half(x2l+x2r); x1r:=x3l;
//! set_min_max(xl_packet); set_min_max(xr_packet);@/
//! y1l:=stack_1(y_packet(xy)); y3r:=stack_3(y_packet(xy));
//! y2l:=half(y1l+stack_2(y_packet(xy)));
//! y2r:=half(y3r+stack_2(y_packet(xy)));
//! y3l:=half(y2l+y2r); y1r:=y3l;
//! set_min_max(yl_packet); set_min_max(yr_packet);@/
//! uv:=l_packets; xy:=l_packets;
//! double(delx); double(dely);@/
//! tol:=tol-three_l+tol_step; double(tol); three_l:=three_l+tol_step
//!
//! @ @<Advance to the next pair |(cur_t,cur_tt)|@>=
//! not_found: if odd(cur_tt) then
//!   if odd(cur_t) then @<Descend to the previous level and |goto not_found|@>
//!   else  begin incr(cur_t);
//!     delx:=delx+stack_1(u_packet(uv))+stack_2(u_packet(uv))
//!       +stack_3(u_packet(uv));
//!     dely:=dely+stack_1(v_packet(uv))+stack_2(v_packet(uv))
//!       +stack_3(v_packet(uv));
//!     uv:=uv+int_packets; {switch from |l_packets| to |r_packets|}
//!     decr(cur_tt); xy:=xy-int_packets; {switch from |r_packets| to |l_packets|}
//!     delx:=delx+stack_1(x_packet(xy))+stack_2(x_packet(xy))
//!       +stack_3(x_packet(xy));
//!     dely:=dely+stack_1(y_packet(xy))+stack_2(y_packet(xy))
//!       +stack_3(y_packet(xy));
//!     end
//! else  begin incr(cur_tt); tol:=tol+three_l;
//!   delx:=delx-stack_1(x_packet(xy))-stack_2(x_packet(xy))
//!     -stack_3(x_packet(xy));
//!   dely:=dely-stack_1(y_packet(xy))-stack_2(y_packet(xy))
//!     -stack_3(y_packet(xy));
//!   xy:=xy+int_packets; {switch from |l_packets| to |r_packets|}
//!   end
//!
//! @ @<Descend to the previous level...@>=
//! begin cur_t:=half(cur_t); cur_tt:=half(cur_tt);
//! if cur_t=0 then return;
//! bisect_ptr:=bisect_ptr-int_increment; three_l:=three_l-tol_step;
//! delx:=stack_dx; dely:=stack_dy; tol:=stack_tol; uv:=stack_uv; xy:=stack_xy;@/
//! goto not_found;
//! end
//!
//! @ The |path_intersection| procedure is much simpler.
//! It invokes |cubic_intersection| in lexicographic order until finding a
//! pair of cubics that intersect. The final intersection times are placed in
//! |cur_t| and~|cur_tt|.
//!
//! @p procedure path_intersection(@!h,@!hh:pointer);
//! label exit;
//! var @!p,@!pp:pointer; {link registers that traverse the given paths}
//! @!n,@!nn:integer; {integer parts of intersection times, minus |unity|}
//! begin @<Change one-point paths into dead cycles@>;
//! tol_step:=0;
//! repeat n:=-unity; p:=h;
//!   repeat if right_type(p)<>endpoint then
//!     begin nn:=-unity; pp:=hh;
//!     repeat if right_type(pp)<>endpoint then
//!       begin cubic_intersection(p,pp);
//!       if cur_t>0 then
//!         begin cur_t:=cur_t+n; cur_tt:=cur_tt+nn; return;
//!         end;
//!       end;
//!     nn:=nn+unity; pp:=link(pp);
//!     until pp=hh;
//!     end;
//!   n:=n+unity; p:=link(p);
//!   until p=h;
//! tol_step:=tol_step+3;
//! until tol_step>3;
//! cur_t:=-unity; cur_tt:=-unity;
//! exit:end;
//!
//! @ @<Change one-point paths...@>=
//! if right_type(h)=endpoint then
//!   begin right_x(h):=x_coord(h); left_x(h):=x_coord(h);
//!   right_y(h):=y_coord(h); left_y(h):=y_coord(h); right_type(h):=explicit;
//!   end;
//! if right_type(hh)=endpoint then
//!   begin right_x(hh):=x_coord(hh); left_x(hh):=x_coord(hh);
//!   right_y(hh):=y_coord(hh); left_y(hh):=y_coord(hh); right_type(hh):=explicit;
//!   end;
//!
