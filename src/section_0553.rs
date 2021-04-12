//! @ We shall use an explicit stack to implement the recursive bisection
//! method described above. In fact, the |bisect_stack| array is available for
//! this purpose. It will contain numerous 5-word packets like
//! $(U_1,U_2,U_3,U\submin,U\submax)$, as well as 20-word packets comprising
//! the 5-word packets for $U$, $V$, $X$, and~$Y$.
//!
//! The following macros define the allocation of stack positions to
//! the quantities needed for bisection-intersection.
//
// @d stack_1(#)==bisect_stack[#] {$U_1$, $V_1$, $X_1$, or $Y_1$}
// @d stack_2(#)==bisect_stack[#+1] {$U_2$, $V_2$, $X_2$, or $Y_2$}
// @d stack_3(#)==bisect_stack[#+2] {$U_3$, $V_3$, $X_3$, or $Y_3$}
// @d stack_min(#)==bisect_stack[#+3]
//   {$U\submin$, $V\submin$, $X\submin$, or $Y\submin$}
// @d stack_max(#)==bisect_stack[#+4]
//   {$U\submax$, $V\submax$, $X\submax$, or $Y\submax$}
// @d int_packets=20 {number of words to represent $U_k$, $V_k$, $X_k$, and $Y_k$}
/// number of words to represent `U_k`, `V_k`, `X_k`, and `Y_k`
pub(crate) const int_packets: word = 20;
// @#
// @d u_packet(#)==#-5
// @d v_packet(#)==#-10
// @d x_packet(#)==#-15
// @d y_packet(#)==#-20
// @d l_packets==bisect_ptr-int_packets
// @d r_packets==bisect_ptr
// @d ul_packet==u_packet(l_packets) {base of $U'_k$ variables}
// @d vl_packet==v_packet(l_packets) {base of $V'_k$ variables}
// @d xl_packet==x_packet(l_packets) {base of $X'_k$ variables}
// @d yl_packet==y_packet(l_packets) {base of $Y'_k$ variables}
// @d ur_packet==u_packet(r_packets) {base of $U''_k$ variables}
// @d vr_packet==v_packet(r_packets) {base of $V''_k$ variables}
// @d xr_packet==x_packet(r_packets) {base of $X''_k$ variables}
// @d yr_packet==y_packet(r_packets) {base of $Y''_k$ variables}
// @#
// @d u1l==stack_1(ul_packet) {$U'_1$}
// @d u2l==stack_2(ul_packet) {$U'_2$}
// @d u3l==stack_3(ul_packet) {$U'_3$}
// @d v1l==stack_1(vl_packet) {$V'_1$}
// @d v2l==stack_2(vl_packet) {$V'_2$}
// @d v3l==stack_3(vl_packet) {$V'_3$}
// @d x1l==stack_1(xl_packet) {$X'_1$}
// @d x2l==stack_2(xl_packet) {$X'_2$}
// @d x3l==stack_3(xl_packet) {$X'_3$}
// @d y1l==stack_1(yl_packet) {$Y'_1$}
// @d y2l==stack_2(yl_packet) {$Y'_2$}
// @d y3l==stack_3(yl_packet) {$Y'_3$}
// @d u1r==stack_1(ur_packet) {$U''_1$}
// @d u2r==stack_2(ur_packet) {$U''_2$}
// @d u3r==stack_3(ur_packet) {$U''_3$}
// @d v1r==stack_1(vr_packet) {$V''_1$}
// @d v2r==stack_2(vr_packet) {$V''_2$}
// @d v3r==stack_3(vr_packet) {$V''_3$}
// @d x1r==stack_1(xr_packet) {$X''_1$}
// @d x2r==stack_2(xr_packet) {$X''_2$}
// @d x3r==stack_3(xr_packet) {$X''_3$}
// @d y1r==stack_1(yr_packet) {$Y''_1$}
// @d y2r==stack_2(yr_packet) {$Y''_2$}
// @d y3r==stack_3(yr_packet) {$Y''_3$}
// @#
// @d stack_dx==bisect_stack[bisect_ptr] {stacked value of |delx|}
// @d stack_dy==bisect_stack[bisect_ptr+1] {stacked value of |dely|}
// @d stack_tol==bisect_stack[bisect_ptr+2] {stacked value of |tol|}
// @d stack_uv==bisect_stack[bisect_ptr+3] {stacked value of |uv|}
// @d stack_xy==bisect_stack[bisect_ptr+4] {stacked value of |xy|}
// @d int_increment=int_packets+int_packets+5 {number of stack words per level}
/// number of stack words per level
pub(crate) const int_increment: word = int_packets + int_packets + 5;

// @<Check the ``constant''...@>=
pub(crate) fn Check_the_constant_values_for_consistency_0553(bad: &mut usize) {
    // if int_packets+17*int_increment>bistack_size then bad:=32;
    if int_packets + 17 * int_increment > bistack_size {
        *bad = 32;
    }
}

use crate::pascal::word;
use crate::section_0011::bistack_size;
