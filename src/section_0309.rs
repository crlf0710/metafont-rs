//! @ When bisection occurs, we ``push'' the subproblem corresponding
//! to the right-hand subinterval onto the |bisect_stack| while
//! we continue to work on the left-hand subinterval. Thus, the |bisect_stack|
//! will hold $(X_1,X_2,X_3,R,m,Y_1,Y_2,Y_3,S,n,l)$ values for
//! subproblems yet to be tackled.
//!
//! At most 15 subproblems will be on the stack at once (namely, for
//! $l=15$,~16, \dots,~29); but the stack is bigger than this, because
//! it is used also for more complicated bisection algorithms.
//
// @d stack_x1==bisect_stack[bisect_ptr] {stacked value of $X_1$}
// @d stack_x2==bisect_stack[bisect_ptr+1] {stacked value of $X_2$}
// @d stack_x3==bisect_stack[bisect_ptr+2] {stacked value of $X_3$}
// @d stack_r==bisect_stack[bisect_ptr+3] {stacked value of $R$}
// @d stack_m==bisect_stack[bisect_ptr+4] {stacked value of $m$}
// @d stack_y1==bisect_stack[bisect_ptr+5] {stacked value of $Y_1$}
// @d stack_y2==bisect_stack[bisect_ptr+6] {stacked value of $Y_2$}
// @d stack_y3==bisect_stack[bisect_ptr+7] {stacked value of $Y_3$}
// @d stack_s==bisect_stack[bisect_ptr+8] {stacked value of $S$}
// @d stack_n==bisect_stack[bisect_ptr+9] {stacked value of $n$}
// @d stack_l==bisect_stack[bisect_ptr+10] {stacked value of $l$}
// @d move_increment=11 {number of items pushed by |make_moves|}
/// number of items pushed by `make_moves`
pub(crate) const move_increment: word = 11;

// @<Glob...@>=
// @!bisect_stack:array[0..bistack_size] of integer;
// @!bisect_ptr:0..bistack_size;
//
use crate::pascal::word;