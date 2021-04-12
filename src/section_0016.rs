//! @ Here are some macros for common programming idioms.
//
// @d incr(#) == #:=#+1 {increase a variable by unity}
/// increase a variable by unity
pub(crate) macro_rules! incr {
    ($v:expr) => {
        $v += 1
    }
}
// @d decr(#) == #:=#-1 {decrease a variable by unity}
/// decrease a variable by unity
pub(crate) macro_rules! decr {
    ($v:expr) => {
        $v -= 1
    }
}
// @d negate(#) == #:=-# {change the sign of a variable}
/// change the sign of a variable
pub(crate) macro_rules! negate {
    ($v:expr) => {
        $v = -$v
    }
}
// @d double(#) == #:=#+# {multiply a variable by two}
/// multiply a variable by two
pub(crate) macro_rules! double {
    ($v:expr) => {
        $v += $v
    }
}
// @d loop == @+ while true do@+ {repeat over and over until a |goto| happens}
eliminated_text!();
// @f loop == xclause
//   {\.{WEB}'s |xclause| acts like `\ignorespaces|while true do|\unskip'}
eliminated_text!();
// @d do_nothing == {empty statement}
pub(crate) macro_rules! do_nothing {
    () => {};
}
// @d return == goto exit {terminate a procedure call}
eliminated_text!();
// @f return == nil {\.{WEB} will henceforth say |return| instead of \\{return}}
eliminated_text!();
