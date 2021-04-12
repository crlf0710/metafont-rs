//! @ Like the preceding parameters, the following quantities can be changed
//! at compile time to extend or reduce \MF's capacity. But if they are changed,
//! it is necessary to rerun the initialization program \.{INIMF}
//! @.INIMF@>
//! to generate new tables for the production \MF\ program.
//! One can't simply make helter-skelter changes to the following constants,
//! since certain rather complex initialization
//! numbers are computed from them. They are defined here using
//! \.{WEB} macros, instead of being put into \PASCAL's |const| list, in order to
//! emphasize this distinction.
//
// @d mem_min=0 {smallest index in the |mem| array, must not be less
//   than |min_halfword|}
/// smallest index in the `mem` array, must not be less than `min_halfword`
pub(crate) const mem_min: word = 0;
// @d mem_top==30000 {largest index in the |mem| array dumped by \.{INIMF};
//   must be substantially larger than |mem_min|
//   and not greater than |mem_max|}
/// largest index in the `mem` array dumped by `INIMF`; must be substantially larger than `mem_min` and not greater than `mem_max`
pub(crate) const mem_top: word = 30000;
// @d hash_size=2100 {maximum number of symbolic tokens,
//   must be less than |max_halfword-3*param_size|}
/// maximum number of symbolic tokens, must be less than `max_halfword-3*param_size`
pub(crate) const hash_size: word = 2100;
// @d hash_prime=1777 {a prime number equal to about 85\pct! of |hash_size|}
/// a prime number equal to about 85% of `hash_size`
pub(crate) const hash_prime: word = 1777;
// @d max_in_open=6 {maximum number of input files and error insertions that
//   can be going on simultaneously}
// @d param_size=150 {maximum number of simultaneous macro parameters}
pub(crate) const param_size: word = 150;
// @^system dependencies@>

use crate::pascal::word;
