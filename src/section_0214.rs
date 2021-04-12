//! @* \[14] Token lists.
//! A \MF\ token is either symbolic or numeric or a string, or it denotes
//! a macro parameter or capsule; so there are five corresponding ways to encode it
//! @^token@>
//! internally: (1)~A symbolic token whose hash code is~|p|
//! is represented by the number |p|, in the |info| field of a single-word
//! node in~|mem|. (2)~A numeric token whose |scaled| value is~|v| is
//! represented in a two-word node of~|mem|; the |type| field is |known|,
//! the |name_type| field is |token|, and the |value| field holds~|v|.
//! The fact that this token appears in a two-word node rather than a
//! one-word node is, of course, clear from the node address.
//! (3)~A string token is also represented in a two-word node; the |type|
//! field is |string_type|, the |name_type| field is |token|, and the
//! |value| field holds the corresponding |str_number|.  (4)~Capsules have
//! |name_type=capsule|, and their |type| and |value| fields represent
//! arbitrary values (in ways to be explained later).  (5)~Macro parameters
//! are like symbolic tokens in that they appear in |info| fields of
//! one-word nodes. The $k$th parameter is represented by |expr_base+k| if it
//! is of type \&{expr}, or by |suffix_base+k| if it is of type \&{suffix}, or
//! by |text_base+k| if it is of type \&{text}.  (Here |0<=k<param_size|.)
//! Actual values of these parameters are kept in a separate stack, as we will
//! see later.  The constants |expr_base|, |suffix_base|, and |text_base| are,
//! of course, chosen so that there will be no confusion between symbolic
//! tokens and parameters of various types.
//!
//! It turns out that |value(null)=0|, because |null=null_coords|;
//! we will make use of this coincidence later.
//!
//! Incidentally, while we're speaking of coincidences, we might note that
//! the `\\{type}' field of a node has nothing to do with ``type'' in a
//! printer's sense. It's curious that the same word is used in such different ways.

use crate::section_0153::max_halfword;
//
// @d type(#) == mem[#].hh.b0 {identifies what kind of value this is}
// @d name_type(#) == mem[#].hh.b1 {a clue to the name of this value}
// @d token_node_size=2 {the number of words in a large token node}
// @d value_loc(#)==#+1 {the word that contains the |value| field}
// @d value(#)==mem[value_loc(#)].int {the value stored in a large token node}
// @d expr_base==hash_end+1 {code for the zeroth \&{expr} parameter}
/// code for the zeroth `expr` parameter
pub(crate) const expr_base: word = hash_end + 1;
// @d suffix_base==expr_base+param_size {code for the zeroth \&{suffix} parameter}
/// code for the zeroth `suffix` parameter
pub(crate) const suffix_base: word = expr_base + param_size;
// @d text_base==suffix_base+param_size {code for the zeroth \&{text} parameter}
/// code for the zeroth `text` parameter
pub(crate) const text_base: word = suffix_base + param_size;
//
// @<Check the ``constant''...@>=
pub(crate) fn Check_the_constant_values_for_consistency_0214(bad: &mut usize) {
    // if text_base+param_size>max_halfword then bad:=22;
    if text_base.lift_to_word() + param_size > max_halfword {
        *bad = 22;
    }
}

use crate::pascal::word;
use crate::pascal::LiftToWord;
use crate::section_0012::param_size;
use crate::section_0201::hash_end;
