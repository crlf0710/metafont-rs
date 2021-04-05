//! @* \[13] The hash table.
//! Symbolic tokens are stored and retrieved by means of a fairly standard hash
//! table algorithm called the method of ``coalescing lists'' (cf.\ Algorithm 6.4C
//! in {\sl The Art of Computer Programming\/}). Once a symbolic token enters the
//! table, it is never removed.
//!
//! The actual sequence of characters forming a symbolic token is
//! stored in the |str_pool| array together with all the other strings. An
//! auxiliary array |hash| consists of items with two halfword fields per
//! word. The first of these, called |next(p)|, points to the next identifier
//! belonging to the same coalesced list as the identifier corresponding to~|p|;
//! and the other, called |text(p)|, points to the |str_start| entry for
//! |p|'s identifier. If position~|p| of the hash table is empty, we have
//! |text(p)=0|; if position |p| is either empty or the end of a coalesced
//! hash list, we have |next(p)=0|.
//!
//! An auxiliary pointer variable called |hash_used| is maintained in such a
//! way that all locations |p>=hash_used| are nonempty. The global variable
//! |st_count| tells how many symbolic tokens have been defined, if statistics
//! are being kept.
//!
//! The first 256 locations of |hash| are reserved for symbols of length one.
//!
//! There's a parallel array called |eqtb| that contains the current equivalent
//! values of each symbolic token. The entries of this array consist of
//! two halfwords called |eq_type| (a command code) and |equiv| (a secondary
//! piece of information that qualifies the |eq_type|).

#[derive(Clone, Copy, Default)]
pub(crate) struct hash_pointer(halfword);

impl hash_pointer {
    pub(crate) const fn is_null(self) -> bool {
        self.0 == 0
    }
}

// @d next(#) == hash[#].lh {link for coalesced lists}
// @d text(#) == hash[#].rh {string number for symbolic token name}
// @d eq_type(#) == eqtb[#].lh {the current ``meaning'' of a symbolic token}
// @d equiv(#) == eqtb[#].rh {parametric part of a token's meaning}
// @d hash_base=257 {hashing actually starts here}
// @d hash_is_full == (hash_used=hash_base) {are all positions occupied?}
//
// @<Glob...@>=
// @!hash_used:pointer; {allocation pointer for |hash|}
// @!st_count:integer; {total number of known identifiers}
//
// @ Certain entries in the hash table are ``frozen'' and not redefinable,
// since they are used in error recovery.
//
// @d hash_top==hash_base+hash_size {the first location of the frozen area}
// @d frozen_inaccessible==hash_top {|hash| location to protect the frozen area}
// @d frozen_repeat_loop==hash_top+1 {|hash| location of a loop-repeat token}
// @d frozen_right_delimiter==hash_top+2 {|hash| location of a permanent `\.)'}
// @d frozen_left_bracket==hash_top+3 {|hash| location of a permanent `\.['}
// @d frozen_slash==hash_top+4 {|hash| location of a permanent `\./'}
// @d frozen_colon==hash_top+5 {|hash| location of a permanent `\.:'}
// @d frozen_semicolon==hash_top+6 {|hash| location of a permanent `\.;'}
// @d frozen_end_for==hash_top+7 {|hash| location of a permanent \&{endfor}}
// @d frozen_end_def==hash_top+8 {|hash| location of a permanent \&{enddef}}
// @d frozen_fi==hash_top+9 {|hash| location of a permanent \&{fi}}
// @d frozen_end_group==hash_top+10
//   {|hash| location of a permanent `\.{endgroup}'}
// @d frozen_bad_vardef==hash_top+11 {|hash| location of `\.{a bad variable}'}
// @d frozen_undefined==hash_top+12 {|hash| location that never gets defined}
// @d hash_end==hash_top+12 {the actual size of the |hash| and |eqtb| arrays}
//
// @<Glob...@>=
// @!hash: array[1..hash_end] of two_halves; {the hash table}
// @!eqtb: array[1..hash_end] of two_halves; {the equivalents}
//
use crate::section_0156::halfword;