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
pub(crate) const hash_base: word = 257;
// @d hash_is_full == (hash_used=hash_base) {are all positions occupied?}
//
// @<Glob...@>=
// @!hash_used:pointer; {allocation pointer for |hash|}
// @!st_count:integer; {total number of known identifiers}
//

use crate::pascal::word;
use crate::section_0156::halfword;
