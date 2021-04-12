// @ Certain entries in the hash table are ``frozen'' and not redefinable,
// since they are used in error recovery.
//
// @d hash_top==hash_base+hash_size {the first location of the frozen area}
/// the first location of the frozen area
pub(crate) const hash_top: word = hash_base + hash_size;
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
/// the actual size of the `hash` and `eqtb` arrays
pub(crate) const hash_end: word = hash_top + 12;
//
// @<Glob...@>=
// @!hash: array[1..hash_end] of two_halves; {the hash table}
// @!eqtb: array[1..hash_end] of two_halves; {the equivalents}
//
use crate::pascal::word;
use crate::section_0012::hash_size;
use crate::section_0156::halfword;
use crate::section_0200::hash_base;
