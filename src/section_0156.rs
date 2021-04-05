//! @ The reader should study the following definitions closely:
//! @^system dependencies@>
//
// @d sc==int {|scaled| data is equivalent to |integer|}
//
// @<Types...@>=
// @!quarterword = min_quarterword..max_quarterword; {1/4 of a word}
/// 1/4 of a word
pub(crate) type quarterword = u8;
// @!halfword=min_halfword..max_halfword; {1/2 of a word}
/// 1/2 of a word
pub(crate) type halfword = u16;
// @!two_choices = 1..2; {used when there are two variants in a record}
// @!three_choices = 1..3; {used when there are three variants in a record}
// @!two_halves = packed record@;@/
//   @!rh:halfword;
//   case two_choices of
//   1: (@!lh:halfword);
//   2: (@!b0:quarterword; @!b1:quarterword);
//   end;
// @!four_quarters = packed record@;@/
//   @!b0:quarterword;
//   @!b1:quarterword;
//   @!b2:quarterword;
//   @!b3:quarterword;
//   end;
// @!memory_word = record@;@/
//   case three_choices of
//   1: (@!int:integer);
//   2: (@!hh:two_halves);
//   3: (@!qqqq:four_quarters);
//   end;
// @!word_file = file of memory_word;
//
