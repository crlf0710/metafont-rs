//! @ The operation of subtracting |min_halfword| occurs rather frequently in
//! \MF, so it is convenient to abbreviate this operation by using the macro
//! |ho| defined here.  \MF\ will run faster with respect to compilers that
//! don't optimize the expression `|x-0|', if this macro is simplified in the
//! obvious way when |min_halfword=0|. Similarly, |qi| and |qo| are used for
//! input to and output from quarterwords.
//! @^system dependencies@>
//!
//! @d ho(#)==#-min_halfword
//!   {to take a sixteen-bit item from a halfword}
//! @d qo(#)==#-min_quarterword {to read eight bits from a quarterword}
//! @d qi(#)==#+min_quarterword {to store eight bits in a quarterword}
//!
