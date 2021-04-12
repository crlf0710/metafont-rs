//! @ @<Set init...@>=
//! next(1):=0; text(1):=0; eq_type(1):=tag_token; equiv(1):=null;
//! for k:=2 to hash_end do
//!   begin hash[k]:=hash[1]; eqtb[k]:=eqtb[1];
//!   end;
//!
//! @ @<Initialize table entries...@>=
//! hash_used:=frozen_inaccessible; {nothing is used}
//! st_count:=0;@/
//! text(frozen_bad_vardef):="a bad variable";
//! text(frozen_fi):="fi";
//! text(frozen_end_group):="endgroup";
//! text(frozen_end_def):="enddef";
//! text(frozen_end_for):="endfor";@/
//! text(frozen_semicolon):=";";
//! text(frozen_colon):=":";
//! text(frozen_slash):="/";
//! text(frozen_left_bracket):="[";
//! text(frozen_right_delimiter):=")";@/
//! text(frozen_inaccessible):=" INACCESSIBLE";@/
//! eq_type(frozen_right_delimiter):=right_delimiter;
//!
