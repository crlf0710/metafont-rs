//! @ The |jump_out| procedure just cuts across all active procedure levels and
//! goes to |end_of_MF|. This is the only nontrivial |@!goto| statement in the
//! whole program. It is used when there is no recovery from a particular error.
//!
//! Some \PASCAL\ compilers do not implement non-local |goto| statements.
//! @^system dependencies@>
//! In such cases the body of |jump_out| should simply be
//! `|close_files_and_terminate|;\thinspace' followed by a call on some system
//! procedure that quietly terminates the program.
//
// @<Error hand...@>=
// procedure jump_out;
pub(crate) fn jump_out() -> MFResult<()> {
    // begin goto end_of_MF;
    return Err(JumpOutToEndOfMF);
    // end;
}

pub(crate) struct JumpOutToEndOfMF;

impl fmt::Display for JumpOutToEndOfMF {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "JumpOutToEndOfMF")
    }
}

pub(crate) type MFResult<T> = Result<T, JumpOutToEndOfMF>;

pub(crate) macro_rules! try_or_jump {
    ($val:expr, $jump_target:lifetime) => {
        match $val {
            Ok(v) => v,
            Err(crate::section_0076::JumpOutToEndOfMF) => goto_forward_label!($jump_target),
        }
    };
}

use core::fmt;

migration_complete!();
