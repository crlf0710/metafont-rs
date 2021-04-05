//! @ A global variable |deletions_allowed| is set |false| if the |get_next|
//! routine is active when |error| is called; this ensures that |get_next|
//! will never be called recursively.
//! @^recursion@>
//!
//! The global variable |history| records the worst level of error that
//! has been detected. It has four possible values: |spotless|, |warning_issued|,
//! |error_message_issued|, and |fatal_error_stop|.
//!
//! Another global variable, |error_count|, is increased by one when an
//! |error| occurs without an interactive dialog, and it is reset to zero at
//! the end of every statement.  If |error_count| reaches 100, \MF\ decides
//! that there is no point in continuing further.
//
// @d spotless=0 {|history| value when nothing has been amiss yet}
// @d warning_issued=1 {|history| value when |begin_diagnostic| has been called}
// @d error_message_issued=2 {|history| value when |error| has been called}
// @d fatal_error_stop=3 {|history| value when termination was premature}
#[derive(Clone, Copy, PartialEq, PartialOrd)]
pub(crate) enum history_kind {
    /// `history` value when nothing has been amiss yet
    spotless = 0,
    /// `history` value when `begin_diagnostic` has been called
    warning_issued = 1,
    /// `history` value when `error` has been called
    error_message_issued = 2,
    /// `history` value when termination was premature
    fatal_error_stop = 3,
}

// @<Glob...@>=
// @!deletions_allowed:boolean; {is it safe for |error| to call |get_next|?}
/// is it safe for `error` to call `get_next`?
#[globals_struct_field(MetafontInteractive)]
pub(crate) static deletions_allowed: boolean = true;

#[globals_struct_use(MetafontInteractive)]
use crate::pascal::boolean;

// @!history:spotless..fatal_error_stop; {has the source input been clean so far?}
/// has the source input been clean so far?
#[globals_struct_field(MetafontInteractive)]
pub(crate) static history: history_kind = history_kind::spotless;

#[globals_struct_use(MetafontInteractive)]
use crate::section_0071::history_kind;

// @!error_count:-1..100; {the number of scrolled errors since the
//   last statement ended}
/// the number of scrolled errors since the last statement ended
#[globals_struct_field(MetafontInteractive)]
pub(crate) static error_count: i8_from_m_to_n<-1, 100> = i8_from_m_to_n::default();

#[globals_struct_use(MetafontInteractive)]
use crate::pascal::i8_from_m_to_n;

use globals_struct::{globals_struct_field, globals_struct_use};
