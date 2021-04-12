//! @ The following procedure, which is called just before \MF\ initializes its
//! input and output, establishes the initial values of the date and time.
//! @^system dependencies@>
//! Since standard \PASCAL\ cannot provide such information, something special
//! is needed. The program here simply assumes that suitable values appear in
//! the global variables \\{sys\_time}, \\{sys\_day}, \\{sys\_month}, and
//! \\{sys\_year} (which are initialized to noon on 4 July 1776,
//! in case the implementor is careless).
//!
//! Note that the values are |scaled| integers. Hence \MF\ can no longer
//! be used after the year 32767.
//
// @p procedure fix_date_and_time;
pub(crate) fn fix_date_and_time(_system: &mut MetafontSystem) {
    // begin sys_time:=12*60;
    // sys_day:=4; sys_month:=7; sys_year:=1776;  {self-evident truths}
    // internal[time]:=sys_time*unity; {minutes since midnight}
    // internal[day]:=sys_day*unity; {day of the month}
    // internal[month]:=sys_month*unity; {month of the year}
    // internal[year]:=sys_year*unity; {Anno Domini}
    // end;
    todo!();
}

use crate::section_0004::MetafontSystem;
