//! @ \MF's |main_control| procedure just calls |do_statement| repeatedly
//! until coming to the end of the user's program.
//! Each execution of |do_statement| concludes with
//! |cur_cmd=semicolon|, |end_group|, or |stop|.
//
impl MetafontSystem {
    // @p procedure main_control;
    pub(crate) fn main_control(&mut self) -> MFResult<()> {
        // begin repeat do_statement;
        // if cur_cmd=end_group then
        //   begin print_err("Extra `endgroup'");
        // @.Extra `endgroup'@>
        //   help2("I'm not currently working on a `begingroup',")@/
        //     ("so I had better not try to end anything.");
        //   flush_error(0);
        //   end;
        // until cur_cmd=stop;
        // end;
        todo!();
    }
}

use crate::section_0004::MetafontSystem;
use crate::section_0076::MFResult;
