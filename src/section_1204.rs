//! @ Now this is really it: \MF\ starts and ends here.
//!
//! The initial test involving |ready_already| should be deleted if the
//! \PASCAL\ runtime system is smart enough to detect such a ``mistake.''
//! @^system dependencies@>

impl MetafontSystem {
    /// Main entry to METAFONT
    pub fn entry(&mut self) {
        let system = &mut *self;
        // @p begin @!{|start_here|}
        /// `start_here`
        region_forward_label! {|'final_end|{
        region_forward_label! {|'end_of_MF|{
        region_forward_label! {|'start_of_MF|{
        // history:=fatal_error_stop; {in case we quit during initialization}
        /// in case we quit during initialization
        assign!(system.interactive_system.history = history_kind::fatal_error_stop);
        // t_open_out; {open the terminal for output}
        /// open the terminal for output
        t_open_out(system.interactive_system.io_view());
        // if ready_already=314159 then goto start_of_MF;
        if system.ready_already == 314159 {
            goto_forward_label!('start_of_MF);
        }
        // @<Check the ``constant'' values...@>@;
        let bad = Check_the_constant_values_for_consistency(system);
        // if bad>0 then
        if let Err(bad) = bad {
            // begin wterm_ln('Ouch---my internal constants have been clobbered!',
            //   '---case ',bad:1);
            wterm_ln(system.interactive_system.io_view(), format!("{}{}{:1}","Ouch---my internal constants have been clobbered!",
                "---case ", bad));
            // @.Ouch...clobbered@>
            // goto final_end;
            goto_forward_label!('final_end);
            // end;
        }
        // initialize; {set global variables to their starting values}
        /// set global variables to their starting values
        initialize(system);
        // @!init if not get_strings_started then goto final_end;
        region_init! {
            if !get_strings_started(system) {
                goto_forward_label!('final_end);
            }
            // init_tab; {initialize the tables}
            /// initialize the tables
            init_tab(system);
            // init_prim; {call |primitive| for each primitive}
            /// call `primitive` for each primitive
            init_prim(system);
            // init_str_ptr:=str_ptr; init_pool_ptr:=pool_ptr;@/
            system.string_pool.init_str_ptr = system.string_pool.str_ptr;
            system.string_pool.init_pool_ptr = system.string_pool.pool_ptr;
            // max_str_ptr:=str_ptr; max_pool_ptr:=pool_ptr; fix_date_and_time;
            system.string_pool.max_str_ptr = system.string_pool.str_ptr;
            system.string_pool.max_pool_ptr = system.string_pool.pool_ptr;
            fix_date_and_time(system);
            // tini@/
        }
        // ready_already:=314159;
        system.ready_already = 314159;
        }
        // start_of_MF: @<Initialize the output routines@>;
        'start_of_MF <-
        };
        Initialize_the_output_routines(system);
        // @<Get the first line of input and prepare to start@>;
        Get_the_first_line_of_input_and_prepare_to_start!(system, 'end_of_MF, 'final_end);
        // history:=spotless; {ready to go!}
        /// ready to go!
        assign! { system.interactive_system.history = history_kind::spotless };
        // if start_sym>0 then {insert the `\&{everyjob}' symbol}
        if !system.interpreter_system.start_sym.is_null() {
            /// insert the `\everyjob` symbol
            eliminated_text!();
            // begin cur_sym:=start_sym; back_input;
            system.interpreter_system.cur_sym = system.interpreter_system.start_sym;
            system.interpreter_system.back_input();
            // end;
        }
        // main_control; {come to life}
        /// come to life
        try_or_jump!(system.main_control(), 'end_of_MF);
        // final_cleanup; {prepare for death}
        /// prepare for death
        try_or_jump!(system.final_cleanup(), 'end_of_MF);
        }
        // end_of_MF: close_files_and_terminate;
        'end_of_MF <-
        };
        system.close_files_and_terminate();
        }
        // final_end: ready_already:=0;
        'final_end <-
        };
        system.ready_already = 0;
        // end.
    }
}

#[allow(non_snake_case)]
fn Initialize_the_output_routines(_system: &mut MetafontSystem) {
    todo!();
}

#[allow(non_snake_case)]
fn Check_the_constant_values_for_consistency(_system: &mut MetafontSystem) -> Result<(), usize> {
    let mut bad = 0;
    crate::section_0014::Check_the_constant_values_for_consistency_0014(&mut bad);
    crate::section_0154::Check_the_constant_values_for_consistency_0154(&mut bad);
    crate::section_0204::Check_the_constant_values_for_consistency_0204(&mut bad);
    crate::section_0214::Check_the_constant_values_for_consistency_0214(&mut bad);
    crate::section_0310::Check_the_constant_values_for_consistency_0310(&mut bad);
    crate::section_0553::Check_the_constant_values_for_consistency_0553(&mut bad);
    crate::section_0777::Check_the_constant_values_for_consistency_0777(&mut bad);
    if bad != 0 {
        return Err(bad);
    }
    Ok(())
}

use crate::section_0004::initialize;
use crate::section_0004::MetafontSystem;
use crate::section_0008::{region_init, items_init};
use crate::section_0032::t_open_out;
use crate::section_0056::wterm_ln;
use crate::section_0071::history_kind;
use crate::section_0076::try_or_jump;
use crate::section_0194::fix_date_and_time;
use crate::section_1211::Get_the_first_line_of_input_and_prepare_to_start;
items_init! {
    use crate::section_0047::get_strings_started;
    use crate::section_1210::init_tab;
    use crate::section_1210::init_prim;
}
