//! @* \[30] Introduction to the syntactic routines.
//! Let's pause a moment now and try to look at the Big Picture.
//! The \MF\ program consists of three main parts: syntactic routines,
//! semantic routines, and output routines. The chief purpose of the
//! syntactic routines is to deliver the user's input to the semantic routines,
//! while parsing expressions and locating operators and operands. The
//! semantic routines act as an interpreter responding to these operators,
//! which may be regarded as commands. And the output routines are
//! periodically called on to produce compact font descriptions that can be
//! used for typesetting or for making interim proof drawings. We have
//! discussed the basic data structures and many of the details of semantic
//! operations, so we are good and ready to plunge into the part of \MF\ that
//! actually controls the activities.
//!
//! Our current goal is to come to grips with the |get_next| procedure,
//! which is the keystone of \MF's input mechanism. Each call of |get_next|
//! sets the value of three variables |cur_cmd|, |cur_mod|, and |cur_sym|,
//! representing the next input token.
//! $$\vbox{\halign{#\hfil\cr
//!   \hbox{|cur_cmd| denotes a command code from the long list of codes
//!    given earlier;}\cr
//!   \hbox{|cur_mod| denotes a modifier of the command code;}\cr
//!   \hbox{|cur_sym| is the hash address of the symbolic token that was
//!    just scanned,}\cr
//!   \hbox{\qquad or zero in the case of a numeric or string
//!    or capsule token.}\cr}}$$
//! Underlying this external behavior of |get_next| is all the machinery
//! necessary to convert from character files to tokens. At a given time we
//! may be only partially finished with the reading of several files (for
//! which \&{input} was specified), and partially finished with the expansion
//! of some user-defined macros and/or some macro parameters, and partially
//! finished reading some text that the user has inserted online,
//! and so on. When reading a character file, the characters must be
//! converted to tokens; comments and blank spaces must
//! be removed, numeric and string tokens must be evaluated.
//!
//! To handle these situations, which might all be present simultaneously,
//! \MF\ uses various stacks that hold information about the incomplete
//! activities, and there is a finite state control for each level of the
//! input mechanism. These stacks record the current state of an implicitly
//! recursive process, but the |get_next| procedure is not recursive.

#[globals_struct_field(MetafontSystem)]
pub(crate) static interpreter_system: MetafontInterpreter = MetafontInterpreter::default();

#[globals_struct_use(MetafontSystem)]
use crate::section_0624::MetafontInterpreter;

#[globals_struct]
pub(crate) mod MetafontInterpreter {
    include!("src/section_0624.rs");
    include!("src/section_1077.rs");
}

// @<Glob...@>=
// @!cur_cmd: eight_bits; {current command set by |get_next|}
/// current command set by `get_next`
#[globals_struct_field(MetafontInterpreter)]
pub(crate) static cur_cmd: eight_bits = eight_bits::default();

#[globals_struct_use(MetafontInterpreter)]
use crate::section_0024::eight_bits;
// @!cur_mod: integer; {operand of current command}
/// operand of current command
#[globals_struct_field(MetafontInterpreter)]
pub(crate) static cur_mod: integer = integer::default();

#[globals_struct_use(MetafontInterpreter)]
use crate::pascal::integer;
// @!cur_sym: halfword; {hash address of current symbol}
/// hash address of current symbol
#[globals_struct_field(MetafontInterpreter)]
pub(crate) static cur_sym: hash_pointer = hash_pointer::default();

#[globals_struct_use(MetafontInterpreter)]
use crate::section_0200::hash_pointer;

use globals_struct::{globals_struct, globals_struct_field, globals_struct_use};
