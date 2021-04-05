#![allow(missing_docs)]
//! @ The program begins with a normal \PASCAL\ program heading, whose
//! components will be filled in later, using the conventions of \.{WEB}.
//! @.WEB@>
//! For example, the portion of the program called `\X\glob:Global
//! variables\X' below will be replaced by a sequence of variable declarations
//! that starts in $\section\glob$ of this documentation. In this way, we are able
//! to define each individual global variable when we are prepared to
//! understand what it means; we do not have to define all of the globals at
//! once.  Cross references in $\section\glob$, where it says ``See also
//! sections \gglob, \dots,'' also make it possible to look at the set of
//! all global variables, if desired.  Similar remarks apply to the other
//! portions of the program heading.
//!
//! Actually the heading shown here is not quite normal: The |program| line
//! does not mention any |output| file, because \ph\ would ask the \MF\ user
//! to specify a file name if |output| were specified here.
//! @:PASCAL H}{\ph@>
//! @^system dependencies@>
//
// @d mtype==t@&y@&p@&e {this is a \.{WEB} coding trick:}
// @f mtype==type {`\&{mtype}' will be equivalent to `\&{type}'}
// @f type==true {but `|type|' will not be treated as a reserved word}
comment_text!();

// @p @t\4@>@<Compiler directives@>@/
comment_text!();
// program MF; {all file names are defined dynamically}
comment_text!();
// label @<Labels in the outer block@>@/
comment_text!();
// const @<Constants in the outer block@>@/
comment_text!();
// mtype @<Types in the outer block@>@/
comment_text!();
// var @<Global variables@>@/
#[globals_struct]
pub mod MetafontSystem {
    include!("src/section_0031.rs");
    include!("src/section_0624.rs");
    include!("src/section_1203.rs");
}

impl_debug_with_literal!(MetafontSystem, "MetafontSystem");

// @#
comment_text!();

// procedure initialize; {this procedure gets things started properly}
/// this procedure gets things started properly
pub(crate) fn initialize(_globals: &mut MetafontSystem) {
    // var @<Local variables for initialization@>@/
    comment_text!();
    // begin @<Set initial values of key variables@>@/
    // end;@#
}
// @t\4@>@<Basic printing procedures@>@/
comment_text!();
// @t\4@>@<Error handling procedures@>@/
comment_text!();

use globals_struct::globals_struct;
