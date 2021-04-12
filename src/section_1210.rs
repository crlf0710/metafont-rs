//! ` `
// @<Last-minute...@>=
// @!init procedure init_prim; {initialize all the primitives}
items_init! {
    /// initialize all the primitives
    pub(crate) fn init_prim(_system: &mut MetafontSystem) {
        // begin
        // @<Put each...@>;
        todo!();
        // end;
    }
    // @#
    // procedure init_tab; {initialize other tables}
    /// initialize other tables
    pub(crate) fn init_tab(_system: &mut MetafontSystem) {
        // var @!k:integer; {all-purpose index}
        // begin @<Initialize table entries (done by \.{INIMF} only)@>@;
        todo!();
        // end;
    }
    // tini

    use crate::section_0004::MetafontSystem;
}

use crate::section_0008::items_init;
