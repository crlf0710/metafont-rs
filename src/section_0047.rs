//! @ The initial values of |str_pool|, |str_start|, |pool_ptr|,
//! and |str_ptr| are computed by the \.{INIMF} program, based in part
//! on the information that \.{WEB} has output while processing \MF.
//! @.INIMF@>
//! @^string pool@>
//
// @p @!init function get_strings_started:boolean; {initializes the string pool,
//   but returns |false| if something goes wrong}
items_init! {
    /// initializes the string pool, but returns `false` if something goes wrong
    pub(crate) fn get_strings_started(_system: &mut MetafontSystem) -> boolean {
        // label done,exit;
        // var @!k,@!l:0..255; {small indices or counters}
        // @!m,@!n:text_char; {characters input from |pool_file|}
        // @!g:str_number; {the string just created}
        // @!a:integer; {accumulator for check sum}
        // @!c:boolean; {check sum has been checked}
        // begin pool_ptr:=0; str_ptr:=0; max_pool_ptr:=0; max_str_ptr:=0; str_start[0]:=0;
        // @<Make the first 256 strings@>;
        // @<Read the other strings from the \.{MF.POOL} file and return |true|,
        //   or give an error message and return |false|@>;
        // exit:end;
        // tini
        todo!();
    }

    use crate::pascal::boolean;
    use crate::section_0004::MetafontSystem;
}

use crate::section_0008::items_init;
