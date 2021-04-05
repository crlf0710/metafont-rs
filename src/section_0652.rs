//! @ Sometimes \MF\ has read too far and wants to ``unscan'' what it has
//! seen. The |back_input| procedure takes care of this by putting the token
//! just scanned back into the input stream, ready to be read again.
//! If |cur_sym<>0|, the values of |cur_cmd| and |cur_mod| are irrelevant.
//
// @p procedure back_input; {undoes one token of input}
impl MetafontInterpreter {
    /// undoes one token of input
    pub(crate) fn back_input(&mut self) {
        // var @!p:pointer; {a token list of length one}
        // begin p:=cur_tok;
        // while token_state and(loc=null) do end_token_list; {conserve stack space}
        // back_list(p);
        // end;
        todo!();
    }
}

use crate::section_0624::MetafontInterpreter;
