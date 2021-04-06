//! @ We need a special routine to read the first line of \MF\ input from
//! the user's terminal. This line is different because it is read before we
//! have opened the transcript file; there is sort of a ``chicken and
//! egg'' problem here. If the user types `\.{input cmr10}' on the first
//! line, or if some macro invoked by that line does such an \.{input},
//! the transcript file will be named `\.{cmr10.log}'; but if no \.{input}
//! commands are performed during the first line of terminal input, the transcript
//! file will acquire its default name `\.{mfput.log}'. (The transcript file
//! will not contain error messages generated by the first line before the
//! first \.{input} command.)
//! @.mfput@>
//!
//! The first line is even more special if we are lucky enough to have an operating
//! system that treats \MF\ differently from a run-of-the-mill \PASCAL\ object
//! program. It's nice to let the user start running a \MF\ job by typing
//! a command line like `\.{MF cmr10}'; in such a case, \MF\ will operate
//! as if the first line of input were `\.{cmr10}', i.e., the first line will
//! consist of the remainder of the command line, after the part that invoked \MF.
//!
//! The first line is special also because it may be read before \MF\ has
//! input a base file. In such cases, normal error messages cannot yet
//! be given. The following code uses concepts that will be explained later.
//! (If the \PASCAL\ compiler does not support non-local |@!goto|\unskip, the
//! @^system dependencies@>
//! statement `|goto final_end|' should be replaced by something that
//! quietly terminates the program.)
//!
//! @<Report overflow of the input buffer, and abort@>=
//! if base_ident=0 then
//!   begin write_ln(term_out,'Buffer size exceeded!'); goto final_end;
//! @.Buffer size exceeded@>
//!   end
//! else begin cur_input.loc_field:=first; cur_input.limit_field:=last-1;
//!   overflow("buffer size",buf_size);
//! @:METAFONT capacity exceeded buffer size}{\quad buffer size@>
//!   end
//!
//! @ Different systems have different ways to get started. But regardless of
//! what conventions are adopted, the routine that initializes the terminal
//! should satisfy the following specifications:
//!
//! \yskip\textindent{1)}It should open file |term_in| for input from the
//!   terminal. (The file |term_out| will already be open for output to the
//!   terminal.)
//!
//! \textindent{2)}If the user has given a command line, this line should be
//!   considered the first line of terminal input. Otherwise the
//!   user should be prompted with `\.{**}', and the first line of input
//!   should be whatever is typed in response.
//!
//! \textindent{3)}The first line of input, which might or might not be a
//!   command line, should appear in locations |first| to |last-1| of the
//!   |buffer| array.
//!
//! \textindent{4)}The global variable |loc| should be set so that the
//!   character to be read next by \MF\ is in |buffer[loc]|. This
//!   character should not be blank, and we should have |loc<last|.
//!
//! \yskip\noindent(It may be necessary to prompt the user several times
//! before a non-blank line comes in. The prompt is `\.{**}' instead of the
//! later `\.*' because the meaning is slightly different: `\.{input}' need
//! not be typed immediately after~`\.{**}'.)
//!
//! @d loc==cur_input.loc_field {location of first unread character in |buffer|}
//!
//! @ The following program does the required initialization
//! without retrieving a possible command line.
//! It should be clear how to modify this routine to deal with command lines,
//! if the system permits them.
//! @^system dependencies@>
//!
//! @p function init_terminal:boolean; {gets the terminal input started}
//! label exit;
//! begin t_open_in;
//! loop@+begin wake_up_terminal; write(term_out,'**'); update_terminal;
//! @.**@>
//!   if not input_ln(term_in,true) then {this shouldn't happen}
//!     begin write_ln(term_out);
//!     write(term_out,'! End of file on the terminal... why?');
//! @.End of file on the terminal@>
//!     init_terminal:=false; return;
//!     end;
//!   loc:=first;
//!   while (loc<last)and(buffer[loc]=" ") do incr(loc);
//!   if loc<last then
//!     begin init_terminal:=true;
//!     return; {return unless the line was all blank}
//!     end;
//!   write_ln(term_out,'Please type the name of your input file.');
//!   end;
//! exit:end;
//!
