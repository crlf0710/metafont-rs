//! @ Most of what we need to do with respect to input and output can be handled
//! by the I/O facilities that are standard in \PASCAL, i.e., the routines
//! called |get|, |put|, |eof|, and so on. But
//! standard \PASCAL\ does not allow file variables to be associated with file
//! names that are determined at run time, so it cannot be used to implement
//! \MF; some sort of extension to \PASCAL's ordinary |reset| and |rewrite|
//! is crucial for our purposes. We shall assume that |name_of_file| is a variable
//! of an appropriate type such that the \PASCAL\ run-time system being used to
//! implement \MF\ can open a file whose external name is specified by
//! |name_of_file|.
//! @^system dependencies@>
//!
//! @<Glob...@>=
//! @!name_of_file:packed array[1..file_name_size] of char;@;@/
//!   {on some systems this may be a \&{record} variable}
//! @!name_length:0..file_name_size;@/{this many characters are actually
//!   relevant in |name_of_file| (the rest are blank)}
//!
//! @ The \ph\ compiler with which the present version of \MF\ was prepared has
//! extended the rules of \PASCAL\ in a very convenient way. To open file~|f|,
//! we can write
//! $$\vbox{\halign{#\hfil\qquad&#\hfil\cr
//! |reset(f,@t\\{name}@>,'/O')|&for input;\cr
//! |rewrite(f,@t\\{name}@>,'/O')|&for output.\cr}}$$
//! The `\\{name}' parameter, which is of type `\ignorespaces|packed
//! array[@t\<\\{any}>@>] of text_char|', stands for the name of
//! the external file that is being opened for input or output.
//! Blank spaces that might appear in \\{name} are ignored.
//!
//! The `\.{/O}' parameter tells the operating system not to issue its own
//! error messages if something goes wrong. If a file of the specified name
//! cannot be found, or if such a file cannot be opened for some other reason
//! (e.g., someone may already be trying to write the same file), we will have
//! |@!erstat(f)<>0| after an unsuccessful |reset| or |rewrite|.  This allows
//! \MF\ to undertake appropriate corrective action.
//! @:PASCAL H}{\ph@>
//! @^system dependencies@>
//!
//! \MF's file-opening procedures return |false| if no file identified by
//! |name_of_file| could be opened.
//!
//! @d reset_OK(#)==erstat(#)=0
//! @d rewrite_OK(#)==erstat(#)=0
//!
//! @p function a_open_in(var @!f:alpha_file):boolean;
//!   {open a text file for input}
//! begin reset(f,name_of_file,'/O'); a_open_in:=reset_OK(f);
//! end;
//! @#
//! function a_open_out(var @!f:alpha_file):boolean;
//!   {open a text file for output}
//! begin rewrite(f,name_of_file,'/O'); a_open_out:=rewrite_OK(f);
//! end;
//! @#
//! function b_open_out(var @!f:byte_file):boolean;
//!   {open a binary file for output}
//! begin rewrite(f,name_of_file,'/O'); b_open_out:=rewrite_OK(f);
//! end;
//! @#
//! function w_open_in(var @!f:word_file):boolean;
//!   {open a word file for input}
//! begin reset(f,name_of_file,'/O'); w_open_in:=reset_OK(f);
//! end;
//! @#
//! function w_open_out(var @!f:word_file):boolean;
//!   {open a word file for output}
//! begin rewrite(f,name_of_file,'/O'); w_open_out:=rewrite_OK(f);
//! end;
//!
//! @ Files can be closed with the \ph\ routine `|close(f)|', which
//! @:PASCAL H}{\ph@>
//! @^system dependencies@>
//! should be used when all input or output with respect to |f| has been completed.
//! This makes |f| available to be opened again, if desired; and if |f| was used for
//! output, the |close| operation makes the corresponding external file appear
//! on the user's area, ready to be read.
//!
//! @p procedure a_close(var @!f:alpha_file); {close a text file}
//! begin close(f);
//! end;
//! @#
//! procedure b_close(var @!f:byte_file); {close a binary file}
//! begin close(f);
//! end;
//! @#
//! procedure w_close(var @!f:word_file); {close a word file}
//! begin close(f);
//! end;
//!
//! @ Binary input and output are done with \PASCAL's ordinary |get| and |put|
//! procedures, so we don't have to make any other special arrangements for
//! binary~I/O. Text output is also easy to do with standard \PASCAL\ routines.
//! The treatment of text input is more difficult, however, because
//! of the necessary translation to |ASCII_code| values.
//! \MF's conventions should be efficient, and they should
//! blend nicely with the user's operating environment.
//!
//! @ Input from text files is read one line at a time, using a routine called
//! |input_ln|. This function is defined in terms of global variables called
//! |buffer|, |first|, and |last| that will be described in detail later; for
//! now, it suffices for us to know that |buffer| is an array of |ASCII_code|
//! values, and that |first| and |last| are indices into this array
//! representing the beginning and ending of a line of text.
//!
//! @<Glob...@>=
//! @!buffer:array[0..buf_size] of ASCII_code; {lines of characters being read}
//! @!first:0..buf_size; {the first unused position in |buffer|}
//! @!last:0..buf_size; {end of the line just input to |buffer|}
//! @!max_buf_stack:0..buf_size; {largest index used in |buffer|}
//!
//! @ The |input_ln| function brings the next line of input from the specified
//! file into available positions of the buffer array and returns the value
//! |true|, unless the file has already been entirely read, in which case it
//! returns |false| and sets |last:=first|.  In general, the |ASCII_code|
//! numbers that represent the next line of the file are input into
//! |buffer[first]|, |buffer[first+1]|, \dots, |buffer[last-1]|; and the
//! global variable |last| is set equal to |first| plus the length of the
//! line. Trailing blanks are removed from the line; thus, either |last=first|
//! (in which case the line was entirely blank) or |buffer[last-1]<>" "|.
//! @^inner loop@>
//!
//! An overflow error is given, however, if the normal actions of |input_ln|
//! would make |last>=buf_size|; this is done so that other parts of \MF\
//! can safely look at the contents of |buffer[last+1]| without overstepping
//! the bounds of the |buffer| array. Upon entry to |input_ln|, the condition
//! |first<buf_size| will always hold, so that there is always room for an
//! ``empty'' line.
//!
//! The variable |max_buf_stack|, which is used to keep track of how large
//! the |buf_size| parameter must be to accommodate the present job, is
//! also kept up to date by |input_ln|.
//!
//! If the |bypass_eoln| parameter is |true|, |input_ln| will do a |get|
//! before looking at the first character of the line; this skips over
//! an |eoln| that was in |f^|. The procedure does not do a |get| when it
//! reaches the end of the line; therefore it can be used to acquire input
//! from the user's terminal as well as from ordinary text files.
//!
//! Standard \PASCAL\ says that a file should have |eoln| immediately
//! before |eof|, but \MF\ needs only a weaker restriction: If |eof|
//! occurs in the middle of a line, the system function |eoln| should return
//! a |true| result (even though |f^| will be undefined).
//!
//! @p function input_ln(var @!f:alpha_file;@!bypass_eoln:boolean):boolean;
//!   {inputs the next line or returns |false|}
//! var @!last_nonblank:0..buf_size; {|last| with trailing blanks removed}
//! begin if bypass_eoln then if not eof(f) then get(f);
//!   {input the first character of the line into |f^|}
//! last:=first; {cf.\ Matthew 19\thinspace:\thinspace30}
//! if eof(f) then input_ln:=false
//! else  begin last_nonblank:=first;
//!   while not eoln(f) do
//!     begin if last>=max_buf_stack then
//!       begin max_buf_stack:=last+1;
//!       if max_buf_stack=buf_size then
//!         @<Report overflow of the input buffer, and abort@>;
//!       end;
//!     buffer[last]:=xord[f^]; get(f); incr(last);
//!     if buffer[last-1]<>" " then last_nonblank:=last;
//!     end;
//!   last:=last_nonblank; input_ln:=true;
//!   end;
//! end;
//!
