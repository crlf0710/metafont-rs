//! @ \MF\ is occasionally supposed to print diagnostic information that
//! goes only into the transcript file, unless |tracing_online| is positive.
//! Now that we have defined |tracing_online| we can define
//! two routines that adjust the destination of print commands:
//!
//! @<Basic printing...@>=
//! procedure begin_diagnostic; {prepare to do some tracing}
//! begin old_setting:=selector;
//! if(internal[tracing_online]<=0)and(selector=term_and_log) then
//!   begin decr(selector);
//!   if history=spotless then history:=warning_issued;
//!   end;
//! end;
//! @#
//! procedure end_diagnostic(@!blank_line:boolean);
//!   {restore proper conditions after tracing}
//! begin print_nl("");
//! if blank_line then print_ln;
//! selector:=old_setting;
//! end;
//!
//! @ Of course we had better declare a few more global variables, if the previous
//! routines are going to work.
//!
//! @<Glob...@>=
//! @!old_setting:0..max_selector;
//! @!sys_time,@!sys_day,@!sys_month,@!sys_year:integer;
//!     {date and time supplied by external system}
//!
//! @ We will occasionally use |begin_diagnostic| in connection with line-number
//! printing, as follows. (The parameter |s| is typically |"Path"| or
//! |"Cycle spec"|, etc.)
//!
//! @<Basic printing...@>=
//! procedure print_diagnostic(@!s,@!t:str_number;@!nuline:boolean);
//! begin begin_diagnostic;
//! if nuline then print_nl(s)@+else print(s);
//! print(" at line "); print_int(line);
//! print(t); print_char(":");
//! end;
//!
//! @ The 256 |ASCII_code| characters are grouped into classes by means of
//! the |char_class| table. Individual class numbers have no semantic
//! or syntactic significance, except in a few instances defined here.
//! There's also |max_class|, which can be used as a basis for additional
//! class numbers in nonstandard extensions of \MF.
//!
//! @d digit_class=0 {the class number of \.{0123456789}}
//! @d period_class=1 {the class number of `\..'}
//! @d space_class=2 {the class number of spaces and nonstandard characters}
//! @d percent_class=3 {the class number of `\.\%'}
//! @d string_class=4 {the class number of `\."'}
//! @d right_paren_class=8 {the class number of `\.)'}
//! @d isolated_classes==5,6,7,8 {characters that make length-one tokens only}
//! @d letter_class=9 {letters and the underline character}
//! @d left_bracket_class=17 {`\.['}
//! @d right_bracket_class=18 {`\.]'}
//! @d invalid_class=20 {bad character in the input}
//! @d max_class=20 {the largest class number}
//!
//! @<Glob...@>=
//! @!char_class:array[ASCII_code] of 0..max_class; {the class numbers}
//!
//! @ If changes are made to accommodate non-ASCII character sets, they should
//! follow the guidelines in Appendix~C of {\sl The {\logos METAFONT\/}book}.
//! @:METAFONTbook}{\sl The {\logos METAFONT\/}book@>
//! @^system dependencies@>
//!
//! @<Set init...@>=
//! for k:="0" to "9" do char_class[k]:=digit_class;
//! char_class["."]:=period_class;
//! char_class[" "]:=space_class;
//! char_class["%"]:=percent_class;
//! char_class[""""]:=string_class;@/
//! char_class[","]:=5;
//! char_class[";"]:=6;
//! char_class["("]:=7;
//! char_class[")"]:=right_paren_class;
//! for k:="A" to "Z" do char_class[k]:=letter_class;
//! for k:="a" to "z" do char_class[k]:=letter_class;
//! char_class["_"]:=letter_class;@/
//! char_class["<"]:=10;
//! char_class["="]:=10;
//! char_class[">"]:=10;
//! char_class[":"]:=10;
//! char_class["|"]:=10;@/
//! char_class["`"]:=11;
//! char_class["'"]:=11;@/
//! char_class["+"]:=12;
//! char_class["-"]:=12;@/
//! char_class["/"]:=13;
//! char_class["*"]:=13;
//! char_class["\"]:=13;@/
//! char_class["!"]:=14;
//! char_class["?"]:=14;@/
//! char_class["#"]:=15;
//! char_class["&"]:=15;
//! char_class["@@"]:=15;
//! char_class["$"]:=15;@/
//! char_class["^"]:=16;
//! char_class["~"]:=16;@/
//! char_class["["]:=left_bracket_class;
//! char_class["]"]:=right_bracket_class;@/
//! char_class["{"]:=19;
//! char_class["}"]:=19;@/
//! for k:=0 to " "-1 do char_class[k]:=invalid_class;
//! for k:=127 to 255 do char_class[k]:=invalid_class;
//!
