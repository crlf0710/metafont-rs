//! @* \[4] String handling.
//! Symbolic token names and diagnostic messages are variable-length strings
//! of eight-bit characters. Since \PASCAL\ does not have a well-developed string
//! mechanism, \MF\ does all of its string processing by homegrown methods.
//!
//! Elaborate facilities for dynamic strings are not needed, so all of the
//! necessary operations can be handled with a simple data structure.
//! The array |str_pool| contains all of the (eight-bit) ASCII codes in all
//! of the strings, and the array |str_start| contains indices of the starting
//! points of each string. Strings are referred to by integer numbers, so that
//! string number |s| comprises the characters |str_pool[j]| for
//! |str_start[s]<=j<str_start[s+1]|. Additional integer variables
//! |pool_ptr| and |str_ptr| indicate the number of entries used so far
//! in |str_pool| and |str_start|, respectively; locations
//! |str_pool[pool_ptr]| and |str_start[str_ptr]| are
//! ready for the next string to be allocated.
//!
//! String numbers 0 to 255 are reserved for strings that correspond to single
//! ASCII characters. This is in accordance with the conventions of \.{WEB},
//! @.WEB@>
//! which converts single-character strings into the ASCII code number of the
//! single character involved, while it converts other strings into integers
//! and builds a string pool file. Thus, when the string constant \.{"."} appears
//! in the program below, \.{WEB} converts it into the integer 46, which is the
//! ASCII code for a period, while \.{WEB} will convert a string like \.{"hello"}
//! into some integer greater than~255. String number 46 will presumably be the
//! single character `\..'\thinspace; but some ASCII codes have no standard visible
//! representation, and \MF\ may need to be able to print an arbitrary
//! ASCII character, so the first 256 strings are used to specify exactly what
//! should be printed for each of the 256 possibilities.
//!
//! Elements of the |str_pool| array must be ASCII codes that can actually be
//! printed; i.e., they must have an |xchr| equivalent in the local
//! character set. (This restriction applies only to preloaded strings,
//! not to those generated dynamically by the user.)
//!
//! Some \PASCAL\ compilers won't pack integers into a single byte unless the
//! integers lie in the range |-128..127|. To accommodate such systems
//! we access the string pool only via macros that can easily be redefined.
//! @^system dependencies@>
//!
//! @d si(#) == # {convert from |ASCII_code| to |packed_ASCII_code|}
//! @d so(#) == # {convert from |packed_ASCII_code| to |ASCII_code|}
//!
//! @<Types...@>=
//! @!pool_pointer = 0..pool_size; {for variables that point into |str_pool|}
//! @!str_number = 0..max_strings; {for variables that point into |str_start|}
//! @!packed_ASCII_code = 0..255; {elements of |str_pool| array}
//!
//! @ @<Glob...@>=
//! @!str_pool:packed array[pool_pointer] of packed_ASCII_code; {the characters}
//! @!str_start : array[str_number] of pool_pointer; {the starting pointers}
//! @!pool_ptr : pool_pointer; {first unused position in |str_pool|}
//! @!str_ptr : str_number; {number of the current string being created}
//! @!init_pool_ptr : pool_pointer; {the starting value of |pool_ptr|}
//! @!init_str_ptr : str_number; {the starting value of |str_ptr|}
//! @!max_pool_ptr : pool_pointer; {the maximum so far of |pool_ptr|}
//! @!max_str_ptr : str_number; {the maximum so far of |str_ptr|}
//!
//! @ Several of the elementary string operations are performed using \.{WEB}
//! macros instead of \PASCAL\ procedures, because many of the
//! operations are done quite frequently and we want to avoid the
//! overhead of procedure calls. For example, here is
//! a simple macro that computes the length of a string.
//! @.WEB@>
//!
//! @d length(#)==(str_start[#+1]-str_start[#]) {the number of characters
//!   in string number \#}
//!
//! @ The length of the current string is called |cur_length|:
//!
//! @d cur_length == (pool_ptr - str_start[str_ptr])
//!
//! @ Strings are created by appending character codes to |str_pool|.
//! The |append_char| macro, defined here, does not check to see if the
//! value of |pool_ptr| has gotten too high; this test is supposed to be
//! made before |append_char| is used.
//!
//! To test if there is room to append |l| more characters to |str_pool|,
//! we shall write |str_room(l)|, which aborts \MF\ and gives an
//! apologetic error message if there isn't enough room.
//!
//! @d append_char(#) == {put |ASCII_code| \# at the end of |str_pool|}
//! begin str_pool[pool_ptr]:=si(#); incr(pool_ptr);
//! end
//! @d str_room(#) == {make sure that the pool hasn't overflowed}
//!   begin if pool_ptr+# > max_pool_ptr then
//!     begin if pool_ptr+# > pool_size then
//!       overflow("pool size",pool_size-init_pool_ptr);
//! @:METAFONT capacity exceeded pool size}{\quad pool size@>
//!     max_pool_ptr:=pool_ptr+#;
//!     end;
//!   end
//!
//! @ \MF's string expressions are implemented in a brute-force way: Every
//! new string or substring that is needed is simply copied into the string pool.
//!
//! Such a scheme can be justified because string expressions aren't a big
//! deal in \MF\ applications; strings rarely need to be saved from one
//! statement to the next. But it would waste space needlessly if we didn't
//! try to reclaim the space of strings that are going to be used only once.
//!
//! Therefore a simple reference count mechanism is provided: If there are
//! @^reference counts@>
//! no references to a certain string from elsewhere in the program, and
//! if there are no references to any strings created subsequent to it,
//! then the string space will be reclaimed.
//!
//! The number of references to string number |s| will be |str_ref[s]|. The
//! special value |str_ref[s]=max_str_ref=127| is used to denote an unknown
//! positive number of references; such strings will never be recycled. If
//! a string is ever referred to more than 126 times, simultaneously, we
//! put it in this category. Hence a single byte suffices to store each |str_ref|.
//!
//! @d max_str_ref=127 {``infinite'' number of references}
//! @d add_str_ref(#)==begin if str_ref[#]<max_str_ref then incr(str_ref[#]);
//!   end
//!
//! @<Glob...@>=
//! @!str_ref:array[str_number] of 0..max_str_ref;
//!
//! @ Here's what we do when a string reference disappears:
//!
//! @d delete_str_ref(#)== begin if str_ref[#]<max_str_ref then
//!     if str_ref[#]>1 then decr(str_ref[#])@+else flush_string(#);
//!     end
//!
//! @<Declare the procedure called |flush_string|@>=
//! procedure flush_string(@!s:str_number);
//! begin if s<str_ptr-1 then str_ref[s]:=0
//! else  repeat decr(str_ptr);
//!   until str_ref[str_ptr-1]<>0;
//! pool_ptr:=str_start[str_ptr];
//! end;
//!
//! @ Once a sequence of characters has been appended to |str_pool|, it
//! officially becomes a string when the function |make_string| is called.
//! This function returns the identification number of the new string as its
//! value.
//!
//! @p function make_string : str_number; {current string enters the pool}
//! begin if str_ptr=max_str_ptr then
//!   begin if str_ptr=max_strings then
//!     overflow("number of strings",max_strings-init_str_ptr);
//! @:METAFONT capacity exceeded number of strings}{\quad number of strings@>
//!   incr(max_str_ptr);
//!   end;
//! str_ref[str_ptr]:=1; incr(str_ptr); str_start[str_ptr]:=pool_ptr;
//! make_string:=str_ptr-1;
//! end;
//!
//! @ The following subroutine compares string |s| with another string of the
//! same length that appears in |buffer| starting at position |k|;
//! the result is |true| if and only if the strings are equal.
//!
//! @p function str_eq_buf(@!s:str_number;@!k:integer):boolean;
//!   {test equality of strings}
//! label not_found; {loop exit}
//! var @!j: pool_pointer; {running index}
//! @!result: boolean; {result of comparison}
//! begin j:=str_start[s];
//! while j<str_start[s+1] do
//!   begin if so(str_pool[j])<>buffer[k] then
//!     begin result:=false; goto not_found;
//!     end;
//!   incr(j); incr(k);
//!   end;
//! result:=true;
//! not_found: str_eq_buf:=result;
//! end;
//!
//! @ Here is a similar routine, but it compares two strings in the string pool,
//! and it does not assume that they have the same length. If the first string
//! is lexicographically greater than, less than, or equal to the second,
//! the result is respectively positive, negative, or zero.
//!
//! @p function str_vs_str(@!s,@!t:str_number):integer;
//!   {test equality of strings}
//! label exit;
//! var @!j,@!k: pool_pointer; {running indices}
//! @!ls,@!lt:integer; {lengths}
//! @!l:integer; {length remaining to test}
//! begin ls:=length(s); lt:=length(t);
//! if ls<=lt then l:=ls@+else l:=lt;
//! j:=str_start[s]; k:=str_start[t];
//! while l>0 do
//!   begin if str_pool[j]<>str_pool[k] then
//!     begin str_vs_str:=str_pool[j]-str_pool[k]; return;
//!     end;
//!   incr(j); incr(k); decr(l);
//!   end;
//! str_vs_str:=ls-lt;
//! exit:end;
//!
//! @ The initial values of |str_pool|, |str_start|, |pool_ptr|,
//! and |str_ptr| are computed by the \.{INIMF} program, based in part
//! on the information that \.{WEB} has output while processing \MF.
//! @.INIMF@>
//! @^string pool@>
//!
//! @p @!init function get_strings_started:boolean; {initializes the string pool,
//!   but returns |false| if something goes wrong}
//! label done,exit;
//! var @!k,@!l:0..255; {small indices or counters}
//! @!m,@!n:text_char; {characters input from |pool_file|}
//! @!g:str_number; {the string just created}
//! @!a:integer; {accumulator for check sum}
//! @!c:boolean; {check sum has been checked}
//! begin pool_ptr:=0; str_ptr:=0; max_pool_ptr:=0; max_str_ptr:=0; str_start[0]:=0;
//! @<Make the first 256 strings@>;
//! @<Read the other strings from the \.{MF.POOL} file and return |true|,
//!   or give an error message and return |false|@>;
//! exit:end;
//! tini
//!
//! @ @d app_lc_hex(#)==l:=#;
//!   if l<10 then append_char(l+"0")@+else append_char(l-10+"a")
//!
//! @<Make the first 256...@>=
//! for k:=0 to 255 do
//!   begin if (@<Character |k| cannot be printed@>) then
//!     begin append_char("^"); append_char("^");
//!     if k<@'100 then append_char(k+@'100)
//!     else if k<@'200 then append_char(k-@'100)
//!     else begin app_lc_hex(k div 16); app_lc_hex(k mod 16);
//!       end;
//!     end
//!   else append_char(k);
//!   g:=make_string; str_ref[g]:=max_str_ref;
//!   end
//!
//! @ The first 128 strings will contain 95 standard ASCII characters, and the
//! other 33 characters will be printed in three-symbol form like `\.{\^\^A}'
//! unless a system-dependent change is made here. Installations that have
//! an extended character set, where for example |xchr[@'32]=@t\.{\'^^Z\'}@>|,
//! would like string @'32 to be the single character @'32 instead of the
//! three characters @'136, @'136, @'132 (\.{\^\^Z}). On the other hand,
//! even people with an extended character set will want to represent string
//! @'15 by \.{\^\^M}, since @'15 is ASCII's ``carriage return'' code; the idea is
//! to produce visible strings instead of tabs or line-feeds or carriage-returns
//! or bell-rings or characters that are treated anomalously in text files.
//!
//! Unprintable characters of codes 128--255 are, similarly, rendered
//! \.{\^\^80}--\.{\^\^ff}.
//!
//! The boolean expression defined here should be |true| unless \MF\ internal
//! code number~|k| corresponds to a non-troublesome visible symbol in the
//! local character set.
//! If character |k| cannot be printed, and |k<@'200|, then character |k+@'100| or
//! |k-@'100| must be printable; moreover, ASCII codes
//! |[@'60..@'71, @'136, @'141..@'146]|
//! must be printable.
//! @^character set dependencies@>
//! @^system dependencies@>
//!
//! @<Character |k| cannot be printed@>=
//!   (k<" ")or(k>"~")
//!
//! @ When the \.{WEB} system program called \.{TANGLE} processes the \.{MF.WEB}
//! description that you are now reading, it outputs the \PASCAL\ program
//! \.{MF.PAS} and also a string pool file called \.{MF.POOL}. The \.{INIMF}
//! @.WEB@>@.INIMF@>
//! program reads the latter file, where each string appears as a two-digit decimal
//! length followed by the string itself, and the information is recorded in
//! \MF's string memory.
//!
//! @<Glob...@>=
//! @!init @!pool_file:alpha_file; {the string-pool file output by \.{TANGLE}}
//! tini
//!
//! @ @d bad_pool(#)==begin wake_up_terminal; write_ln(term_out,#);
//!   a_close(pool_file); get_strings_started:=false; return;
//!   end
//! @<Read the other strings...@>=
//! name_of_file:=pool_name; {we needn't set |name_length|}
//! if a_open_in(pool_file) then
//!   begin c:=false;
//!   repeat @<Read one string, but return |false| if the
//!     string memory space is getting too tight for comfort@>;
//!   until c;
//!   a_close(pool_file); get_strings_started:=true;
//!   end
//! else  bad_pool('! I can''t read MF.POOL.')
//! @.I can't read MF.POOL@>
//!
//! @ @<Read one string...@>=
//! begin if eof(pool_file) then bad_pool('! MF.POOL has no check sum.');
//! @.MF.POOL has no check sum@>
//! read(pool_file,m,n); {read two digits of string length}
//! if m='*' then @<Check the pool check sum@>
//! else  begin if (xord[m]<"0")or(xord[m]>"9")or@|
//!       (xord[n]<"0")or(xord[n]>"9") then
//!     bad_pool('! MF.POOL line doesn''t begin with two digits.');
//! @.MF.POOL line doesn't...@>
//!   l:=xord[m]*10+xord[n]-"0"*11; {compute the length}
//!   if pool_ptr+l+string_vacancies>pool_size then
//!     bad_pool('! You have to increase POOLSIZE.');
//! @.You have to increase POOLSIZE@>
//!   for k:=1 to l do
//!     begin if eoln(pool_file) then m:=' '@+else read(pool_file,m);
//!     append_char(xord[m]);
//!     end;
//!   read_ln(pool_file); g:=make_string; str_ref[g]:=max_str_ref;
//!   end;
//! end
//!
//! @ The \.{WEB} operation \.{@@\$} denotes the value that should be at the
//! end of this \.{MF.POOL} file; any other value means that the wrong pool
//! file has been loaded.
//! @^check sum@>
//!
//! @<Check the pool check sum@>=
//! begin a:=0; k:=1;
//! loop@+  begin if (xord[n]<"0")or(xord[n]>"9") then
//!   bad_pool('! MF.POOL check sum doesn''t have nine digits.');
//! @.MF.POOL check sum...@>
//!   a:=10*a+xord[n]-"0";
//!   if k=9 then goto done;
//!   incr(k); read(pool_file,n);
//!   end;
//! done: if a<>@$ then bad_pool('! MF.POOL doesn''t match; TANGLE me again.');
//! @.MF.POOL doesn't match@>
//! c:=true;
//! end
//!
