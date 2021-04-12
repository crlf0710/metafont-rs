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
