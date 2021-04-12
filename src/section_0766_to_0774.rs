//! @* \[38] File names.
//! It's time now to fret about file names.  Besides the fact that different
//! operating systems treat files in different ways, we must cope with the
//! fact that completely different naming conventions are used by different
//! groups of people. The following programs show what is required for one
//! particular operating system; similar routines for other systems are not
//! difficult to devise.
//! @^system dependencies@>
//!
//! \MF\ assumes that a file name has three parts: the name proper; its
//! ``extension''; and a ``file area'' where it is found in an external file
//! system.  The extension of an input file is assumed to be
//! `\.{.mf}' unless otherwise specified; it is `\.{.log}' on the
//! transcript file that records each run of \MF; it is `\.{.tfm}' on the font
//! metric files that describe characters in the fonts \MF\ creates; it is
//! `\.{.gf}' on the output files that specify generic font information; and it
//! is `\.{.base}' on the base files written by \.{INIMF} to initialize \MF.
//! The file area can be arbitrary on input files, but files are usually
//! output to the user's current area.  If an input file cannot be
//! found on the specified area, \MF\ will look for it on a special system
//! area; this special area is intended for commonly used input files.
//!
//! Simple uses of \MF\ refer only to file names that have no explicit
//! extension or area. For example, a person usually says `\.{input} \.{cmr10}'
//! instead of `\.{input} \.{cmr10.new}'. Simple file
//! names are best, because they make the \MF\ source files portable;
//! whenever a file name consists entirely of letters and digits, it should be
//! treated in the same way by all implementations of \MF. However, users
//! need the ability to refer to other files in their environment, especially
//! when responding to error messages concerning unopenable files; therefore
//! we want to let them use the syntax that appears in their favorite
//! operating system.
//!
//! @ \MF\ uses the same conventions that have proved to be satisfactory for
//! \TeX. In order to isolate the system-dependent aspects of file names, the
//! @^system dependencies@>
//! system-independent parts of \MF\ are expressed in terms
//! of three system-dependent
//! procedures called |begin_name|, |more_name|, and |end_name|. In
//! essence, if the user-specified characters of the file name are $c_1\ldots c_n$,
//! the system-independent driver program does the operations
//! $$|begin_name|;\,|more_name|(c_1);\,\ldots\,;\,|more_name|(c_n);
//! \,|end_name|.$$
//! These three procedures communicate with each other via global variables.
//! Afterwards the file name will appear in the string pool as three strings
//! called |cur_name|\penalty10000\hskip-.05em,
//! |cur_area|, and |cur_ext|; the latter two are null (i.e.,
//! |""|), unless they were explicitly specified by the user.
//!
//! Actually the situation is slightly more complicated, because \MF\ needs
//! to know when the file name ends. The |more_name| routine is a function
//! (with side effects) that returns |true| on the calls |more_name|$(c_1)$,
//! \dots, |more_name|$(c_{n-1})$. The final call |more_name|$(c_n)$
//! returns |false|; or, it returns |true| and $c_n$ is the last character
//! on the current input line. In other words,
//! |more_name| is supposed to return |true| unless it is sure that the
//! file name has been completely scanned; and |end_name| is supposed to be able
//! to finish the assembly of |cur_name|, |cur_area|, and |cur_ext| regardless of
//! whether $|more_name|(c_n)$ returned |true| or |false|.
//!
//! @<Glob...@>=
//! @!cur_name:str_number; {name of file just scanned}
//! @!cur_area:str_number; {file area just scanned, or \.{""}}
//! @!cur_ext:str_number; {file extension just scanned, or \.{""}}
//!
//! @ The file names we shall deal with for illustrative purposes have the
//! following structure:  If the name contains `\.>' or `\.:', the file area
//! consists of all characters up to and including the final such character;
//! otherwise the file area is null.  If the remaining file name contains
//! `\..', the file extension consists of all such characters from the first
//! remaining `\..' to the end, otherwise the file extension is null.
//! @^system dependencies@>
//!
//! We can scan such file names easily by using two global variables that keep track
//! of the occurrences of area and extension delimiters:
//!
//! @<Glob...@>=
//! @!area_delimiter:pool_pointer; {the most recent `\.>' or `\.:', if any}
//! @!ext_delimiter:pool_pointer; {the relevant `\..', if any}
//!
//! @ Input files that can't be found in the user's area may appear in a standard
//! system area called |MF_area|.
//! This system area name will, of course, vary from place to place.
//! @^system dependencies@>
//!
//! @d MF_area=="MFinputs:"
//! @.MFinputs@>
//!
//! @ Here now is the first of the system-dependent routines for file name scanning.
//! @^system dependencies@>
//!
//! @p procedure begin_name;
//! begin area_delimiter:=0; ext_delimiter:=0;
//! end;
//!
//! @ And here's the second.
//! @^system dependencies@>
//!
//! @p function more_name(@!c:ASCII_code):boolean;
//! begin if c=" " then more_name:=false
//! else  begin if (c=">")or(c=":") then
//!     begin area_delimiter:=pool_ptr; ext_delimiter:=0;
//!     end
//!   else if (c=".")and(ext_delimiter=0) then ext_delimiter:=pool_ptr;
//!   str_room(1); append_char(c); {contribute |c| to the current string}
//!   more_name:=true;
//!   end;
//! end;
//!
//! @ The third.
//! @^system dependencies@>
//!
//! @p procedure end_name;
//! begin if str_ptr+3>max_str_ptr then
//!   begin if str_ptr+3>max_strings then
//!     overflow("number of strings",max_strings-init_str_ptr);
//! @:METAFONT capacity exceeded number of strings}{\quad number of strings@>
//!   max_str_ptr:=str_ptr+3;
//!   end;
//! if area_delimiter=0 then cur_area:=""
//! else  begin cur_area:=str_ptr; incr(str_ptr);
//!   str_start[str_ptr]:=area_delimiter+1;
//!   end;
//! if ext_delimiter=0 then
//!   begin cur_ext:=""; cur_name:=make_string;
//!   end
//! else  begin cur_name:=str_ptr; incr(str_ptr);
//!   str_start[str_ptr]:=ext_delimiter; cur_ext:=make_string;
//!   end;
//! end;
//!
//! @ Conversely, here is a routine that takes three strings and prints a file
//! name that might have produced them. (The routine is system dependent, because
//! some operating systems put the file area last instead of first.)
//! @^system dependencies@>
//!
//! @<Basic printing...@>=
//! procedure print_file_name(@!n,@!a,@!e:integer);
//! begin slow_print(a); slow_print(n); slow_print(e);
//! end;
//!
//! @ Another system-dependent routine is needed to convert three internal
//! \MF\ strings
//! to the |name_of_file| value that is used to open files. The present code
//! allows both lowercase and uppercase letters in the file name.
//! @^system dependencies@>
//!
//! @d append_to_name(#)==begin c:=#; incr(k);
//!   if k<=file_name_size then name_of_file[k]:=xchr[c];
//!   end
//!
//! @p procedure pack_file_name(@!n,@!a,@!e:str_number);
//! var @!k:integer; {number of positions filled in |name_of_file|}
//! @!c: ASCII_code; {character being packed}
//! @!j:pool_pointer; {index into |str_pool|}
//! begin k:=0;
//! for j:=str_start[a] to str_start[a+1]-1 do append_to_name(so(str_pool[j]));
//! for j:=str_start[n] to str_start[n+1]-1 do append_to_name(so(str_pool[j]));
//! for j:=str_start[e] to str_start[e+1]-1 do append_to_name(so(str_pool[j]));
//! if k<=file_name_size then name_length:=k@+else name_length:=file_name_size;
//! for k:=name_length+1 to file_name_size do name_of_file[k]:=' ';
//! end;
//!
