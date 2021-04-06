//! @* \[48] Dumping and undumping the tables.
//! After \.{INIMF} has seen a collection of macros, it
//! can write all the necessary information on an auxiliary file so
//! that production versions of \MF\ are able to initialize their
//! memory at high speed. The present section of the program takes
//! care of such output and input. We shall consider simultaneously
//! the processes of storing and restoring,
//! so that the inverse relation between them is clear.
//! @.INIMF@>
//!
//! The global variable |base_ident| is a string that is printed right
//! after the |banner| line when \MF\ is ready to start. For \.{INIMF} this
//! string says simply `\.{(INIMF)}'; for other versions of \MF\ it says,
//! for example, `\.{(preloaded base=plain 1984.2.29)}', showing the year,
//! month, and day that the base file was created. We have |base_ident=0|
//! before \MF's tables are loaded.
//!
//! @<Glob...@>=
//! @!base_ident:str_number;
//!
//! @ @<Set init...@>=
//! base_ident:=0;
//!
//! @ @<Initialize table entries...@>=
//! base_ident:=" (INIMF)";
//!
//! @ @<Declare act...@>=
//! @!init procedure store_base_file;
//! var @!k:integer; {all-purpose index}
//! @!p,@!q: pointer; {all-purpose pointers}
//! @!x: integer; {something to dump}
//! @!w: four_quarters; {four ASCII codes}
//! begin @<Create the |base_ident|, open the base file,
//!   and inform the user that dumping has begun@>;
//! @<Dump constants for consistency check@>;
//! @<Dump the string pool@>;
//! @<Dump the dynamic memory@>;
//! @<Dump the table of equivalents and the hash table@>;
//! @<Dump a few more things and the closing check word@>;
//! @<Close the base file@>;
//! end;
//! tini
//!
//! @ Corresponding to the procedure that dumps a base file, we also have a function
//! that reads~one~in. The function returns |false| if the dumped base is
//! incompatible with the present \MF\ table sizes, etc.
//!
//! @d off_base=6666 {go here if the base file is unacceptable}
//! @d too_small(#)==begin wake_up_terminal;
//!   wterm_ln('---! Must increase the ',#);
//! @.Must increase the x@>
//!   goto off_base;
//!   end
//!
//! @p @t\4@>@<Declare the function called |open_base_file|@>@;
//! function load_base_file:boolean;
//! label off_base,exit;
//! var @!k:integer; {all-purpose index}
//! @!p,@!q: pointer; {all-purpose pointers}
//! @!x: integer; {something undumped}
//! @!w: four_quarters; {four ASCII codes}
//! begin @<Undump constants for consistency check@>;
//! @<Undump the string pool@>;
//! @<Undump the dynamic memory@>;
//! @<Undump the table of equivalents and the hash table@>;
//! @<Undump a few more things and the closing check word@>;
//! load_base_file:=true; return; {it worked!}
//! off_base: wake_up_terminal;
//!   wterm_ln('(Fatal base file error; I''m stymied)');
//! @.Fatal base file error@>
//! load_base_file:=false;
//! exit:end;
//!
//! @ Base files consist of |memory_word| items, and we use the following
//! macros to dump words of different types:
//!
//! @d dump_wd(#)==begin base_file^:=#; put(base_file);@+end
//! @d dump_int(#)==begin base_file^.int:=#; put(base_file);@+end
//! @d dump_hh(#)==begin base_file^.hh:=#; put(base_file);@+end
//! @d dump_qqqq(#)==begin base_file^.qqqq:=#; put(base_file);@+end
//!
//! @<Glob...@>=
//! @!base_file:word_file; {for input or output of base information}
//!
//! @ The inverse macros are slightly more complicated, since we need to check
//! the range of the values we are reading in. We say `|undump(a)(b)(x)|' to
//! read an integer value |x| that is supposed to be in the range |a<=x<=b|.
//! System error messages should be suppressed when undumping.
//! @^system dependencies@>
//!
//! @d undump_wd(#)==begin get(base_file); #:=base_file^;@+end
//! @d undump_int(#)==begin get(base_file); #:=base_file^.int;@+end
//! @d undump_hh(#)==begin get(base_file); #:=base_file^.hh;@+end
//! @d undump_qqqq(#)==begin get(base_file); #:=base_file^.qqqq;@+end
//! @d undump_end_end(#)==#:=x;@+end
//! @d undump_end(#)==(x>#) then goto off_base@+else undump_end_end
//! @d undump(#)==begin undump_int(x); if (x<#) or undump_end
//! @d undump_size_end_end(#)==too_small(#)@+else undump_end_end
//! @d undump_size_end(#)==if x># then undump_size_end_end
//! @d undump_size(#)==begin undump_int(x);
//!   if x<# then goto off_base; undump_size_end
//!
//! @ The next few sections of the program should make it clear how we use the
//! dump/undump macros.
//!
//! @<Dump constants for consistency check@>=
//! dump_int(@$);@/
//! dump_int(mem_min);@/
//! dump_int(mem_top);@/
//! dump_int(hash_size);@/
//! dump_int(hash_prime);@/
//! dump_int(max_in_open)
//!
//! @ Sections of a \.{WEB} program that are ``commented out'' still contribute
//! strings to the string pool; therefore \.{INIMF} and \MF\ will have
//! the same strings. (And it is, of course, a good thing that they do.)
//! @.WEB@>
//! @^string pool@>
//!
//! @<Undump constants for consistency check@>=
//! x:=base_file^.int;
//! if x<>@$ then goto off_base; {check that strings are the same}
//! undump_int(x);
//! if x<>mem_min then goto off_base;
//! undump_int(x);
//! if x<>mem_top then goto off_base;
//! undump_int(x);
//! if x<>hash_size then goto off_base;
//! undump_int(x);
//! if x<>hash_prime then goto off_base;
//! undump_int(x);
//! if x<>max_in_open then goto off_base
//!
//! @ @d dump_four_ASCII==
//!   w.b0:=qi(so(str_pool[k])); w.b1:=qi(so(str_pool[k+1]));
//!   w.b2:=qi(so(str_pool[k+2])); w.b3:=qi(so(str_pool[k+3]));
//!   dump_qqqq(w)
//!
//! @<Dump the string pool@>=
//! dump_int(pool_ptr);
//! dump_int(str_ptr);
//! for k:=0 to str_ptr do dump_int(str_start[k]);
//! k:=0;
//! while k+4<pool_ptr do
//!   begin dump_four_ASCII; k:=k+4;
//!   end;
//! k:=pool_ptr-4; dump_four_ASCII;
//! print_ln; print_int(str_ptr); print(" strings of total length ");
//! print_int(pool_ptr)
//!
//! @ @d undump_four_ASCII==
//!   undump_qqqq(w);
//!   str_pool[k]:=si(qo(w.b0)); str_pool[k+1]:=si(qo(w.b1));
//!   str_pool[k+2]:=si(qo(w.b2)); str_pool[k+3]:=si(qo(w.b3))
//!
//! @<Undump the string pool@>=
//! undump_size(0)(pool_size)('string pool size')(pool_ptr);
//! undump_size(0)(max_strings)('max strings')(str_ptr);
//! for k:=0 to str_ptr do
//!   begin undump(0)(pool_ptr)(str_start[k]); str_ref[k]:=max_str_ref;
//!   end;
//! k:=0;
//! while k+4<pool_ptr do
//!   begin undump_four_ASCII; k:=k+4;
//!   end;
//! k:=pool_ptr-4; undump_four_ASCII;
//! init_str_ptr:=str_ptr; init_pool_ptr:=pool_ptr;
//! max_str_ptr:=str_ptr; max_pool_ptr:=pool_ptr
//!
//! @ By sorting the list of available spaces in the variable-size portion of
//! |mem|, we are usually able to get by without having to dump very much
//! of the dynamic memory.
//!
//! We recompute |var_used| and |dyn_used|, so that \.{INIMF} dumps valid
//! information even when it has not been gathering statistics.
//!
//! @<Dump the dynamic memory@>=
//! sort_avail; var_used:=0;
//! dump_int(lo_mem_max); dump_int(rover);
//! p:=mem_min; q:=rover; x:=0;
//! repeat for k:=p to q+1 do dump_wd(mem[k]);
//! x:=x+q+2-p; var_used:=var_used+q-p;
//! p:=q+node_size(q); q:=rlink(q);
//! until q=rover;
//! var_used:=var_used+lo_mem_max-p; dyn_used:=mem_end+1-hi_mem_min;@/
//! for k:=p to lo_mem_max do dump_wd(mem[k]);
//! x:=x+lo_mem_max+1-p;
//! dump_int(hi_mem_min); dump_int(avail);
//! for k:=hi_mem_min to mem_end do dump_wd(mem[k]);
//! x:=x+mem_end+1-hi_mem_min;
//! p:=avail;
//! while p<>null do
//!   begin decr(dyn_used); p:=link(p);
//!   end;
//! dump_int(var_used); dump_int(dyn_used);
//! print_ln; print_int(x);
//! print(" memory locations dumped; current usage is ");
//! print_int(var_used); print_char("&"); print_int(dyn_used)
//!
//! @ @<Undump the dynamic memory@>=
//! undump(lo_mem_stat_max+1000)(hi_mem_stat_min-1)(lo_mem_max);
//! undump(lo_mem_stat_max+1)(lo_mem_max)(rover);
//! p:=mem_min; q:=rover;
//! repeat for k:=p to q+1 do undump_wd(mem[k]);
//! p:=q+node_size(q);
//! if (p>lo_mem_max)or((q>=rlink(q))and(rlink(q)<>rover)) then goto off_base;
//! q:=rlink(q);
//! until q=rover;
//! for k:=p to lo_mem_max do undump_wd(mem[k]);
//! undump(lo_mem_max+1)(hi_mem_stat_min)(hi_mem_min);
//! undump(null)(mem_top)(avail); mem_end:=mem_top;
//! for k:=hi_mem_min to mem_end do undump_wd(mem[k]);
//! undump_int(var_used); undump_int(dyn_used)
//!
//! @ A different scheme is used to compress the hash table, since its lower region
//! is usually sparse. When |text(p)<>0| for |p<=hash_used|, we output three
//! words: |p|, |hash[p]|, and |eqtb[p]|. The hash table is, of course, densely
//! packed for |p>=hash_used|, so the remaining entries are output in~a~block.
//!
//! @<Dump the table of equivalents and the hash table@>=
//! dump_int(hash_used); st_count:=frozen_inaccessible-1-hash_used;
//! for p:=1 to hash_used do if text(p)<>0 then
//!   begin dump_int(p); dump_hh(hash[p]); dump_hh(eqtb[p]); incr(st_count);
//!   end;
//! for p:=hash_used+1 to hash_end do
//!   begin dump_hh(hash[p]); dump_hh(eqtb[p]);
//!   end;
//! dump_int(st_count);@/
//! print_ln; print_int(st_count); print(" symbolic tokens")
//!
//! @ @<Undump the table of equivalents and the hash table@>=
//! undump(1)(frozen_inaccessible)(hash_used); p:=0;
//! repeat undump(p+1)(hash_used)(p); undump_hh(hash[p]); undump_hh(eqtb[p]);
//! until p=hash_used;
//! for p:=hash_used+1 to hash_end do
//!   begin undump_hh(hash[p]); undump_hh(eqtb[p]);
//!   end;
//! undump_int(st_count)
//!
//! @ We have already printed a lot of statistics, so we set |tracing_stats:=0|
//! to prevent them from appearing again.
//!
//! @<Dump a few more things and the closing check word@>=
//! dump_int(int_ptr);
//! for k:=1 to int_ptr do
//!   begin dump_int(internal[k]); dump_int(int_name[k]);
//!   end;
//! dump_int(start_sym); dump_int(interaction); dump_int(base_ident);
//! dump_int(bg_loc); dump_int(eg_loc); dump_int(serial_no); dump_int(69069);
//! internal[tracing_stats]:=0
//!
//! @ @<Undump a few more things and the closing check word@>=
//! undump(max_given_internal)(max_internal)(int_ptr);
//! for k:=1 to int_ptr do
//!   begin undump_int(internal[k]);
//!   undump(0)(str_ptr)(int_name[k]);
//!   end;
//! undump(0)(frozen_inaccessible)(start_sym);
//! undump(batch_mode)(error_stop_mode)(interaction);
//! undump(0)(str_ptr)(base_ident);
//! undump(1)(hash_end)(bg_loc);
//! undump(1)(hash_end)(eg_loc);
//! undump_int(serial_no);@/
//! undump_int(x);@+if (x<>69069)or eof(base_file) then goto off_base
//!
//! @ @<Create the |base_ident|...@>=
//! selector:=new_string;
//! print(" (preloaded base="); print(job_name); print_char(" ");
//! print_int(round_unscaled(internal[year])); print_char(".");
//! print_int(round_unscaled(internal[month])); print_char(".");
//! print_int(round_unscaled(internal[day])); print_char(")");
//! if interaction=batch_mode then selector:=log_only
//! else selector:=term_and_log;
//! str_room(1); base_ident:=make_string; str_ref[base_ident]:=max_str_ref;@/
//! pack_job_name(base_extension);
//! while not w_open_out(base_file) do
//!  prompt_file_name("base file name",base_extension);
//! print_nl("Beginning to dump on file ");
//! @.Beginning to dump...@>
//! slow_print(w_make_name_string(base_file)); flush_string(str_ptr-1);
//! print_nl(""); slow_print(base_ident)
//!
//! @ @<Close the base file@>=
//! w_close(base_file)
//!
