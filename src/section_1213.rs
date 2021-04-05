//! @ @<Numbered cases...@>=
//! 1: print_word(mem[n]); {display |mem[n]| in all forms}
//! 2: print_int(info(n));
//! 3: print_int(link(n));
//! 4: begin print_int(eq_type(n)); print_char(":"); print_int(equiv(n));
//!   end;
//! 5: print_variable_name(n);
//! 6: print_int(internal[n]);
//! 7: do_show_dependencies;
//! 9: show_token_list(n,null,100000,0);
//! 10: slow_print(n);
//! 11: check_mem(n>0); {check wellformedness; print new busy locations if |n>0|}
//! 12: search_mem(n); {look for pointers to |n|}
//! 13: begin read(term_in,l); print_cmd_mod(n,l);
//!   end;
//! 14: for k:=0 to n do print(buffer[k]);
//! 15: panicking:=not panicking;
//!
