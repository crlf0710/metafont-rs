//! @* \[47] Shipping characters out.
//! The |ship_out| procedure, to be described below, is given a pointer to
//! an edge structure. Its mission is to describe the positive pixels
//! in \.{GF} form, outputting a ``character'' to |gf_file|.
//!
//! Several global variables hold information about the font file as a whole:\
//! |gf_min_m|, |gf_max_m|, |gf_min_n|, and |gf_max_n| are the minimum and
//! maximum \.{GF} coordinates output so far; |gf_prev_ptr| is the byte number
//! following the preamble or the last |eoc| command in the output;
//! |total_chars| is the total number of characters (i.e., |boc..eoc| segments)
//! shipped out.  There's also an array, |char_ptr|, containing the starting
//! positions of each character in the file, as required for the postamble. If
//! character code~|c| has not yet been output, |char_ptr[c]=-1|.
//!
//! @<Glob...@>=
//! @!gf_min_m,@!gf_max_m,@!gf_min_n,@!gf_max_n:integer; {bounding rectangle}
//! @!gf_prev_ptr:integer; {where the present/next character started/starts}
//! @!total_chars:integer; {the number of characters output so far}
//! @!char_ptr:array[eight_bits] of integer; {where individual characters started}
//! @!gf_dx,@!gf_dy:array[eight_bits] of integer; {device escapements}
//!
//! @ @<Set init...@>=
//! gf_prev_ptr:=0; total_chars:=0;
//!
//! @ The \.{GF} bytes are output to a buffer instead of being sent
//! byte-by-byte to |gf_file|, because this tends to save a lot of
//! subroutine-call overhead. \MF\ uses the same conventions for |gf_file|
//! as \TeX\ uses for its \\{dvi\_file}; hence if system-dependent
//! changes are needed, they should probably be the same for both programs.
//!
//! The output buffer is divided into two parts of equal size; the bytes found
//! in |gf_buf[0..half_buf-1]| constitute the first half, and those in
//! |gf_buf[half_buf..gf_buf_size-1]| constitute the second. The global
//! variable |gf_ptr| points to the position that will receive the next
//! output byte. When |gf_ptr| reaches |gf_limit|, which is always equal
//! to one of the two values |half_buf| or |gf_buf_size|, the half buffer that
//! is about to be invaded next is sent to the output and |gf_limit| is
//! changed to its other value. Thus, there is always at least a half buffer's
//! worth of information present, except at the very beginning of the job.
//!
//! Bytes of the \.{GF} file are numbered sequentially starting with 0;
//! the next byte to be generated will be number |gf_offset+gf_ptr|.
//!
//! @<Types...@>=
//! @!gf_index=0..gf_buf_size; {an index into the output buffer}
//!
//! @ Some systems may find it more efficient to make |gf_buf| a |packed|
//! array, since output of four bytes at once may be facilitated.
//! @^system dependencies@>
//!
//! @<Glob...@>=
//! @!gf_buf:array[gf_index] of eight_bits; {buffer for \.{GF} output}
//! @!half_buf:gf_index; {half of |gf_buf_size|}
//! @!gf_limit:gf_index; {end of the current half buffer}
//! @!gf_ptr:gf_index; {the next available buffer address}
//! @!gf_offset:integer; {|gf_buf_size| times the number of times the
//!   output buffer has been fully emptied}
//!
//! @ Initially the buffer is all in one piece; we will output half of it only
//! after it first fills up.
//!
//! @<Set init...@>=
//! half_buf:=gf_buf_size div 2; gf_limit:=gf_buf_size; gf_ptr:=0;
//! gf_offset:=0;
//!
//! @ The actual output of |gf_buf[a..b]| to |gf_file| is performed by calling
//! |write_gf(a,b)|. It is safe to assume that |a| and |b+1| will both be
//! multiples of 4 when |write_gf(a,b)| is called; therefore it is possible on
//! many machines to use efficient methods to pack four bytes per word and to
//! output an array of words with one system call.
//! @^system dependencies@>
//!
//! @<Declare generic font output procedures@>=
//! procedure write_gf(@!a,@!b:gf_index);
//! var k:gf_index;
//! begin for k:=a to b do write(gf_file,gf_buf[k]);
//! end;
//!
//! @ To put a byte in the buffer without paying the cost of invoking a procedure
//! each time, we use the macro |gf_out|.
//!
//! @d gf_out(#)==@+begin gf_buf[gf_ptr]:=#; incr(gf_ptr);
//!   if gf_ptr=gf_limit then gf_swap;
//!   end
//!
//! @<Declare generic font output procedures@>=
//! procedure gf_swap; {outputs half of the buffer}
//! begin if gf_limit=gf_buf_size then
//!   begin write_gf(0,half_buf-1); gf_limit:=half_buf;
//!   gf_offset:=gf_offset+gf_buf_size; gf_ptr:=0;
//!   end
//! else  begin write_gf(half_buf,gf_buf_size-1); gf_limit:=gf_buf_size;
//!   end;
//! end;
//!
//! @ Here is how we clean out the buffer when \MF\ is all through; |gf_ptr|
//! will be a multiple of~4.
//!
//! @<Empty the last bytes out of |gf_buf|@>=
//! if gf_limit=half_buf then write_gf(half_buf,gf_buf_size-1);
//! if gf_ptr>0 then write_gf(0,gf_ptr-1)
//!
//! @ The |gf_four| procedure outputs four bytes in two's complement notation,
//! without risking arithmetic overflow.
//!
//! @<Declare generic font output procedures@>=
//! procedure gf_four(@!x:integer);
//! begin if x>=0 then gf_out(x div three_bytes)
//! else  begin x:=x+@'10000000000;
//!   x:=x+@'10000000000;
//!   gf_out((x div three_bytes) + 128);
//!   end;
//! x:=x mod three_bytes; gf_out(x div unity);
//! x:=x mod unity; gf_out(x div @'400);
//! gf_out(x mod @'400);
//! end;
//!
//! @ Of course, it's even easier to output just two or three bytes.
//!
//! @<Declare generic font output procedures@>=
//! procedure gf_two(@!x:integer);
//! begin gf_out(x div @'400); gf_out(x mod @'400);
//! end;
//! @#
//! procedure gf_three(@!x:integer);
//! begin gf_out(x div unity); gf_out((x mod unity) div @'400);
//! gf_out(x mod @'400);
//! end;
//!
//! @ We need a simple routine to generate a \\{paint}
//! command of the appropriate type.
//!
//! @<Declare generic font output procedures@>=
//! procedure gf_paint(@!d:integer); {here |0<=d<65536|}
//! begin if d<64 then gf_out(paint_0+d)
//! else if d<256 then
//!   begin gf_out(paint1); gf_out(d);
//!   end
//! else  begin gf_out(paint1+1); gf_two(d);
//!   end;
//! end;
//!
//! @ And |gf_string| outputs one or two strings. If the first string number
//! is nonzero, an \\{xxx} command is generated.
//!
//! @<Declare generic font output procedures@>=
//! procedure gf_string(@!s,@!t:str_number);
//! var @!k:pool_pointer;
//! @!l:integer; {length of the strings to output}
//! begin if s<>0 then
//!   begin l:=length(s);
//!   if t<>0 then l:=l+length(t);
//!   if l<=255 then
//!     begin gf_out(xxx1); gf_out(l);
//!     end
//!   else  begin gf_out(xxx3); gf_three(l);
//!     end;
//!   for k:=str_start[s] to str_start[s+1]-1 do gf_out(so(str_pool[k]));
//!   end;
//! if t<>0 then for k:=str_start[t] to str_start[t+1]-1 do gf_out(so(str_pool[k]));
//! end;
//!
//! @ The choice between |boc| commands is handled by |gf_boc|.
//!
//! @d one_byte(#)== #>=0 then if #<256
//!
//! @<Declare generic font output procedures@>=
//! procedure gf_boc(@!min_m,@!max_m,@!min_n,@!max_n:integer);
//! label exit;
//! begin if min_m<gf_min_m then gf_min_m:=min_m;
//! if max_n>gf_max_n then gf_max_n:=max_n;
//! if boc_p=-1 then if one_byte(boc_c) then
//!  if one_byte(max_m-min_m) then if one_byte(max_m) then
//!   if one_byte(max_n-min_n) then if one_byte(max_n) then
//!   begin gf_out(boc1); gf_out(boc_c);@/
//!   gf_out(max_m-min_m); gf_out(max_m);
//!   gf_out(max_n-min_n); gf_out(max_n); return;
//!   end;
//! gf_out(boc); gf_four(boc_c); gf_four(boc_p);@/
//! gf_four(min_m); gf_four(max_m); gf_four(min_n); gf_four(max_n);
//! exit: end;
//!
//! @ Two of the parameters to |gf_boc| are global.
//!
//! @<Glob...@>=
//! @!boc_c,@!boc_p:integer; {parameters of the next |boc| command}
//!
//! @ Here is a routine that gets a \.{GF} file off to a good start.
//!
//! @d check_gf==@t@>@+if output_file_name=0 then init_gf
//!
//! @<Declare generic font output procedures@>=
//! procedure init_gf;
//! var @!k:eight_bits; {runs through all possible character codes}
//! @!t:integer; {the time of this run}
//! begin gf_min_m:=4096; gf_max_m:=-4096; gf_min_n:=4096; gf_max_n:=-4096;
//! for k:=0 to 255 do char_ptr[k]:=-1;
//! @<Determine the file extension, |gf_ext|@>;
//! set_output_file_name;
//! gf_out(pre); gf_out(gf_id_byte); {begin to output the preamble}
//! old_setting:=selector; selector:=new_string; print(" METAFONT output ");
//! print_int(round_unscaled(internal[year])); print_char(".");
//! print_dd(round_unscaled(internal[month])); print_char(".");
//! print_dd(round_unscaled(internal[day])); print_char(":");@/
//! t:=round_unscaled(internal[time]);
//! print_dd(t div 60); print_dd(t mod 60);@/
//! selector:=old_setting; gf_out(cur_length);
//! gf_string(0,make_string); decr(str_ptr);
//! pool_ptr:=str_start[str_ptr]; {flush that string from memory}
//! gf_prev_ptr:=gf_offset+gf_ptr;
//! end;
//!
//! @ @<Determine the file extension...@>=
//! if internal[hppp]<=0 then gf_ext:=".gf"
//! else  begin old_setting:=selector; selector:=new_string; print_char(".");
//!   print_int(make_scaled(internal[hppp],59429463));
//!     {$2^{32}/72.27\approx59429463.07$}
//!   print("gf"); gf_ext:=make_string; selector:=old_setting;
//!   end
//!
//! @ With those preliminaries out of the way, |ship_out| is not especially
//! difficult.
//!
//! @<Declare generic font output procedures@>=
//! procedure ship_out(@!c:eight_bits);
//! label done;
//! var @!f:integer; {current character extension}
//! @!prev_m,@!m,@!mm:integer; {previous and current pixel column numbers}
//! @!prev_n,@!n:integer; {previous and current pixel row numbers}
//! @!p,@!q:pointer; {for list traversal}
//! @!prev_w,@!w,@!ww:integer; {old and new weights}
//! @!d:integer; {data from edge-weight node}
//! @!delta:integer; {number of rows to skip}
//! @!cur_min_m:integer; {starting column, relative to the current offset}
//! @!x_off,@!y_off:integer; {offsets, rounded to integers}
//! begin check_gf; f:=round_unscaled(internal[char_ext]);@/
//! x_off:=round_unscaled(internal[x_offset]);
//! y_off:=round_unscaled(internal[y_offset]);
//! if term_offset>max_print_line-9 then print_ln
//! else if (term_offset>0)or(file_offset>0) then print_char(" ");
//! print_char("["); print_int(c);
//! if f<>0 then
//!   begin print_char("."); print_int(f);
//!   end;
//! update_terminal;
//! boc_c:=256*f+c; boc_p:=char_ptr[c]; char_ptr[c]:=gf_prev_ptr;@/
//! if internal[proofing]>0 then @<Send nonzero offsets to the output file@>;
//! @<Output the character represented in |cur_edges|@>;
//! gf_out(eoc); gf_prev_ptr:=gf_offset+gf_ptr; incr(total_chars);
//! print_char("]"); update_terminal; {progress report}
//! if internal[tracing_output]>0 then
//!   print_edges(" (just shipped out)",true,x_off,y_off);
//! end;
//!
//! @ @<Send nonzero offsets to the output file@>=
//! begin if x_off<>0 then
//!   begin gf_string("xoffset",0); gf_out(yyy); gf_four(x_off*unity);
//!   end;
//! if y_off<>0 then
//!   begin gf_string("yoffset",0); gf_out(yyy); gf_four(y_off*unity);
//!   end;
//! end
//!
//! @ @<Output the character represented in |cur_edges|@>=
//! prev_n:=4096; p:=knil(cur_edges); n:=n_max(cur_edges)-zero_field;
//! while p<>cur_edges do
//!   begin @<Output the pixels of edge row |p| to font row |n|@>;
//!   p:=knil(p); decr(n);
//!   end;
//! if prev_n=4096 then @<Finish off an entirely blank character@>
//! else if prev_n+y_off<gf_min_n then
//!   gf_min_n:=prev_n+y_off
//!
//! @ @<Finish off an entirely blank...@>=
//! begin gf_boc(0,0,0,0);
//! if gf_max_m<0 then gf_max_m:=0;
//! if gf_min_n>0 then gf_min_n:=0;
//! end
//!
//! @ In this loop, |prev_w| represents the weight at column |prev_m|, which is
//! the most recent column reflected in the output so far; |w| represents the
//! weight at column~|m|, which is the most recent column in the edge data.
//! Several edges might cancel at the same column position, so we need to
//! look ahead to column~|mm| before actually outputting anything.
//!
//! @<Output the pixels of edge row |p| to font row |n|@>=
//! if unsorted(p)>void then sort_edges(p);
//! q:=sorted(p); w:=0; prev_m:=-fraction_one; {$|fraction_one|\approx\infty$}
//! ww:=0; prev_w:=0; m:=prev_m;
//! repeat if q=sentinel then mm:=fraction_one
//! else  begin d:=ho(info(q)); mm:=d div 8; ww:=ww+(d mod 8)-zero_w;
//!   end;
//! if mm<>m then
//!   begin if prev_w<=0 then
//!     begin if w>0 then @<Start black at $(m,n)$@>;
//!     end
//!   else if w<=0 then @<Stop black at $(m,n)$@>;
//!   m:=mm;
//!   end;
//! w:=ww; q:=link(q);
//! until mm=fraction_one;
//! if w<>0 then {this should be impossible}
//!   print_nl("(There's unbounded black in character shipped out!)");
//! @.There's unbounded black...@>
//! if prev_m-m_offset(cur_edges)+x_off>gf_max_m then
//!   gf_max_m:=prev_m-m_offset(cur_edges)+x_off
//!
//!
//! @ @<Start black at $(m,n)$@>=
//! begin if prev_m=-fraction_one then @<Start a new row at $(m,n)$@>
//! else gf_paint(m-prev_m);
//! prev_m:=m; prev_w:=w;
//! end
//!
//! @ @<Stop black at $(m,n)$@>=
//! begin gf_paint(m-prev_m); prev_m:=m; prev_w:=w;
//! end
//!
//! @ @<Start a new row at $(m,n)$@>=
//! begin if prev_n=4096 then
//!   begin gf_boc(m_min(cur_edges)+x_off-zero_field,
//!     m_max(cur_edges)+x_off-zero_field,@|
//!     n_min(cur_edges)+y_off-zero_field,n+y_off);
//!   cur_min_m:=m_min(cur_edges)-zero_field+m_offset(cur_edges);
//!   end
//! else if prev_n>n+1 then @<Skip down |prev_n-n| rows@>
//! else @<Skip to column $m$ in the next row and |goto done|, or skip zero rows@>;
//! gf_paint(m-cur_min_m); {skip to column $m$, painting white}
//! done:prev_n:=n;
//! end
//!
//! @ @<Skip to column $m$ in the next row...@>=
//! begin delta:=m-cur_min_m;
//! if delta>max_new_row then gf_out(skip0)
//! else  begin gf_out(new_row_0+delta); goto done;
//!   end;
//! end
//!
//! @ @<Skip down...@>=
//! begin delta:=prev_n-n-1;
//! if delta<@'400 then
//!   begin gf_out(skip1); gf_out(delta);
//!   end
//! else  begin gf_out(skip1+1); gf_two(delta);
//!   end;
//! end
//!
//! @ Now that we've finished |ship_out|, let's look at the other commands
//! by which a user can send things to the \.{GF} file.
//!
//! @<Cases of |do_statement|...@>=
//! special_command: do_special;
//!
//! @ @<Put each...@>=
//! primitive("special",special_command,string_type);@/
//! @!@:special_}{\&{special} primitive@>
//! primitive("numspecial",special_command,known);@/
//! @!@:num_special_}{\&{numspecial} primitive@>
//!
//! @ @<Declare action procedures for use by |do_statement|@>=
//! procedure do_special;
//! var @!m:small_number; {either |string_type| or |known|}
//! begin m:=cur_mod; get_x_next; scan_expression;
//! if internal[proofing]>=0 then
//!   if cur_type<>m then @<Complain about improper special operation@>
//!   else  begin check_gf;
//!     if m=string_type then gf_string(cur_exp,0)
//!     else  begin gf_out(yyy); gf_four(cur_exp);
//!       end;
//!     end;
//! flush_cur_exp(0);
//! end;
//!
//! @ @<Complain about improper special operation@>=
//! begin exp_err("Unsuitable expression");
//! @.Unsuitable expression@>
//! help1("The expression shown above has the wrong type to be output.");
//! put_get_error;
//! end
//!
//! @ @<Send the current expression as a title to the output file@>=
//! begin check_gf; gf_string("title ",cur_exp);
//! @.title@>
//! end
//!
//! @ @<Cases of |print_cmd...@>=
//! special_command:if m=known then print("numspecial")
//!   else print("special");
//!
//! @ @<Determine if a character has been shipped out@>=
//! begin cur_exp:=round_unscaled(cur_exp) mod 256;
//! if cur_exp<0 then cur_exp:=cur_exp+256;
//! boolean_reset(char_exists[cur_exp]); cur_type:=boolean_type;
//! end
//!
//! @ At the end of the program we must finish things off by writing the postamble.
//! The \.{TFM} information should have been computed first.
//!
//! An integer variable |k| and a |scaled| variable |x| will be declared for
//! use by this routine.
//!
//! @<Finish the \.{GF} file@>=
//! begin gf_out(post); {beginning of the postamble}
//! gf_four(gf_prev_ptr); gf_prev_ptr:=gf_offset+gf_ptr-5; {|post| location}
//! gf_four(internal[design_size]*16);
//! for k:=1 to 4 do gf_out(header_byte[k]); {the check sum}
//! gf_four(internal[hppp]);
//! gf_four(internal[vppp]);@/
//! gf_four(gf_min_m); gf_four(gf_max_m);
//! gf_four(gf_min_n); gf_four(gf_max_n);
//! for k:=0 to 255 do if char_exists[k] then
//!   begin x:=gf_dx[k] div unity;
//!   if (gf_dy[k]=0)and(x>=0)and(x<256)and(gf_dx[k]=x*unity) then
//!     begin gf_out(char_loc+1); gf_out(k); gf_out(x);
//!     end
//!   else  begin gf_out(char_loc); gf_out(k);
//!     gf_four(gf_dx[k]); gf_four(gf_dy[k]);
//!     end;
//!   x:=value(tfm_width[k]);
//!   if abs(x)>max_tfm_dimen then
//!     if x>0 then x:=three_bytes-1@+else x:=1-three_bytes
//!   else x:=make_scaled(x*16,internal[design_size]);
//!   gf_four(x); gf_four(char_ptr[k]);
//!   end;
//! gf_out(post_post); gf_four(gf_prev_ptr); gf_out(gf_id_byte);@/
//! k:=4+((gf_buf_size-gf_ptr) mod 4); {the number of 223's}
//! while k>0 do
//!   begin gf_out(223); decr(k);
//!   end;
//! @<Empty the last bytes out of |gf_buf|@>;
//! print_nl("Output written on "); slow_print(output_file_name);
//! @.Output written...@>
//! print(" ("); print_int(total_chars); print(" character");
//! if total_chars<>1 then print_char("s");
//! print(", "); print_int(gf_offset+gf_ptr); print(" bytes).");
//! b_close(gf_file);
//! end
//!
