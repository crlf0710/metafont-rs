//! @ @<Set init...@>=
//! next(1):=0; text(1):=0; eq_type(1):=tag_token; equiv(1):=null;
//! for k:=2 to hash_end do
//!   begin hash[k]:=hash[1]; eqtb[k]:=eqtb[1];
//!   end;
//!
//! @ @<Initialize table entries...@>=
//! hash_used:=frozen_inaccessible; {nothing is used}
//! st_count:=0;@/
//! text(frozen_bad_vardef):="a bad variable";
//! text(frozen_fi):="fi";
//! text(frozen_end_group):="endgroup";
//! text(frozen_end_def):="enddef";
//! text(frozen_end_for):="endfor";@/
//! text(frozen_semicolon):=";";
//! text(frozen_colon):=":";
//! text(frozen_slash):="/";
//! text(frozen_left_bracket):="[";
//! text(frozen_right_delimiter):=")";@/
//! text(frozen_inaccessible):=" INACCESSIBLE";@/
//! eq_type(frozen_right_delimiter):=right_delimiter;
//!
//! @ @<Check the ``constant'' values...@>=
//! if hash_end+max_internal>max_halfword then bad:=21;
//!
//! @ Here is the subroutine that searches the hash table for an identifier
//! that matches a given string of length~|l| appearing in |buffer[j..
//! (j+l-1)]|. If the identifier is not found, it is inserted; hence it
//! will always be found, and the corresponding hash table address
//! will be returned.
//!
//! @p function id_lookup(@!j,@!l:integer):pointer; {search the hash table}
//! label found; {go here when you've found it}
//! var @!h:integer; {hash code}
//! @!p:pointer; {index in |hash| array}
//! @!k:pointer; {index in |buffer| array}
//! begin if l=1 then @<Treat special case of length 1 and |goto found|@>;
//! @<Compute the hash code |h|@>;
//! p:=h+hash_base; {we start searching here; note that |0<=h<hash_prime|}
//! loop@+  begin if text(p)>0 then if length(text(p))=l then
//!     if str_eq_buf(text(p),j) then goto found;
//!   if next(p)=0 then
//!     @<Insert a new symbolic token after |p|, then
//!       make |p| point to it and |goto found|@>;
//!   p:=next(p);
//!   end;
//! found: id_lookup:=p;
//! end;
//!
//! @ @<Treat special case of length 1...@>=
//! begin p:=buffer[j]+1; text(p):=p-1; goto found;
//! end
//!
//! @ @<Insert a new symbolic...@>=
//! begin if text(p)>0 then
//!   begin repeat if hash_is_full then
//!     overflow("hash size",hash_size);
//! @:METAFONT capacity exceeded hash size}{\quad hash size@>
//!   decr(hash_used);
//!   until text(hash_used)=0; {search for an empty location in |hash|}
//!   next(p):=hash_used; p:=hash_used;
//!   end;
//! str_room(l);
//! for k:=j to j+l-1 do append_char(buffer[k]);
//! text(p):=make_string; str_ref[text(p)]:=max_str_ref;
//! @!stat incr(st_count);@+tats@;@/
//! goto found;
//! end
//!
//! @ The value of |hash_prime| should be roughly 85\pct! of |hash_size|, and it
//! should be a prime number.  The theory of hashing tells us to expect fewer
//! than two table probes, on the average, when the search is successful.
//! [See J.~S. Vitter, {\sl Journal of the ACM\/ \bf30} (1983), 231--258.]
//! @^Vitter, Jeffrey Scott@>
//!
//! @<Compute the hash code |h|@>=
//! h:=buffer[j];
//! for k:=j+1 to j+l-1 do
//!   begin h:=h+h+buffer[k];
//!   while h>=hash_prime do h:=h-hash_prime;
//!   end
//!
//! @ @<Search |eqtb| for equivalents equal to |p|@>=
//! for q:=1 to hash_end do
//!   begin if equiv(q)=p then
//!     begin print_nl("EQUIV("); print_int(q); print_char(")");
//!     end;
//!   end
//!
//! @ We need to put \MF's ``primitive'' symbolic tokens into the hash
//! table, together with their command code (which will be the |eq_type|)
//! and an operand (which will be the |equiv|). The |primitive| procedure
//! does this, in a way that no \MF\ user can. The global value |cur_sym|
//! contains the new |eqtb| pointer after |primitive| has acted.
//!
//! @p @!init procedure primitive(@!s:str_number;@!c:halfword;@!o:halfword);
//! var @!k:pool_pointer; {index into |str_pool|}
//! @!j:small_number; {index into |buffer|}
//! @!l:small_number; {length of the string}
//! begin k:=str_start[s]; l:=str_start[s+1]-k;
//!   {we will move |s| into the (empty) |buffer|}
//! for j:=0 to l-1 do buffer[j]:=so(str_pool[k+j]);
//! cur_sym:=id_lookup(0,l);@/
//! if s>=256 then {we don't want to have the string twice}
//!   begin flush_string(str_ptr-1); text(cur_sym):=s;
//!   end;
//! eq_type(cur_sym):=c; equiv(cur_sym):=o;
//! end;
//! tini
//!
//! @ Many of \MF's primitives need no |equiv|, since they are identifiable
//! by their |eq_type| alone. These primitives are loaded into the hash table
//! as follows:
//!
//! @<Put each of \MF's primitives into the hash table@>=
//! primitive("..",path_join,0);@/
//! @!@:.._}{\.{..} primitive@>
//! primitive("[",left_bracket,0); eqtb[frozen_left_bracket]:=eqtb[cur_sym];@/
//! @!@:[ }{\.{[} primitive@>
//! primitive("]",right_bracket,0);@/
//! @!@:] }{\.{]} primitive@>
//! primitive("}",right_brace,0);@/
//! @!@:]]}{\.{\char`\}} primitive@>
//! primitive("{",left_brace,0);@/
//! @!@:][}{\.{\char`\{} primitive@>
//! primitive(":",colon,0); eqtb[frozen_colon]:=eqtb[cur_sym];@/
//! @!@:: }{\.{:} primitive@>
//! primitive("::",double_colon,0);@/
//! @!@::: }{\.{::} primitive@>
//! primitive("||:",bchar_label,0);@/
//! @!@:::: }{\.{\char'174\char'174:} primitive@>
//! primitive(":=",assignment,0);@/
//! @!@::=_}{\.{:=} primitive@>
//! primitive(",",comma,0);@/
//! @!@:, }{\., primitive@>
//! primitive(";",semicolon,0); eqtb[frozen_semicolon]:=eqtb[cur_sym];@/
//! @!@:; }{\.; primitive@>
//! primitive("\",relax,0);@/
//! @!@:]]\\}{\.{\char`\\} primitive@>
//! @#
//! primitive("addto",add_to_command,0);@/
//! @!@:add_to_}{\&{addto} primitive@>
//! primitive("at",at_token,0);@/
//! @!@:at_}{\&{at} primitive@>
//! primitive("atleast",at_least,0);@/
//! @!@:at_least_}{\&{atleast} primitive@>
//! primitive("begingroup",begin_group,0); bg_loc:=cur_sym;@/
//! @!@:begin_group_}{\&{begingroup} primitive@>
//! primitive("controls",controls,0);@/
//! @!@:controls_}{\&{controls} primitive@>
//! primitive("cull",cull_command,0);@/
//! @!@:cull_}{\&{cull} primitive@>
//! primitive("curl",curl_command,0);@/
//! @!@:curl_}{\&{curl} primitive@>
//! primitive("delimiters",delimiters,0);@/
//! @!@:delimiters_}{\&{delimiters} primitive@>
//! primitive("display",display_command,0);@/
//! @!@:display_}{\&{display} primitive@>
//! primitive("endgroup",end_group,0);
//!  eqtb[frozen_end_group]:=eqtb[cur_sym]; eg_loc:=cur_sym;@/
//! @!@:endgroup_}{\&{endgroup} primitive@>
//! primitive("everyjob",every_job_command,0);@/
//! @!@:every_job_}{\&{everyjob} primitive@>
//! primitive("exitif",exit_test,0);@/
//! @!@:exit_if_}{\&{exitif} primitive@>
//! primitive("expandafter",expand_after,0);@/
//! @!@:expand_after_}{\&{expandafter} primitive@>
//! primitive("from",from_token,0);@/
//! @!@:from_}{\&{from} primitive@>
//! primitive("inwindow",in_window,0);@/
//! @!@:in_window_}{\&{inwindow} primitive@>
//! primitive("interim",interim_command,0);@/
//! @!@:interim_}{\&{interim} primitive@>
//! primitive("let",let_command,0);@/
//! @!@:let_}{\&{let} primitive@>
//! primitive("newinternal",new_internal,0);@/
//! @!@:new_internal_}{\&{newinternal} primitive@>
//! primitive("of",of_token,0);@/
//! @!@:of_}{\&{of} primitive@>
//! primitive("openwindow",open_window,0);@/
//! @!@:open_window_}{\&{openwindow} primitive@>
//! primitive("randomseed",random_seed,0);@/
//! @!@:random_seed_}{\&{randomseed} primitive@>
//! primitive("save",save_command,0);@/
//! @!@:save_}{\&{save} primitive@>
//! primitive("scantokens",scan_tokens,0);@/
//! @!@:scan_tokens_}{\&{scantokens} primitive@>
//! primitive("shipout",ship_out_command,0);@/
//! @!@:ship_out_}{\&{shipout} primitive@>
//! primitive("skipto",skip_to,0);@/
//! @!@:skip_to_}{\&{skipto} primitive@>
//! primitive("step",step_token,0);@/
//! @!@:step_}{\&{step} primitive@>
//! primitive("str",str_op,0);@/
//! @!@:str_}{\&{str} primitive@>
//! primitive("tension",tension,0);@/
//! @!@:tension_}{\&{tension} primitive@>
//! primitive("to",to_token,0);@/
//! @!@:to_}{\&{to} primitive@>
//! primitive("until",until_token,0);@/
//! @!@:until_}{\&{until} primitive@>
//!
//! @ Each primitive has a corresponding inverse, so that it is possible to
//! display the cryptic numeric contents of |eqtb| in symbolic form.
//! Every call of |primitive| in this program is therefore accompanied by some
//! straightforward code that forms part of the |print_cmd_mod| routine
//! explained below.
//!
//! @<Cases of |print_cmd_mod| for symbolic printing of primitives@>=
//! add_to_command:print("addto");
//! assignment:print(":=");
//! at_least:print("atleast");
//! at_token:print("at");
//! bchar_label:print("||:");
//! begin_group:print("begingroup");
//! colon:print(":");
//! comma:print(",");
//! controls:print("controls");
//! cull_command:print("cull");
//! curl_command:print("curl");
//! delimiters:print("delimiters");
//! display_command:print("display");
//! double_colon:print("::");
//! end_group:print("endgroup");
//! every_job_command:print("everyjob");
//! exit_test:print("exitif");
//! expand_after:print("expandafter");
//! from_token:print("from");
//! in_window:print("inwindow");
//! interim_command:print("interim");
//! left_brace:print("{");
//! left_bracket:print("[");
//! let_command:print("let");
//! new_internal:print("newinternal");
//! of_token:print("of");
//! open_window:print("openwindow");
//! path_join:print("..");
//! random_seed:print("randomseed");
//! relax:print_char("\");
//! right_brace:print("}");
//! right_bracket:print("]");
//! save_command:print("save");
//! scan_tokens:print("scantokens");
//! semicolon:print(";");
//! ship_out_command:print("shipout");
//! skip_to:print("skipto");
//! step_token:print("step");
//! str_op:print("str");
//! tension:print("tension");
//! to_token:print("to");
//! until_token:print("until");
//!
//! @ We will deal with the other primitives later, at some point in the program
//! where their |eq_type| and |equiv| values are more meaningful.  For example,
//! the primitives for macro definitions will be loaded when we consider the
//! routines that define macros.
//! It is easy to find where each particular
//! primitive was treated by looking in the index at the end; for example, the
//! section where |"def"| entered |eqtb| is listed under `\&{def} primitive'.
//!
