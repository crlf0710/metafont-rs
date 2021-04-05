//! @ Here now is the general |error| routine.
//!
//! @<Error hand...@>=
//! procedure error; {completes the job of error reporting}
//! label continue,exit;
//! var @!c:ASCII_code; {what the user types}
//! @!s1,@!s2,@!s3:integer; {used to save global variables when deleting tokens}
//! @!j:pool_pointer; {character position being printed}
//! begin if history<error_message_issued then history:=error_message_issued;
//! print_char("."); show_context;
//! if interaction=error_stop_mode then @<Get user's advice and |return|@>;
//! incr(error_count);
//! if error_count=100 then
//!   begin print_nl("(That makes 100 errors; please try again.)");
//! @.That makes 100 errors...@>
//!   history:=fatal_error_stop; jump_out;
//!   end;
//! @<Put help message on the transcript file@>;
//! exit:end;
//!
//! @ @<Get user's advice...@>=
//! loop@+begin continue: if interaction<>error_stop_mode then return;
//!   clear_for_error_prompt; prompt_input("? ");
//! @.?\relax@>
//!   if last=first then return;
//!   c:=buffer[first];
//!   if c>="a" then c:=c+"A"-"a"; {convert to uppercase}
//!   @<Interpret code |c| and |return| if done@>;
//!   end
//!
//! @ It is desirable to provide an `\.E' option here that gives the user
//! an easy way to return from \MF\ to the system editor, with the offending
//! line ready to be edited. But such an extension requires some system
//! wizardry, so the present implementation simply types out the name of the
//! file that should be
//! edited and the relevant line number.
//! @^system dependencies@>
//!
//! There is a secret `\.D' option available when the debugging routines haven't
//! been commented~out.
//! @^debugging@>
//!
//! @<Interpret code |c| and |return| if done@>=
//! case c of
//! "0","1","2","3","4","5","6","7","8","9": if deletions_allowed then
//!   @<Delete |c-"0"| tokens and |goto continue|@>;
//! @t\4\4@>@;@+@!debug "D":begin debug_help;goto continue;@+end;@+gubed@/
//! "E": if file_ptr>0 then if input_stack[file_ptr].name_field>=256 then
//!   begin print_nl("You want to edit file ");
//! @.You want to edit file x@>
//!   slow_print(input_stack[file_ptr].name_field);
//!   print(" at line "); print_int(line);@/
//!   interaction:=scroll_mode; jump_out;
//!   end;
//! "H": @<Print the help information and |goto continue|@>;
//! "I":@<Introduce new material from the terminal and |return|@>;
//! "Q","R","S":@<Change the interaction level and |return|@>;
//! "X":begin interaction:=scroll_mode; jump_out;
//!   end;
//! othercases do_nothing
//! endcases;@/
//! @<Print the menu of available options@>
//!
//! @ @<Print the menu...@>=
//! begin print("Type <return> to proceed, S to scroll future error messages,");@/
//! @.Type <return> to proceed...@>
//! print_nl("R to run without stopping, Q to run quietly,");@/
//! print_nl("I to insert something, ");
//! if file_ptr>0 then if input_stack[file_ptr].name_field>=256 then
//!   print("E to edit your file,");
//! if deletions_allowed then
//!   print_nl("1 or ... or 9 to ignore the next 1 to 9 tokens of input,");
//! print_nl("H for help, X to quit.");
//! end
//!
//! @ Here the author of \MF\ apologizes for making use of the numerical
//! relation between |"Q"|, |"R"|, |"S"|, and the desired interaction settings
//! |batch_mode|, |nonstop_mode|, |scroll_mode|.
//! @^Knuth, Donald Ervin@>
//!
//! @<Change the interaction...@>=
//! begin error_count:=0; interaction:=batch_mode+c-"Q";
//! print("OK, entering ");
//! case c of
//! "Q":begin print("batchmode"); decr(selector);
//!   end;
//! "R":print("nonstopmode");
//! "S":print("scrollmode");
//! end; {there are no other cases}
//! print("..."); print_ln; update_terminal; return;
//! end
//!
//! @ When the following code is executed, |buffer[(first+1)..(last-1)]| may
//! contain the material inserted by the user; otherwise another prompt will
//! be given. In order to understand this part of the program fully, you need
//! to be familiar with \MF's input stacks.
//!
//! @<Introduce new material...@>=
//! begin begin_file_reading; {enter a new syntactic level for terminal input}
//! if last>first+1 then
//!   begin loc:=first+1; buffer[first]:=" ";
//!   end
//! else  begin prompt_input("insert>"); loc:=first;
//! @.insert>@>
//!   end;
//! first:=last+1; cur_input.limit_field:=last; return;
//! end
//!
//! @ We allow deletion of up to 99 tokens at a time.
//!
//! @<Delete |c-"0"| tokens...@>=
//! begin s1:=cur_cmd; s2:=cur_mod; s3:=cur_sym; OK_to_interrupt:=false;
//! if (last>first+1) and (buffer[first+1]>="0")and(buffer[first+1]<="9") then
//!   c:=c*10+buffer[first+1]-"0"*11
//! else c:=c-"0";
//! while c>0 do
//!   begin get_next; {one-level recursive call of |error| is possible}
//!   @<Decrease the string reference count, if the current token is a string@>;
//!   decr(c);
//!   end;
//! cur_cmd:=s1; cur_mod:=s2; cur_sym:=s3; OK_to_interrupt:=true;
//! help2("I have just deleted some text, as you asked.")@/
//! ("You can now delete more, or insert, or whatever.");
//! show_context; goto continue;
//! end
//!
//! @ @<Print the help info...@>=
//! begin if use_err_help then
//!   begin @<Print the string |err_help|, possibly on several lines@>;
//!   use_err_help:=false;
//!   end
//! else  begin if help_ptr=0 then
//!     help2("Sorry, I don't know how to help in this situation.")@/
//!     @t\kern1em@>("Maybe you should try asking a human?");
//!   repeat decr(help_ptr); print(help_line[help_ptr]); print_ln;
//!   until help_ptr=0;
//!   end;
//! help4("Sorry, I already gave what help I could...")@/
//!   ("Maybe you should try asking a human?")@/
//!   ("An error might have occurred before I noticed any problems.")@/
//!   ("``If all else fails, read the instructions.''");@/
//! goto continue;
//! end
//!
//! @ @<Print the string |err_help|, possibly on several lines@>=
//! j:=str_start[err_help];
//! while j<str_start[err_help+1] do
//!   begin if str_pool[j]<>si("%") then print(so(str_pool[j]))
//!   else if j+1=str_start[err_help+1] then print_ln
//!   else if str_pool[j+1]<>si("%") then print_ln
//!   else  begin incr(j); print_char("%");
//!     end;
//!   incr(j);
//!   end
//!
//! @ @<Put help message on the transcript file@>=
//! if interaction>batch_mode then decr(selector); {avoid terminal output}
//! if use_err_help then
//!   begin print_nl("");
//!   @<Print the string |err_help|, possibly on several lines@>;
//!   end
//! else while help_ptr>0 do
//!   begin decr(help_ptr); print_nl(help_line[help_ptr]);
//!   end;
//! print_ln;
//! if interaction>batch_mode then incr(selector); {re-enable terminal output}
//! print_ln
//!
//! @ In anomalous cases, the print selector might be in an unknown state;
//! the following subroutine is called to fix things just enough to keep
//! running a bit longer.
//!
//! @p procedure normalize_selector;
//! begin if log_opened then selector:=term_and_log
//! else selector:=term_only;
//! if job_name=0 then open_log_file;
//! if interaction=batch_mode then decr(selector);
//! end;
//!
//! @ The following procedure prints \MF's last words before dying.
//!
//! @d succumb==begin if interaction=error_stop_mode then
//!     interaction:=scroll_mode; {no more interaction}
//!   if log_opened then error;
//!   @!debug if interaction>batch_mode then debug_help;@;@+gubed@;@/
//!   history:=fatal_error_stop; jump_out; {irrecoverable error}
//!   end
//!
//! @<Error hand...@>=
//! procedure fatal_error(@!s:str_number); {prints |s|, and that's it}
//! begin normalize_selector;@/
//! print_err("Emergency stop"); help1(s); succumb;
//! @.Emergency stop@>
//! end;
//!
//! @ Here is the most dreaded error message.
//!
//! @<Error hand...@>=
//! procedure overflow(@!s:str_number;@!n:integer); {stop due to finiteness}
//! begin normalize_selector;
//! print_err("METAFONT capacity exceeded, sorry [");
//! @.METAFONT capacity exceeded ...@>
//! print(s); print_char("="); print_int(n); print_char("]");
//! help2("If you really absolutely need more capacity,")@/
//!   ("you can ask a wizard to enlarge me.");
//! succumb;
//! end;
//!
//! @ The program might sometime run completely amok, at which point there is
//! no choice but to stop. If no previous error has been detected, that's bad
//! news; a message is printed that is really intended for the \MF\
//! maintenance person instead of the user (unless the user has been
//! particularly diabolical).  The index entries for `this can't happen' may
//! help to pinpoint the problem.
//! @^dry rot@>
//!
//! @<Error hand...@>=
//! procedure confusion(@!s:str_number);
//!   {consistency check violated; |s| tells where}
//! begin normalize_selector;
//! if history<error_message_issued then
//!   begin print_err("This can't happen ("); print(s); print_char(")");
//! @.This can't happen@>
//!   help1("I'm broken. Please show this to someone who can fix can fix");
//!   end
//! else  begin print_err("I can't go on meeting you like this");
//! @.I can't go on...@>
//!   help2("One of your faux pas seems to have wounded me deeply...")@/
//!     ("in fact, I'm barely conscious. Please fix it and try again.");
//!   end;
//! succumb;
//! end;
//!
//! @ Users occasionally want to interrupt \MF\ while it's running.
//! If the \PASCAL\ runtime system allows this, one can implement
//! a routine that sets the global variable |interrupt| to some nonzero value
//! when such an interrupt is signalled. Otherwise there is probably at least
//! a way to make |interrupt| nonzero using the \PASCAL\ debugger.
//! @^system dependencies@>
//! @^debugging@>
//!
//! @d check_interrupt==begin if interrupt<>0 then pause_for_instructions;
//!   end
//!
//! @<Global...@>=
//! @!interrupt:integer; {should \MF\ pause for instructions?}
//! @!OK_to_interrupt:boolean; {should interrupts be observed?}
//!
//! @ @<Set init...@>=
//! interrupt:=0; OK_to_interrupt:=true;
//!
//! @ When an interrupt has been detected, the program goes into its
//! highest interaction level and lets the user have the full flexibility of
//! the |error| routine.  \MF\ checks for interrupts only at times when it is
//! safe to do this.
//!
//! @p procedure pause_for_instructions;
//! begin if OK_to_interrupt then
//!   begin interaction:=error_stop_mode;
//!   if (selector=log_only)or(selector=no_print) then
//!     incr(selector);
//!   print_err("Interruption");
//! @.Interruption@>
//!   help3("You rang?")@/
//!   ("Try to insert an instruction for me (e.g., `I show x;'),")@/
//!   ("unless you just want to quit by typing `X'.");
//!   deletions_allowed:=false; error; deletions_allowed:=true;
//!   interrupt:=0;
//!   end;
//! end;
//!
//! @ Many of \MF's error messages state that a missing token has been
//! inserted behind the scenes. We can save string space and program space
//! by putting this common code into a subroutine.
//!
//! @p procedure missing_err(@!s:str_number);
//! begin print_err("Missing `"); print(s); print("' has been inserted");
//! @.Missing...inserted@>
//! end;
//!
//! @* \[7] Arithmetic with scaled numbers.
//! The principal computations performed by \MF\ are done entirely in terms of
//! integers less than $2^{31}$ in magnitude; thus, the arithmetic specified in this
//! program can be carried out in exactly the same way on a wide variety of
//! computers, including some small ones.
//! @^small computers@>
//!
//! But \PASCAL\ does not define the @!|div|
//! operation in the case of negative dividends; for example, the result of
//! |(-2*n-1) div 2| is |-(n+1)| on some computers and |-n| on others.
//! There are two principal types of arithmetic: ``translation-preserving,''
//! in which the identity |(a+q*b)div b=(a div b)+q| is valid; and
//! ``negation-preserving,'' in which |(-a)div b=-(a div b)|. This leads to
//! two \MF s, which can produce different results, although the differences
//! should be negligible when the language is being used properly.
//! The \TeX\ processor has been defined carefully so that both varieties
//! of arithmetic will produce identical output, but it would be too
//! inefficient to constrain \MF\ in a similar way.
//!
//! @d el_gordo == @'17777777777 {$2^{31}-1$, the largest value that \MF\ likes}
//!
//! @ One of \MF's most common operations is the calculation of
//! $\lfloor{a+b\over2}\rfloor$,
//! the midpoint of two given integers |a| and~|b|. The only decent way to do
//! this in \PASCAL\ is to write `|(a+b) div 2|'; but on most machines it is
//! far more efficient to calculate `|(a+b)| right shifted one bit'.
//!
//! Therefore the midpoint operation will always be denoted by `|half(a+b)|'
//! in this program. If \MF\ is being implemented with languages that permit
//! binary shifting, the |half| macro should be changed to make this operation
//! as efficient as possible.
//!
//! @d half(#)==(#) div 2
//!
//! @ A single computation might use several subroutine calls, and it is
//! desirable to avoid producing multiple error messages in case of arithmetic
//! overflow. So the routines below set the global variable |arith_error| to |true|
//! instead of reporting errors directly to the user.
//! @^overflow in arithmetic@>
//!
//! @<Glob...@>=
//! @!arith_error:boolean; {has arithmetic overflow occurred recently?}
//!
//! @ @<Set init...@>=
//! arith_error:=false;
//!
//! @ At crucial points the program will say |check_arith|, to test if
//! an arithmetic error has been detected.
//!
//! @d check_arith==begin if arith_error then clear_arith;@+end
//!
//! @p procedure clear_arith;
//! begin print_err("Arithmetic overflow");
//! @.Arithmetic overflow@>
//! help4("Uh, oh. A little while ago one of the quantities that I was")@/
//!   ("computing got too large, so I'm afraid your answers will be")@/
//!   ("somewhat askew. You'll probably have to adopt different")@/
//!   ("tactics next time. But I shall try to carry on anyway.");
//! error; arith_error:=false;
//! end;
//!
//! @ Addition is not always checked to make sure that it doesn't overflow,
//! but in places where overflow isn't too unlikely the |slow_add| routine
//! is used.
//!
//! @p function slow_add(@!x,@!y:integer):integer;
//! begin if x>=0 then
//!   if y<=el_gordo-x then slow_add:=x+y
//!   else  begin arith_error:=true; slow_add:=el_gordo;
//!     end
//! else  if -y<=el_gordo+x then slow_add:=x+y
//!   else  begin arith_error:=true; slow_add:=-el_gordo;
//!     end;
//! end;
//!
//! @ Fixed-point arithmetic is done on {\sl scaled integers\/} that are multiples
//! of $2^{-16}$. In other words, a binary point is assumed to be sixteen bit
//! positions from the right end of a binary computer word.
//!
//! @d quarter_unit == @'40000 {$2^{14}$, represents 0.250000}
//! @d half_unit == @'100000 {$2^{15}$, represents 0.50000}
//! @d three_quarter_unit == @'140000 {$3\cdot2^{14}$, represents 0.75000}
//! @d unity == @'200000 {$2^{16}$, represents 1.00000}
//! @d two == @'400000 {$2^{17}$, represents 2.00000}
//! @d three == @'600000 {$2^{17}+2^{16}$, represents 3.00000}
//!
//! @<Types...@>=
//! @!scaled = integer; {this type is used for scaled integers}
//! @!small_number=0..63; {this type is self-explanatory}
//!
//! @ The following function is used to create a scaled integer from a given decimal
//! fraction $(.d_0d_1\ldots d_{k-1})$, where |0<=k<=17|. The digit $d_i$ is
//! given in |dig[i]|, and the calculation produces a correctly rounded result.
//!
//! @p function round_decimals(@!k:small_number) : scaled;
//!   {converts a decimal fraction}
//! var @!a:integer; {the accumulator}
//! begin a:=0;
//! while k>0 do
//!   begin decr(k); a:=(a+dig[k]*two) div 10;
//!   end;
//! round_decimals:=half(a+1);
//! end;
//!
//! @ Conversely, here is a procedure analogous to |print_int|. If the output
//! of this procedure is subsequently read by \MF\ and converted by the
//! |round_decimals| routine above, it turns out that the original value will
//! be reproduced exactly. A decimal point is printed only if the value is
//! not an integer. If there is more than one way to print the result with
//! the optimum number of digits following the decimal point, the closest
//! possible value is given.
//!
//! The invariant relation in the \&{repeat} loop is that a sequence of
//! decimal digits yet to be printed will yield the original number if and only if
//! they form a fraction~$f$ in the range $s-\delta\L10\cdot2^{16}f<s$.
//! We can stop if and only if $f=0$ satisfies this condition; the loop will
//! terminate before $s$ can possibly become zero.
//!
//! @<Basic printing...@>=
//! procedure print_scaled(@!s:scaled); {prints scaled real, rounded to five
//!   digits}
//! var @!delta:scaled; {amount of allowable inaccuracy}
//! begin if s<0 then
//!   begin print_char("-"); negate(s); {print the sign, if negative}
//!   end;
//! print_int(s div unity); {print the integer part}
//! s:=10*(s mod unity)+5;
//! if s<>5 then
//!   begin delta:=10; print_char(".");
//!   repeat if delta>unity then
//!     s:=s+@'100000-(delta div 2); {round the final digit}
//!   print_char("0"+(s div unity)); s:=10*(s mod unity); delta:=delta*10;
//!   until s<=delta;
//!   end;
//! end;
//!
//! @ We often want to print two scaled quantities in parentheses,
//! separated by a comma.
//!
//! @<Basic printing...@>=
//! procedure print_two(@!x,@!y:scaled); {prints `|(x,y)|'}
//! begin print_char("("); print_scaled(x); print_char(","); print_scaled(y);
//! print_char(")");
//! end;
//!
//! @ The |scaled| quantities in \MF\ programs are generally supposed to be
//! less than $2^{12}$ in absolute value, so \MF\ does much of its internal
//! arithmetic with 28~significant bits of precision. A |fraction| denotes
//! a scaled integer whose binary point is assumed to be 28 bit positions
//! from the right.
//!
//! @d fraction_half==@'1000000000 {$2^{27}$, represents 0.50000000}
//! @d fraction_one==@'2000000000 {$2^{28}$, represents 1.00000000}
//! @d fraction_two==@'4000000000 {$2^{29}$, represents 2.00000000}
//! @d fraction_three==@'6000000000 {$3\cdot2^{28}$, represents 3.00000000}
//! @d fraction_four==@'10000000000 {$2^{30}$, represents 4.00000000}
//!
//! @<Types...@>=
//! @!fraction=integer; {this type is used for scaled fractions}
//!
//! @ In fact, the two sorts of scaling discussed above aren't quite
//! sufficient; \MF\ has yet another, used internally to keep track of angles
//! in units of $2^{-20}$ degrees.
//!
//! @d forty_five_deg==@'264000000 {$45\cdot2^{20}$, represents $45^\circ$}
//! @d ninety_deg==@'550000000 {$90\cdot2^{20}$, represents $90^\circ$}
//! @d one_eighty_deg==@'1320000000 {$180\cdot2^{20}$, represents $180^\circ$}
//! @d three_sixty_deg==@'2640000000 {$360\cdot2^{20}$, represents $360^\circ$}
//!
//! @<Types...@>=
//! @!angle=integer; {this type is used for scaled angles}
//!
//! @ The |make_fraction| routine produces the |fraction| equivalent of
//! |p/q|, given integers |p| and~|q|; it computes the integer
//! $f=\lfloor2^{28}p/q+{1\over2}\rfloor$, when $p$ and $q$ are
//! positive. If |p| and |q| are both of the same scaled type |t|,
//! the ``type relation'' |make_fraction(t,t)=fraction| is valid;
//! and it's also possible to use the subroutine ``backwards,'' using
//! the relation |make_fraction(t,fraction)=t| between scaled types.
//!
//! If the result would have magnitude $2^{31}$ or more, |make_fraction|
//! sets |arith_error:=true|. Most of \MF's internal computations have
//! been designed to avoid this sort of error.
//!
//! Notice that if 64-bit integer arithmetic were available,
//! we could simply compute |@t$(2^{29}$@>*p+q)div (2*q)|.
//! But when we are restricted to \PASCAL's 32-bit arithmetic we
//! must either resort to multiple-precision maneuvering
//! or use a simple but slow iteration. The multiple-precision technique
//! would be about three times faster than the code adopted here, but it
//! would be comparatively long and tricky, involving about sixteen
//! additional multiplications and divisions.
//!
//! This operation is part of \MF's ``inner loop''; indeed, it will
//! consume nearly 10\pct! of the running time (exclusive of input and output)
//! if the code below is left unchanged. A machine-dependent recoding
//! will therefore make \MF\ run faster. The present implementation
//! is highly portable, but slow; it avoids multiplication and division
//! except in the initial stage. System wizards should be careful to
//! replace it with a routine that is guaranteed to produce identical
//! results in all cases.
//! @^system dependencies@>
//!
//! As noted below, a few more routines should also be replaced by machine-dependent
//! code, for efficiency. But when a procedure is not part of the ``inner loop,''
//! such changes aren't advisable; simplicity and robustness are
//! preferable to trickery, unless the cost is too high.
//! @^inner loop@>
//!
//! @p function make_fraction(@!p,@!q:integer):fraction;
//! var @!f:integer; {the fraction bits, with a leading 1 bit}
//! @!n:integer; {the integer part of $\vert p/q\vert$}
//! @!negative:boolean; {should the result be negated?}
//! @!be_careful:integer; {disables certain compiler optimizations}
//! begin if p>=0 then negative:=false
//! else  begin negate(p); negative:=true;
//!   end;
//! if q<=0 then
//!   begin debug if q=0 then confusion("/");@;@+gubed@;@/
//! @:this can't happen /}{\quad \./@>
//!   negate(q); negative:=not negative;
//!   end;
//! n:=p div q; p:=p mod q;
//! if n>=8 then
//!   begin arith_error:=true;
//!   if negative then make_fraction:=-el_gordo@+else make_fraction:=el_gordo;
//!   end
//! else  begin n:=(n-1)*fraction_one;
//!   @<Compute $f=\lfloor 2^{28}(1+p/q)+{1\over2}\rfloor$@>;
//!   if negative then make_fraction:=-(f+n)@+else make_fraction:=f+n;
//!   end;
//! end;
//!
//! @ The |repeat| loop here preserves the following invariant relations
//! between |f|, |p|, and~|q|:
//! (i)~|0<=p<q|; (ii)~$fq+p=2^k(q+p_0)$, where $k$ is an integer and
//! $p_0$ is the original value of~$p$.
//!
//! Notice that the computation specifies
//! |(p-q)+p| instead of |(p+p)-q|, because the latter could overflow.
//! Let us hope that optimizing compilers do not miss this point; a
//! special variable |be_careful| is used to emphasize the necessary
//! order of computation. Optimizing compilers should keep |be_careful|
//! in a register, not store it in memory.
//! @^inner loop@>
//!
//! @<Compute $f=\lfloor 2^{28}(1+p/q)+{1\over2}\rfloor$@>=
//! f:=1;
//! repeat be_careful:=p-q; p:=be_careful+p;
//! if p>=0 then f:=f+f+1
//! else  begin double(f); p:=p+q;
//!   end;
//! until f>=fraction_one;
//! be_careful:=p-q;
//! if be_careful+p>=0 then incr(f)
//!
//! @ The dual of |make_fraction| is |take_fraction|, which multiplies a
//! given integer~|q| by a fraction~|f|. When the operands are positive, it
//! computes $p=\lfloor qf/2^{28}+{1\over2}\rfloor$, a symmetric function
//! of |q| and~|f|.
//!
//! This routine is even more ``inner loopy'' than |make_fraction|;
//! the present implementation consumes almost 20\pct! of \MF's computation
//! time during typical jobs, so a machine-language or 64-bit
//! substitute is advisable.
//! @^inner loop@> @^system dependencies@>
//!
//! @p function take_fraction(@!q:integer;@!f:fraction):integer;
//! var @!p:integer; {the fraction so far}
//! @!negative:boolean; {should the result be negated?}
//! @!n:integer; {additional multiple of $q$}
//! @!be_careful:integer; {disables certain compiler optimizations}
//! begin @<Reduce to the case that |f>=0| and |q>=0|@>;
//! if f<fraction_one then n:=0
//! else  begin n:=f div fraction_one; f:=f mod fraction_one;
//!   if q<=el_gordo div n then n:=n*q
//!   else  begin arith_error:=true; n:=el_gordo;
//!     end;
//!   end;
//! f:=f+fraction_one;
//! @<Compute $p=\lfloor qf/2^{28}+{1\over2}\rfloor-q$@>;
//! be_careful:=n-el_gordo;
//! if be_careful+p>0 then
//!   begin arith_error:=true; n:=el_gordo-p;
//!   end;
//! if negative then take_fraction:=-(n+p)
//! else take_fraction:=n+p;
//! end;
//!
//! @ @<Reduce to the case that |f>=0| and |q>=0|@>=
//! if f>=0 then negative:=false
//! else  begin negate(f); negative:=true;
//!   end;
//! if q<0 then
//!   begin negate(q); negative:=not negative;
//!   end;
//!
//! @ The invariant relations in this case are (i)~$\lfloor(qf+p)/2^k\rfloor
//! =\lfloor qf_0/2^{28}+{1\over2}\rfloor$, where $k$ is an integer and
//! $f_0$ is the original value of~$f$; (ii)~$2^k\L f<2^{k+1}$.
//! @^inner loop@>
//!
//! @<Compute $p=\lfloor qf/2^{28}+{1\over2}\rfloor-q$@>=
//! p:=fraction_half; {that's $2^{27}$; the invariants hold now with $k=28$}
//! if q<fraction_four then
//!   repeat if odd(f) then p:=half(p+q)@+else p:=half(p);
//!   f:=half(f);
//!   until f=1
//! else  repeat if odd(f) then p:=p+half(q-p)@+else p:=half(p);
//!   f:=half(f);
//!   until f=1
//!
//!
//! @ When we want to multiply something by a |scaled| quantity, we use a scheme
//! analogous to |take_fraction| but with a different scaling.
//! Given positive operands, |take_scaled|
//! computes the quantity $p=\lfloor qf/2^{16}+{1\over2}\rfloor$.
//!
//! Once again it is a good idea to use 64-bit arithmetic if
//! possible; otherwise |take_scaled| will use more than 2\pct! of the running time
//! when the Computer Modern fonts are being generated.
//! @^inner loop@>
//!
//! @p function take_scaled(@!q:integer;@!f:scaled):integer;
//! var @!p:integer; {the fraction so far}
//! @!negative:boolean; {should the result be negated?}
//! @!n:integer; {additional multiple of $q$}
//! @!be_careful:integer; {disables certain compiler optimizations}
//! begin @<Reduce to the case that |f>=0| and |q>=0|@>;
//! if f<unity then n:=0
//! else  begin n:=f div unity; f:=f mod unity;
//!   if q<=el_gordo div n then n:=n*q
//!   else  begin arith_error:=true; n:=el_gordo;
//!     end;
//!   end;
//! f:=f+unity;
//! @<Compute $p=\lfloor qf/2^{16}+{1\over2}\rfloor-q$@>;
//! be_careful:=n-el_gordo;
//! if be_careful+p>0 then
//!   begin arith_error:=true; n:=el_gordo-p;
//!   end;
//! if negative then take_scaled:=-(n+p)
//! else take_scaled:=n+p;
//! end;
//!
//! @ @<Compute $p=\lfloor qf/2^{16}+{1\over2}\rfloor-q$@>=
//! p:=half_unit; {that's $2^{15}$; the invariants hold now with $k=16$}
//! @^inner loop@>
//! if q<fraction_four then
//!   repeat if odd(f) then p:=half(p+q)@+else p:=half(p);
//!   f:=half(f);
//!   until f=1
//! else  repeat if odd(f) then p:=p+half(q-p)@+else p:=half(p);
//!   f:=half(f);
//!   until f=1
//!
//! @ For completeness, there's also |make_scaled|, which computes a
//! quotient as a |scaled| number instead of as a |fraction|.
//! In other words, the result is $\lfloor2^{16}p/q+{1\over2}\rfloor$, if the
//! operands are positive. \ (This procedure is not used especially often,
//! so it is not part of \MF's inner loop.)
//!
//! @p function make_scaled(@!p,@!q:integer):scaled;
//! var @!f:integer; {the fraction bits, with a leading 1 bit}
//! @!n:integer; {the integer part of $\vert p/q\vert$}
//! @!negative:boolean; {should the result be negated?}
//! @!be_careful:integer; {disables certain compiler optimizations}
//! begin if p>=0 then negative:=false
//! else  begin negate(p); negative:=true;
//!   end;
//! if q<=0 then
//!   begin debug if q=0 then confusion("/");@+gubed@;@/
//! @:this can't happen /}{\quad \./@>
//!   negate(q); negative:=not negative;
//!   end;
//! n:=p div q; p:=p mod q;
//! if n>=@'100000 then
//!   begin arith_error:=true;
//!   if negative then make_scaled:=-el_gordo@+else make_scaled:=el_gordo;
//!   end
//! else  begin n:=(n-1)*unity;
//!   @<Compute $f=\lfloor 2^{16}(1+p/q)+{1\over2}\rfloor$@>;
//!   if negative then make_scaled:=-(f+n)@+else make_scaled:=f+n;
//!   end;
//! end;
//!
//! @ @<Compute $f=\lfloor 2^{16}(1+p/q)+{1\over2}\rfloor$@>=
//! f:=1;
//! repeat be_careful:=p-q; p:=be_careful+p;
//! if p>=0 then f:=f+f+1
//! else  begin double(f); p:=p+q;
//!   end;
//! until f>=unity;
//! be_careful:=p-q;
//! if be_careful+p>=0 then incr(f)
//!
//! @ Here is a typical example of how the routines above can be used.
//! It computes the function
//! $${1\over3\tau}f(\theta,\phi)=
//! {\tau^{-1}\bigl(2+\sqrt2\,(\sin\theta-{1\over16}\sin\phi)
//!  (\sin\phi-{1\over16}\sin\theta)(\cos\theta-\cos\phi)\bigr)\over
//! 3\,\bigl(1+{1\over2}(\sqrt5-1)\cos\theta+{1\over2}(3-\sqrt5\,)\cos\phi\bigr)},$$
//! where $\tau$ is a |scaled| ``tension'' parameter. This is \MF's magic
//! fudge factor for placing the first control point of a curve that starts
//! at an angle $\theta$ and ends at an angle $\phi$ from the straight path.
//! (Actually, if the stated quantity exceeds 4, \MF\ reduces it to~4.)
//!
//! The trigonometric quantity to be multiplied by $\sqrt2$ is less than $\sqrt2$.
//! (It's a sum of eight terms whose absolute values can be bounded using
//! relations such as $\sin\theta\cos\theta\L{1\over2}$.) Thus the numerator
//! is positive; and since the tension $\tau$ is constrained to be at least
//! $3\over4$, the numerator is less than $16\over3$. The denominator is
//! nonnegative and at most~6.  Hence the fixed-point calculations below
//! are guaranteed to stay within the bounds of a 32-bit computer word.
//!
//! The angles $\theta$ and $\phi$ are given implicitly in terms of |fraction|
//! arguments |st|, |ct|, |sf|, and |cf|, representing $\sin\theta$, $\cos\theta$,
//! $\sin\phi$, and $\cos\phi$, respectively.
//!
//! @p function velocity(@!st,@!ct,@!sf,@!cf:fraction;@!t:scaled):fraction;
//! var @!acc,@!num,@!denom:integer; {registers for intermediate calculations}
//! begin acc:=take_fraction(st-(sf div 16), sf-(st div 16));
//! acc:=take_fraction(acc,ct-cf);
//! num:=fraction_two+take_fraction(acc,379625062);
//!   {$2^{28}\sqrt2\approx379625062.497$}
//! denom:=fraction_three+take_fraction(ct,497706707)+take_fraction(cf,307599661);
//!   {$3\cdot2^{27}\cdot(\sqrt5-1)\approx497706706.78$ and
//!     $3\cdot2^{27}\cdot(3-\sqrt5\,)\approx307599661.22$}
//! if t<>unity then num:=make_scaled(num,t);
//!   {|make_scaled(fraction,scaled)=fraction|}
//! if num div 4>=denom then velocity:=fraction_four
//! else velocity:=make_fraction(num,denom);
//! end;
//!
//! @ The following somewhat different subroutine tests rigorously if $ab$ is
//! greater than, equal to, or less than~$cd$,
//! given integers $(a,b,c,d)$. In most cases a quick decision is reached.
//! The result is $+1$, 0, or~$-1$ in the three respective cases.
//!
//! @d return_sign(#)==begin ab_vs_cd:=#; return;
//!   end
//!
//! @p function ab_vs_cd(@!a,b,c,d:integer):integer;
//! label exit;
//! var @!q,@!r:integer; {temporary registers}
//! begin @<Reduce to the case that |a,c>=0|, |b,d>0|@>;
//! loop@+  begin q := a div d; r := c div b;
//!   if q<>r then
//!     if q>r then return_sign(1)@+else return_sign(-1);
//!   q := a mod d; r := c mod b;
//!   if r=0 then
//!     if q=0 then return_sign(0)@+else return_sign(1);
//!   if q=0 then return_sign(-1);
//!   a:=b; b:=q; c:=d; d:=r;
//!   end; {now |a>d>0| and |c>b>0|}
//! exit:end;
//!
//! @ @<Reduce to the case that |a...@>=
//! if a<0 then
//!   begin negate(a); negate(b);
//!   end;
//! if c<0 then
//!   begin negate(c); negate(d);
//!   end;
//! if d<=0 then
//!   begin if b>=0 then
//!     if ((a=0)or(b=0))and((c=0)or(d=0)) then return_sign(0)
//!     else return_sign(1);
//!   if d=0 then
//!     if a=0 then return_sign(0)@+else return_sign(-1);
//!   q:=a; a:=c; c:=q; q:=-b; b:=-d; d:=q;
//!   end
//! else if b<=0 then
//!   begin if b<0 then if a>0 then return_sign(-1);
//!   if c=0 then return_sign(0) else return_sign(-1);
//!   end
//!
//! @ We conclude this set of elementary routines with some simple rounding
//! and truncation operations that are coded in a machine-independent fashion.
//! The routines are slightly complicated because we want them to work
//! without overflow whenever $-2^{31}\L x<2^{31}$.
//!
//! @p function floor_scaled(@!x:scaled):scaled;
//!   {$2^{16}\lfloor x/2^{16}\rfloor$}
//! var @!be_careful:integer; {temporary register}
//! begin if x>=0 then floor_scaled:=x-(x mod unity)
//! else  begin be_careful:=x+1;
//!   floor_scaled:=x+((-be_careful) mod unity)+1-unity;
//!   end;
//! end;
//! @#
//! function floor_unscaled(@!x:scaled):integer;
//!   {$\lfloor x/2^{16}\rfloor$}
//! var @!be_careful:integer; {temporary register}
//! begin if x>=0 then floor_unscaled:=x div unity
//! else  begin be_careful:=x+1; floor_unscaled:=-(1+((-be_careful) div unity));
//!   end;
//! end;
//! @#
//! function round_unscaled(@!x:scaled):integer;
//!   {$\lfloor x/2^{16}+.5\rfloor$}
//! var @!be_careful:integer; {temporary register}
//! begin if x>=half_unit then round_unscaled:=1+((x-half_unit) div unity)
//! else if x>=-half_unit then round_unscaled:=0
//! else  begin be_careful:=x+1;
//!   round_unscaled:=-(1+((-be_careful-half_unit) div unity));
//!   end;
//! end;
//! @#
//! function round_fraction(@!x:fraction):scaled;
//!   {$\lfloor x/2^{12}+.5\rfloor$}
//! var @!be_careful:integer; {temporary register}
//! begin if x>=2048 then round_fraction:=1+((x-2048) div 4096)
//! else if x>=-2048 then round_fraction:=0
//! else  begin be_careful:=x+1;
//!   round_fraction:=-(1+((-be_careful-2048) div 4096));
//!   end;
//! end;
//!
//! @* \[8] Algebraic and transcendental functions.
//! \MF\ computes all of the necessary special functions from scratch, without
//! relying on |real| arithmetic or system subroutines for sines, cosines, etc.
//!
//! @ To get the square root of a |scaled| number |x|, we want to calculate
//! $s=\lfloor 2^8\!\sqrt x +{1\over2}\rfloor$. If $x>0$, this is the unique
//! integer such that $2^{16}x-s\L s^2<2^{16}x+s$. The following subroutine
//! determines $s$ by an iterative method that maintains the invariant
//! relations $x=2^{46-2k}x_0\bmod 2^{30}$, $0<y=\lfloor 2^{16-2k}x_0\rfloor
//! -s^2+s\L q=2s$, where $x_0$ is the initial value of $x$. The value of~$y$
//! might, however, be zero at the start of the first iteration.
//!
//! @p function square_rt(@!x:scaled):scaled;
//! var @!k:small_number; {iteration control counter}
//! @!y,@!q:integer; {registers for intermediate calculations}
//! begin if x<=0 then @<Handle square root of zero or negative argument@>
//! else  begin k:=23; q:=2;
//!   while x<fraction_two do {i.e., |while x<@t$2^{29}$@>|\unskip}
//!     begin decr(k); x:=x+x+x+x;
//!     end;
//!   if x<fraction_four then y:=0
//!   else  begin x:=x-fraction_four; y:=1;
//!     end;
//!   repeat @<Decrease |k| by 1, maintaining the invariant
//!     relations between |x|, |y|, and~|q|@>;
//!   until k=0;
//!   square_rt:=half(q);
//!   end;
//! end;
//!
//! @ @<Handle square root of zero...@>=
//! begin if x<0 then
//!   begin print_err("Square root of ");
//! @.Square root...replaced by 0@>
//!   print_scaled(x); print(" has been replaced by 0");
//!   help2("Since I don't take square roots of negative numbers,")@/
//!     ("I'm zeroing this one. Proceed, with fingers crossed.");
//!   error;
//!   end;
//! square_rt:=0;
//! end
//!
//! @ @<Decrease |k| by 1, maintaining...@>=
//! double(x); double(y);
//! if x>=fraction_four then {note that |fraction_four=@t$2^{30}$@>|}
//!   begin x:=x-fraction_four; incr(y);
//!   end;
//! double(x); y:=y+y-q; double(q);
//! if x>=fraction_four then
//!   begin x:=x-fraction_four; incr(y);
//!   end;
//! if y>q then
//!   begin y:=y-q; q:=q+2;
//!   end
//! else if y<=0 then
//!   begin q:=q-2; y:=y+q;
//!   end;
//! decr(k)
//!
//! @ Pythagorean addition $\psqrt{a^2+b^2}$ is implemented by an elegant
//! iterative scheme due to Cleve Moler and Donald Morrison [{\sl IBM Journal
//! @^Moler, Cleve Barry@>
//! @^Morrison, Donald Ross@>
//! of Research and Development\/ \bf27} (1983), 577--581]. It modifies |a| and~|b|
//! in such a way that their Pythagorean sum remains invariant, while the
//! smaller argument decreases.
//!
//! @p function pyth_add(@!a,@!b:integer):integer;
//! label done;
//! var @!r:fraction; {register used to transform |a| and |b|}
//! @!big:boolean; {is the result dangerously near $2^{31}$?}
//! begin a:=abs(a); b:=abs(b);
//! if a<b then
//!   begin r:=b; b:=a; a:=r;
//!   end; {now |0<=b<=a|}
//! if b>0 then
//!   begin if a<fraction_two then big:=false
//!   else  begin a:=a div 4; b:=b div 4; big:=true;
//!     end; {we reduced the precision to avoid arithmetic overflow}
//!   @<Replace |a| by an approximation to $\psqrt{a^2+b^2}$@>;
//!   if big then
//!     if a<fraction_two then a:=a+a+a+a
//!     else  begin arith_error:=true; a:=el_gordo;
//!       end;
//!   end;
//! pyth_add:=a;
//! end;
//!
//! @ The key idea here is to reflect the vector $(a,b)$ about the
//! line through $(a,b/2)$.
//!
//! @<Replace |a| by an approximation to $\psqrt{a^2+b^2}$@>=
//! loop@+  begin r:=make_fraction(b,a);
//!   r:=take_fraction(r,r); {now $r\approx b^2/a^2$}
//!   if r=0 then goto done;
//!   r:=make_fraction(r,fraction_four+r);
//!   a:=a+take_fraction(a+a,r); b:=take_fraction(b,r);
//!   end;
//! done:
//!
//! @ Here is a similar algorithm for $\psqrt{a^2-b^2}$.
//! It converges slowly when $b$ is near $a$, but otherwise it works fine.
//!
//! @p function pyth_sub(@!a,@!b:integer):integer;
//! label done;
//! var @!r:fraction; {register used to transform |a| and |b|}
//! @!big:boolean; {is the input dangerously near $2^{31}$?}
//! begin a:=abs(a); b:=abs(b);
//! if a<=b then @<Handle erroneous |pyth_sub| and set |a:=0|@>
//! else  begin if a<fraction_four then big:=false
//!   else  begin a:=half(a); b:=half(b); big:=true;
//!     end;
//!   @<Replace |a| by an approximation to $\psqrt{a^2-b^2}$@>;
//!   if big then a:=a+a;
//!   end;
//! pyth_sub:=a;
//! end;
//!
//! @ @<Replace |a| by an approximation to $\psqrt{a^2-b^2}$@>=
//! loop@+  begin r:=make_fraction(b,a);
//!   r:=take_fraction(r,r); {now $r\approx b^2/a^2$}
//!   if r=0 then goto done;
//!   r:=make_fraction(r,fraction_four-r);
//!   a:=a-take_fraction(a+a,r); b:=take_fraction(b,r);
//!   end;
//! done:
//!
//! @ @<Handle erroneous |pyth_sub| and set |a:=0|@>=
//! begin if a<b then
//!   begin print_err("Pythagorean subtraction "); print_scaled(a);
//!   print("+-+"); print_scaled(b); print(" has been replaced by 0");
//! @.Pythagorean...@>
//!   help2("Since I don't take square roots of negative numbers,")@/
//!     ("I'm zeroing this one. Proceed, with fingers crossed.");
//!   error;
//!   end;
//! a:=0;
//! end
//!
//! @ The subroutines for logarithm and exponential involve two tables.
//! The first is simple: |two_to_the[k]| equals $2^k$. The second involves
//! a bit more calculation, which the author claims to have done correctly:
//! |spec_log[k]| is $2^{27}$ times $\ln\bigl(1/(1-2^{-k})\bigr)=
//! 2^{-k}+{1\over2}2^{-2k}+{1\over3}2^{-3k}+\cdots\,$, rounded to the
//! nearest integer.
//!
//! @<Glob...@>=
//! @!two_to_the:array[0..30] of integer; {powers of two}
//! @!spec_log:array[1..28] of integer; {special logarithms}
//!
//! @ @<Local variables for initialization@>=
//! @!k:integer; {all-purpose loop index}
//!
//! @ @<Set init...@>=
//! two_to_the[0]:=1;
//! for k:=1 to 30 do two_to_the[k]:=2*two_to_the[k-1];
//! spec_log[1]:=93032640;
//! spec_log[2]:=38612034;
//! spec_log[3]:=17922280;
//! spec_log[4]:=8662214;
//! spec_log[5]:=4261238;
//! spec_log[6]:=2113709;
//! spec_log[7]:=1052693;
//! spec_log[8]:=525315;
//! spec_log[9]:=262400;
//! spec_log[10]:=131136;
//! spec_log[11]:=65552;
//! spec_log[12]:=32772;
//! spec_log[13]:=16385;
//! for k:=14 to 27 do spec_log[k]:=two_to_the[27-k];
//! spec_log[28]:=1;
//!
//! @ Here is the routine that calculates $2^8$ times the natural logarithm
//! of a |scaled| quantity; it is an integer approximation to $2^{24}\ln(x/2^{16})$,
//! when |x| is a given positive integer.
//!
//! The method is based on exercise 1.2.2--25 in {\sl The Art of Computer
//! Programming\/}: During the main iteration we have $1\L 2^{-30}x<1/(1-2^{1-k})$,
//! and the logarithm of $2^{30}x$ remains to be added to an accumulator
//! register called~$y$. Three auxiliary bits of accuracy are retained in~$y$
//! during the calculation, and sixteen auxiliary bits to extend |y| are
//! kept in~|z| during the initial argument reduction. (We add
//! $100\cdot2^{16}=6553600$ to~|z| and subtract 100 from~|y| so that |z| will
//! not become negative; also, the actual amount subtracted from~|y| is~96,
//! not~100, because we want to add~4 for rounding before the final division by~8.)
//!
//! @p function m_log(@!x:scaled):scaled;
//! var @!y,@!z:integer; {auxiliary registers}
//! @!k:integer; {iteration counter}
//! begin if x<=0 then @<Handle non-positive logarithm@>
//! else  begin y:=1302456956+4-100; {$14\times2^{27}\ln2\approx1302456956.421063$}
//!   z:=27595+6553600; {and $2^{16}\times .421063\approx 27595$}
//!   while x<fraction_four do
//!     begin double(x); y:=y-93032639; z:=z-48782;
//!     end; {$2^{27}\ln2\approx 93032639.74436163$
//!       and $2^{16}\times.74436163\approx 48782$}
//!   y:=y+(z div unity); k:=2;
//!   while x>fraction_four+4 do
//!     @<Increase |k| until |x| can be multiplied by a
//!       factor of $2^{-k}$, and adjust $y$ accordingly@>;
//!   m_log:=y div 8;
//!   end;
//! end;
//!
//! @ @<Increase |k| until |x| can...@>=
//! begin z:=((x-1) div two_to_the[k])+1; {$z=\lceil x/2^k\rceil$}
//! while x<fraction_four+z do
//!   begin z:=half(z+1); k:=k+1;
//!   end;
//! y:=y+spec_log[k]; x:=x-z;
//! end
//!
//! @ @<Handle non-positive logarithm@>=
//! begin print_err("Logarithm of ");
//! @.Logarithm...replaced by 0@>
//! print_scaled(x); print(" has been replaced by 0");
//! help2("Since I don't take logs of non-positive numbers,")@/
//!   ("I'm zeroing this one. Proceed, with fingers crossed.");
//! error; m_log:=0;
//! end
//!
//! @ Conversely, the exponential routine calculates $\exp(x/2^8)$,
//! when |x| is |scaled|. The result is an integer approximation to
//! $2^{16}\exp(x/2^{24})$, when |x| is regarded as an integer.
//!
//! @p function m_exp(@!x:scaled):scaled;
//! var @!k:small_number; {loop control index}
//! @!y,@!z:integer; {auxiliary registers}
//! begin if x>174436200 then
//!     {$2^{24}\ln((2^{31}-1)/2^{16})\approx 174436199.51$}
//!   begin arith_error:=true; m_exp:=el_gordo;
//!   end
//! else if x<-197694359 then m_exp:=0
//!     {$2^{24}\ln(2^{-1}/2^{16})\approx-197694359.45$}
//! else  begin if x<=0 then
//!     begin z:=-8*x; y:=@'4000000; {$y=2^{20}$}
//!     end
//!   else  begin if x<=127919879 then z:=1023359037-8*x
//!       {$2^{27}\ln((2^{31}-1)/2^{20})\approx 1023359037.125$}
//!     else z:=8*(174436200-x); {|z| is always nonnegative}
//!     y:=el_gordo;
//!     end;
//!   @<Multiply |y| by $\exp(-z/2^{27})$@>;
//!   if x<=127919879 then m_exp:=(y+8) div 16@+else m_exp:=y;
//!   end;
//! end;
//!
//! @ The idea here is that subtracting |spec_log[k]| from |z| corresponds
//! to multiplying |y| by $1-2^{-k}$.
//!
//! A subtle point (which had to be checked) was that if $x=127919879$, the
//! value of~|y| will decrease so that |y+8| doesn't overflow. In fact,
//! $z$ will be 5 in this case, and |y| will decrease by~64 when |k=25|
//! and by~16 when |k=27|.
//!
//! @<Multiply |y| by...@>=
//! k:=1;
//! while z>0 do
//!   begin while z>=spec_log[k] do
//!     begin z:=z-spec_log[k];
//!     y:=y-1-((y-two_to_the[k-1]) div two_to_the[k]);
//!     end;
//!   incr(k);
//!   end
//!
//! @ The trigonometric subroutines use an auxiliary table such that
//! |spec_atan[k]| contains an approximation to the |angle| whose tangent
//! is~$1/2^k$.
//!
//! @<Glob...@>=
//! @!spec_atan:array[1..26] of angle; {$\arctan2^{-k}$ times $2^{20}\cdot180/\pi$}
//!
//! @ @<Set init...@>=
//! spec_atan[1]:=27855475;
//! spec_atan[2]:=14718068;
//! spec_atan[3]:=7471121;
//! spec_atan[4]:=3750058;
//! spec_atan[5]:=1876857;
//! spec_atan[6]:=938658;
//! spec_atan[7]:=469357;
//! spec_atan[8]:=234682;
//! spec_atan[9]:=117342;
//! spec_atan[10]:=58671;
//! spec_atan[11]:=29335;
//! spec_atan[12]:=14668;
//! spec_atan[13]:=7334;
//! spec_atan[14]:=3667;
//! spec_atan[15]:=1833;
//! spec_atan[16]:=917;
//! spec_atan[17]:=458;
//! spec_atan[18]:=229;
//! spec_atan[19]:=115;
//! spec_atan[20]:=57;
//! spec_atan[21]:=29;
//! spec_atan[22]:=14;
//! spec_atan[23]:=7;
//! spec_atan[24]:=4;
//! spec_atan[25]:=2;
//! spec_atan[26]:=1;
//!
//! @ Given integers |x| and |y|, not both zero, the |n_arg| function
//! returns the |angle| whose tangent points in the direction $(x,y)$.
//! This subroutine first determines the correct octant, then solves the
//! problem for |0<=y<=x|, then converts the result appropriately to
//! return an answer in the range |-one_eighty_deg<=@t$\theta$@><=one_eighty_deg|.
//! (The answer is |+one_eighty_deg| if |y=0| and |x<0|, but an answer of
//! |-one_eighty_deg| is possible if, for example, |y=-1| and $x=-2^{30}$.)
//!
//! The octants are represented in a ``Gray code,'' since that turns out
//! to be computationally simplest.
//!
//! @d negate_x=1
//! @d negate_y=2
//! @d switch_x_and_y=4
//! @d first_octant=1
//! @d second_octant=first_octant+switch_x_and_y
//! @d third_octant=first_octant+switch_x_and_y+negate_x
//! @d fourth_octant=first_octant+negate_x
//! @d fifth_octant=first_octant+negate_x+negate_y
//! @d sixth_octant=first_octant+switch_x_and_y+negate_x+negate_y
//! @d seventh_octant=first_octant+switch_x_and_y+negate_y
//! @d eighth_octant=first_octant+negate_y
//!
//! @p function n_arg(@!x,@!y:integer):angle;
//! var @!z:angle; {auxiliary register}
//! @!t:integer; {temporary storage}
//! @!k:small_number; {loop counter}
//! @!octant:first_octant..sixth_octant; {octant code}
//! begin if x>=0 then octant:=first_octant
//! else  begin negate(x); octant:=first_octant+negate_x;
//!   end;
//! if y<0 then
//!   begin negate(y); octant:=octant+negate_y;
//!   end;
//! if x<y then
//!   begin t:=y; y:=x; x:=t; octant:=octant+switch_x_and_y;
//!   end;
//! if x=0 then @<Handle undefined arg@>
//! else  begin @<Set variable |z| to the arg of $(x,y)$@>;
//!   @<Return an appropriate answer based on |z| and |octant|@>;
//!   end;
//! end;
//!
//! @ @<Handle undefined arg@>=
//! begin print_err("angle(0,0) is taken as zero");
//! @.angle(0,0)...zero@>
//! help2("The `angle' between two identical points is undefined.")@/
//!   ("I'm zeroing this one. Proceed, with fingers crossed.");
//! error; n_arg:=0;
//! end
//!
//! @ @<Return an appropriate answer...@>=
//! case octant of
//! first_octant:n_arg:=z;
//! second_octant:n_arg:=ninety_deg-z;
//! third_octant:n_arg:=ninety_deg+z;
//! fourth_octant:n_arg:=one_eighty_deg-z;
//! fifth_octant:n_arg:=z-one_eighty_deg;
//! sixth_octant:n_arg:=-z-ninety_deg;
//! seventh_octant:n_arg:=z-ninety_deg;
//! eighth_octant:n_arg:=-z;
//! end {there are no other cases}
//!
//! @ At this point we have |x>=y>=0|, and |x>0|. The numbers are scaled up
//! or down until $2^{28}\L x<2^{29}$, so that accurate fixed-point calculations
//! will be made.
//!
//! @<Set variable |z| to the arg...@>=
//! while x>=fraction_two do
//!   begin x:=half(x); y:=half(y);
//!   end;
//! z:=0;
//! if y>0 then
//!   begin while x<fraction_one do
//!     begin double(x); double(y);
//!     end;
//!   @<Increase |z| to the arg of $(x,y)$@>;
//!   end
//!
//! @ During the calculations of this section, variables |x| and~|y|
//! represent actual coordinates $(x,2^{-k}y)$. We will maintain the
//! condition |x>=y|, so that the tangent will be at most $2^{-k}$.
//! If $x<2y$, the tangent is greater than $2^{-k-1}$. The transformation
//! $(a,b)\mapsto(a+b\tan\phi,b-a\tan\phi)$ replaces $(a,b)$ by
//! coordinates whose angle has decreased by~$\phi$; in the special case
//! $a=x$, $b=2^{-k}y$, and $\tan\phi=2^{-k-1}$, this operation reduces
//! to the particularly simple iteration shown here. [Cf.~John E. Meggitt,
//! @^Meggitt, John E.@>
//! {\sl IBM Journal of Research and Development\/ \bf6} (1962), 210--226.]
//!
//! The initial value of |x| will be multiplied by at most
//! $(1+{1\over2})(1+{1\over8})(1+{1\over32})\cdots\approx 1.7584$; hence
//! there is no chance of integer overflow.
//!
//! @<Increase |z|...@>=
//! k:=0;
//! repeat double(y); incr(k);
//! if y>x then
//!   begin z:=z+spec_atan[k]; t:=x; x:=x+(y div two_to_the[k+k]); y:=y-t;
//!   end;
//! until k=15;
//! repeat double(y); incr(k);
//! if y>x then
//!   begin z:=z+spec_atan[k]; y:=y-x;
//!   end;
//! until k=26
//!
//! @ Conversely, the |n_sin_cos| routine takes an |angle| and produces the sine
//! and cosine of that angle. The results of this routine are
//! stored in global integer variables |n_sin| and |n_cos|.
//!
//! @<Glob...@>=
//! @!n_sin,@!n_cos:fraction; {results computed by |n_sin_cos|}
//!
//! @ Given an integer |z| that is $2^{20}$ times an angle $\theta$ in degrees,
//! the purpose of |n_sin_cos(z)| is to set
//! |x=@t$r\cos\theta$@>| and |y=@t$r\sin\theta$@>| (approximately),
//! for some rather large number~|r|. The maximum of |x| and |y|
//! will be between $2^{28}$ and $2^{30}$, so that there will be hardly
//! any loss of accuracy. Then |x| and~|y| are divided by~|r|.
//!
//! @p procedure n_sin_cos(@!z:angle); {computes a multiple of the sine and cosine}
//! var @!k:small_number; {loop control variable}
//! @!q:0..7; {specifies the quadrant}
//! @!r:fraction; {magnitude of |(x,y)|}
//! @!x,@!y,@!t:integer; {temporary registers}
//! begin while z<0 do z:=z+three_sixty_deg;
//! z:=z mod three_sixty_deg; {now |0<=z<three_sixty_deg|}
//! q:=z div forty_five_deg; z:=z mod forty_five_deg;
//! x:=fraction_one; y:=x;
//! if not odd(q) then z:=forty_five_deg-z;
//! @<Subtract angle |z| from |(x,y)|@>;
//! @<Convert |(x,y)| to the octant determined by~|q|@>;
//! r:=pyth_add(x,y); n_cos:=make_fraction(x,r); n_sin:=make_fraction(y,r);
//! end;
//!
//! @ In this case the octants are numbered sequentially.
//!
//! @<Convert |(x,...@>=
//! case q of
//! 0:do_nothing;
//! 1:begin t:=x; x:=y; y:=t;
//!   end;
//! 2:begin t:=x; x:=-y; y:=t;
//!   end;
//! 3:negate(x);
//! 4:begin negate(x); negate(y);
//!   end;
//! 5:begin t:=x; x:=-y; y:=-t;
//!   end;
//! 6:begin t:=x; x:=y; y:=-t;
//!   end;
//! 7:negate(y);
//! end {there are no other cases}
//!
//! @ The main iteration of |n_sin_cos| is similar to that of |n_arg| but
//! applied in reverse. The values of |spec_atan[k]| decrease slowly enough
//! that this loop is guaranteed to terminate before the (nonexistent) value
//! |spec_atan[27]| would be required.
//!
//! @<Subtract angle |z|...@>=
//! k:=1;
//! while z>0 do
//!   begin if z>=spec_atan[k] then
//!     begin z:=z-spec_atan[k]; t:=x;@/
//!     x:=t+y div two_to_the[k];
//!     y:=y-t div two_to_the[k];
//!     end;
//!   incr(k);
//!   end;
//! if y<0 then y:=0 {this precaution may never be needed}
//!
//! @ And now let's complete our collection of numeric utility routines
//! by considering random number generation.
//! \MF\ generates pseudo-random numbers with the additive scheme recommended
//! in Section 3.6 of {\sl The Art of Computer Programming}; however, the
//! results are random fractions between 0 and |fraction_one-1|, inclusive.
//!
//! There's an auxiliary array |randoms| that contains 55 pseudo-random
//! fractions. Using the recurrence $x_n=(x_{n-55}-x_{n-24})\bmod 2^{28}$,
//! we generate batches of 55 new $x_n$'s at a time by calling |new_randoms|.
//! The global variable |j_random| tells which element has most recently
//! been consumed.
//!
//! @<Glob...@>=
//! @!randoms:array[0..54] of fraction; {the last 55 random values generated}
//! @!j_random:0..54; {the number of unused |randoms|}
//!
//! @ To consume a random fraction, the program below will say `|next_random|'
//! and then it will fetch |randoms[j_random]|. The |next_random| macro
//! actually accesses the numbers backwards; blocks of 55~$x$'s are
//! essentially being ``flipped.'' But that doesn't make them less random.
//!
//! @d next_random==if j_random=0 then new_randoms
//!   else decr(j_random)
//!
//! @p procedure new_randoms;
//! var @!k:0..54; {index into |randoms|}
//! @!x:fraction; {accumulator}
//! begin for k:=0 to 23 do
//!   begin x:=randoms[k]-randoms[k+31];
//!   if x<0 then x:=x+fraction_one;
//!   randoms[k]:=x;
//!   end;
//! for k:=24 to 54 do
//!   begin x:=randoms[k]-randoms[k-24];
//!   if x<0 then x:=x+fraction_one;
//!   randoms[k]:=x;
//!   end;
//! j_random:=54;
//! end;
//!
//! @ To initialize the |randoms| table, we call the following routine.
//!
//! @p procedure init_randoms(@!seed:scaled);
//! var @!j,@!jj,@!k:fraction; {more or less random integers}
//! @!i:0..54; {index into |randoms|}
//! begin j:=abs(seed);
//! while j>=fraction_one do j:=half(j);
//! k:=1;
//! for i:=0 to 54 do
//!   begin jj:=k; k:=j-k; j:=jj;
//!   if k<0 then k:=k+fraction_one;
//!   randoms[(i*21)mod 55]:=j;
//!   end;
//! new_randoms; new_randoms; new_randoms; {``warm up'' the array}
//! end;
//!
//! @ To produce a uniform random number in the range |0<=u<x| or |0>=u>x|
//! or |0=u=x|, given a |scaled| value~|x|, we proceed as shown here.
//!
//! Note that the call of |take_fraction| will produce the values 0 and~|x|
//! with about half the probability that it will produce any other particular
//! values between 0 and~|x|, because it rounds its answers.
//!
//! @p function unif_rand(@!x:scaled):scaled;
//! var @!y:scaled; {trial value}
//! begin next_random; y:=take_fraction(abs(x),randoms[j_random]);
//! if y=abs(x) then unif_rand:=0
//! else if x>0 then unif_rand:=y
//! else unif_rand:=-y;
//! end;
//!
//! @ Finally, a normal deviate with mean zero and unit standard deviation
//! can readily be obtained with the ratio method (Algorithm 3.4.1R in
//! {\sl The Art of Computer Programming\/}).
//!
//! @p function norm_rand:scaled;
//! var @!x,@!u,@!l:integer; {what the book would call $2^{16}X$, $2^{28}U$,
//!   and $-2^{24}\ln U$}
//! begin repeat
//!   repeat next_random;
//!   x:=take_fraction(112429,randoms[j_random]-fraction_half);
//!     {$2^{16}\sqrt{8/e}\approx 112428.82793$}
//!   next_random; u:=randoms[j_random];
//!   until abs(x)<u;
//! x:=make_fraction(x,u);
//! l:=139548960-m_log(u); {$2^{24}\cdot12\ln2\approx139548959.6165$}
//! until ab_vs_cd(1024,l,x,x)>=0;
//! norm_rand:=x;
//! end;
//!
//! @* \[9] Packed data.
//! In order to make efficient use of storage space, \MF\ bases its major data
//! structures on a |memory_word|, which contains either a (signed) integer,
//! possibly scaled, or a small number of fields that are one half or one
//! quarter of the size used for storing integers.
//!
//! If |x| is a variable of type |memory_word|, it contains up to four
//! fields that can be referred to as follows:
//! $$\vbox{\halign{\hfil#&#\hfil&#\hfil\cr
//! |x|&.|int|&(an |integer|)\cr
//! |x|&.|sc|\qquad&(a |scaled| integer)\cr
//! |x.hh.lh|, |x.hh|&.|rh|&(two halfword fields)\cr
//! |x.hh.b0|, |x.hh.b1|, |x.hh|&.|rh|&(two quarterword fields, one halfword
//!   field)\cr
//! |x.qqqq.b0|, |x.qqqq.b1|, |x.qqqq|&.|b2|, |x.qqqq.b3|\hskip-100pt
//!   &\qquad\qquad\qquad(four quarterword fields)\cr}}$$
//! This is somewhat cumbersome to write, and not very readable either, but
//! macros will be used to make the notation shorter and more transparent.
//! The \PASCAL\ code below gives a formal definition of |memory_word| and
//! its subsidiary types, using packed variant records. \MF\ makes no
//! assumptions about the relative positions of the fields within a word.
//!
//! Since we are assuming 32-bit integers, a halfword must contain at least
//! 16 bits, and a quarterword must contain at least 8 bits.
//! @^system dependencies@>
//! But it doesn't hurt to have more bits; for example, with enough 36-bit
//! words you might be able to have |mem_max| as large as 262142.
//!
//! N.B.: Valuable memory space will be dreadfully wasted unless \MF\ is compiled
//! by a \PASCAL\ that packs all of the |memory_word| variants into
//! the space of a single integer. Some \PASCAL\ compilers will pack an
//! integer whose subrange is `|0..255|' into an eight-bit field, but others
//! insist on allocating space for an additional sign bit; on such systems you
//! can get 256 values into a quarterword only if the subrange is `|-128..127|'.
//!
//! The present implementation tries to accommodate as many variations as possible,
//! so it makes few assumptions. If integers having the subrange
//! `|min_quarterword..max_quarterword|' can be packed into a quarterword,
//! and if integers having the subrange `|min_halfword..max_halfword|'
//! can be packed into a halfword, everything should work satisfactorily.
//!
//! It is usually most efficient to have |min_quarterword=min_halfword=0|,
//! so one should try to achieve this unless it causes a severe problem.
//! The values defined here are recommended for most 32-bit computers.
//!
//! @d min_quarterword=0 {smallest allowable value in a |quarterword|}
//! @d max_quarterword=255 {largest allowable value in a |quarterword|}
//! @d min_halfword==0 {smallest allowable value in a |halfword|}
//! @d max_halfword==65535 {largest allowable value in a |halfword|}
//!
//! @ Here are the inequalities that the quarterword and halfword values
//! must satisfy (or rather, the inequalities that they mustn't satisfy):
//!
//! @<Check the ``constant''...@>=
//! init if mem_max<>mem_top then bad:=10;@+tini@;@/
//! if mem_max<mem_top then bad:=10;
//! if (min_quarterword>0)or(max_quarterword<127) then bad:=11;
//! if (min_halfword>0)or(max_halfword<32767) then bad:=12;
//! if (min_quarterword<min_halfword)or@|
//!   (max_quarterword>max_halfword) then bad:=13;
//! if (mem_min<min_halfword)or(mem_max>=max_halfword) then bad:=14;
//! if max_strings>max_halfword then bad:=15;
//! if buf_size>max_halfword then bad:=16;
//! if (max_quarterword-min_quarterword<255)or@|
//!   (max_halfword-min_halfword<65535) then bad:=17;
//!
