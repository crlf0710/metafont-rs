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
