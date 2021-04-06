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
