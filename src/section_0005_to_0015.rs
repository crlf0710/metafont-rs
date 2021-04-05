//! @ The overall \MF\ program begins with the heading just shown, after which
//! comes a bunch of procedure declarations and function declarations.
//! Finally we will get to the main program, which begins with the
//! comment `|start_here|'. If you want to skip down to the
//! main program now, you can look up `|start_here|' in the index.
//! But the author suggests that the best way to understand this program
//! is to follow pretty much the order of \MF's components as they appear in the
//! \.{WEB} description you are now reading, since the present ordering is
//! intended to combine the advantages of the ``bottom up'' and ``top down''
//! approaches to the problem of understanding a somewhat complicated system.
//!
//! @ Three labels must be declared in the main program, so we give them
//! symbolic names.
//!
//! @d start_of_MF=1 {go here when \MF's variables are initialized}
//! @d end_of_MF=9998 {go here to close files and terminate gracefully}
//! @d final_end=9999 {this label marks the ending of the program}
//!
//! @<Labels in the out...@>=
//! start_of_MF@t\hskip-2pt@>, end_of_MF@t\hskip-2pt@>,@,final_end;
//!   {key control points}
//!
//! @ Some of the code below is intended to be used only when diagnosing the
//! strange behavior that sometimes occurs when \MF\ is being installed or
//! when system wizards are fooling around with \MF\ without quite knowing
//! what they are doing. Such code will not normally be compiled; it is
//! delimited by the codewords `$|debug|\ldots|gubed|$', with apologies
//! to people who wish to preserve the purity of English.
//!
//! Similarly, there is some conditional code delimited by
//! `$|stat|\ldots|tats|$' that is intended for use when statistics are to be
//! kept about \MF's memory usage.  The |stat| $\ldots$ |tats| code also
//! implements special diagnostic information that is printed when
//! $\\{tracingedges}>1$.
//! @^debugging@>
//!
//! @d debug==@{ {change this to `$\\{debug}\equiv\null$' when debugging}
//! @d gubed==@t@>@} {change this to `$\\{gubed}\equiv\null$' when debugging}
//! @f debug==begin
//! @f gubed==end
//! @#
//! @d stat==@{ {change this to `$\\{stat}\equiv\null$' when gathering
//!   usage statistics}
//! @d tats==@t@>@} {change this to `$\\{tats}\equiv\null$' when gathering
//!   usage statistics}
//! @f stat==begin
//! @f tats==end
//!
//! @ This program has two important variations: (1) There is a long and slow
//! version called \.{INIMF}, which does the extra calculations needed to
//! @.INIMF@>
//! initialize \MF's internal tables; and (2)~there is a shorter and faster
//! production version, which cuts the initialization to a bare minimum.
//! Parts of the program that are needed in (1) but not in (2) are delimited by
//! the codewords `$|init|\ldots|tini|$'.
//!
//! @d init== {change this to `$\\{init}\equiv\.{@@\{}$' in the production version}
//! @d tini== {change this to `$\\{tini}\equiv\.{@@\}}$' in the production version}
//! @f init==begin
//! @f tini==end
//!
//! @ If the first character of a \PASCAL\ comment is a dollar sign,
//! \ph\ treats the comment as a list of ``compiler directives'' that will
//! affect the translation of this program into machine language.  The
//! directives shown below specify full checking and inclusion of the \PASCAL\
//! debugger when \MF\ is being debugged, but they cause range checking and other
//! redundant code to be eliminated when the production system is being generated.
//! Arithmetic overflow will be detected in all cases.
//! @:PASCAL H}{\ph@>
//! @^system dependencies@>
//! @^overflow in arithmetic@>
//!
//! @<Compiler directives@>=
//! @{@&$C-,A+,D-@} {no range check, catch arithmetic overflow, no debug overhead}
//! @!debug @{@&$C+,D+@}@+ gubed {but turn everything on when debugging}
//!
//! @ This \MF\ implementation conforms to the rules of the {\sl Pascal User
//! @:PASCAL}{\PASCAL@>
//! @^system dependencies@>
//! Manual} published by Jensen and Wirth in 1975, except where system-dependent
//! @^Wirth, Niklaus@>
//! @^Jensen, Kathleen@>
//! code is necessary to make a useful system program, and except in another
//! respect where such conformity would unnecessarily obscure the meaning
//! and clutter up the code: We assume that |case| statements may include a
//! default case that applies if no matching label is found. Thus, we shall use
//! constructions like
//! $$\vbox{\halign{\ignorespaces#\hfil\cr
//! |case x of|\cr
//! 1: $\langle\,$code for $x=1\,\rangle$;\cr
//! 3: $\langle\,$code for $x=3\,\rangle$;\cr
//! |othercases| $\langle\,$code for |x<>1| and |x<>3|$\,\rangle$\cr
//! |endcases|\cr}}$$
//! since most \PASCAL\ compilers have plugged this hole in the language by
//! incorporating some sort of default mechanism. For example, the \ph\
//! compiler allows `|others|:' as a default label, and other \PASCAL s allow
//! syntaxes like `\&{else}' or `\&{otherwise}' or `\\{otherwise}:', etc. The
//! definitions of |othercases| and |endcases| should be changed to agree with
//! local conventions.  Note that no semicolon appears before |endcases| in
//! this program, so the definition of |endcases| should include a semicolon
//! if the compiler wants one. (Of course, if no default mechanism is
//! available, the |case| statements of \MF\ will have to be laboriously
//! extended by listing all remaining cases. People who are stuck with such
//! \PASCAL s have, in fact, done this, successfully but not happily!)
//! @:PASCAL H}{\ph@>
//!
//! @d othercases == others: {default for cases not listed explicitly}
//! @d endcases == @+end {follows the default case in an extended |case| statement}
//! @f othercases == else
//! @f endcases == end
//!
//! @ The following parameters can be changed at compile time to extend or
//! reduce \MF's capacity. They may have different values in \.{INIMF} and
//! in production versions of \MF.
//! @.INIMF@>
//! @^system dependencies@>
//!
//! @<Constants...@>=
//! @!mem_max=30000; {greatest index in \MF's internal |mem| array;
//!   must be strictly less than |max_halfword|;
//!   must be equal to |mem_top| in \.{INIMF}, otherwise |>=mem_top|}
//! @!max_internal=100; {maximum number of internal quantities}
//! @!buf_size=500; {maximum number of characters simultaneously present in
//!   current lines of open files; must not exceed |max_halfword|}
//! @!error_line=72; {width of context lines on terminal error messages}
//! @!half_error_line=42; {width of first lines of contexts in terminal
//!   error messages; should be between 30 and |error_line-15|}
//! @!max_print_line=79; {width of longest text lines output; should be at least 60}
//! @!screen_width=768; {number of pixels in each row of screen display}
//! @!screen_depth=1024; {number of pixels in each column of screen display}
//! @!stack_size=30; {maximum number of simultaneous input sources}
//! @!max_strings=2000; {maximum number of strings; must not exceed |max_halfword|}
//! @!string_vacancies=8000; {the minimum number of characters that should be
//!   available for the user's identifier names and strings,
//!   after \MF's own error messages are stored}
//! @!pool_size=32000; {maximum number of characters in strings, including all
//!   error messages and help texts, and the names of all identifiers;
//!   must exceed |string_vacancies| by the total
//!   length of \MF's own strings, which is currently about 22000}
//! @!move_size=5000; {space for storing moves in a single octant}
//! @!max_wiggle=300; {number of autorounded points per cycle}
//! @!gf_buf_size=800; {size of the output buffer, must be a multiple of 8}
//! @!file_name_size=40; {file names shouldn't be longer than this}
//! @!pool_name='MFbases:MF.POOL                         ';
//!   {string of length |file_name_size|; tells where the string pool appears}
//! @.MFbases@>
//! @!path_size=300; {maximum number of knots between breakpoints of a path}
//! @!bistack_size=785; {size of stack for bisection algorithms;
//!   should probably be left at this value}
//! @!header_size=100; {maximum number of \.{TFM} header words, times~4}
//! @!lig_table_size=5000; {maximum number of ligature/kern steps, must be
//!   at least 255 and at most 32510}
//! @!max_kerns=500; {maximum number of distinct kern amounts}
//! @!max_font_dimen=50; {maximum number of \&{fontdimen} parameters}
//!
//! @ Like the preceding parameters, the following quantities can be changed
//! at compile time to extend or reduce \MF's capacity. But if they are changed,
//! it is necessary to rerun the initialization program \.{INIMF}
//! @.INIMF@>
//! to generate new tables for the production \MF\ program.
//! One can't simply make helter-skelter changes to the following constants,
//! since certain rather complex initialization
//! numbers are computed from them. They are defined here using
//! \.{WEB} macros, instead of being put into \PASCAL's |const| list, in order to
//! emphasize this distinction.
//!
//! @d mem_min=0 {smallest index in the |mem| array, must not be less
//!   than |min_halfword|}
//! @d mem_top==30000 {largest index in the |mem| array dumped by \.{INIMF};
//!   must be substantially larger than |mem_min|
//!   and not greater than |mem_max|}
//! @d hash_size=2100 {maximum number of symbolic tokens,
//!   must be less than |max_halfword-3*param_size|}
//! @d hash_prime=1777 {a prime number equal to about 85\pct! of |hash_size|}
//! @d max_in_open=6 {maximum number of input files and error insertions that
//!   can be going on simultaneously}
//! @d param_size=150 {maximum number of simultaneous macro parameters}
//! @^system dependencies@>
//!
//! @ In case somebody has inadvertently made bad settings of the ``constants,''
//! \MF\ checks them using a global variable called |bad|.
//!
//! This is the first of many sections of \MF\ where global variables are
//! defined.
//!
//! @<Glob...@>=
//! @!bad:integer; {is some ``constant'' wrong?}
//!
//! @ Later on we will say `\ignorespaces|if mem_max>=max_halfword then bad:=10|',
//! or something similar. (We can't do that until |max_halfword| has been defined.)
//!
//! @<Check the ``constant'' values for consistency@>=
//! bad:=0;
//! if (half_error_line<30)or(half_error_line>error_line-15) then bad:=1;
//! if max_print_line<60 then bad:=2;
//! if gf_buf_size mod 8<>0 then bad:=3;
//! if mem_min+1100>mem_top then bad:=4;
//! if hash_prime>hash_size then bad:=5;
//! if header_size mod 4 <> 0 then bad:=6;
//! if(lig_table_size<255)or(lig_table_size>32510)then bad:=7;
//!
//! @ Labels are given symbolic names by the following definitions, so that
//! occasional |goto| statements will be meaningful. We insert the label
//! `|exit|' just before the `\ignorespaces|end|\unskip' of a procedure in
//! which we have used the `|return|' statement defined below; the label
//! `|restart|' is occasionally used at the very beginning of a procedure; and
//! the label `|reswitch|' is occasionally used just prior to a |case|
//! statement in which some cases change the conditions and we wish to branch
//! to the newly applicable case.  Loops that are set up with the |loop|
//! construction defined below are commonly exited by going to `|done|' or to
//! `|found|' or to `|not_found|', and they are sometimes repeated by going to
//! `|continue|'.  If two or more parts of a subroutine start differently but
//! end up the same, the shared code may be gathered together at
//! `|common_ending|'.
//!
//! Incidentally, this program never declares a label that isn't actually used,
//! because some fussy \PASCAL\ compilers will complain about redundant labels.
//!
//! @d exit=10 {go here to leave a procedure}
//! @d restart=20 {go here to start a procedure again}
//! @d reswitch=21 {go here to start a case statement again}
//! @d continue=22 {go here to resume a loop}
//! @d done=30 {go here to exit a loop}
//! @d done1=31 {like |done|, when there is more than one loop}
//! @d done2=32 {for exiting the second loop in a long block}
//! @d done3=33 {for exiting the third loop in a very long block}
//! @d done4=34 {for exiting the fourth loop in an extremely long block}
//! @d done5=35 {for exiting the fifth loop in an immense block}
//! @d done6=36 {for exiting the sixth loop in a block}
//! @d found=40 {go here when you've found it}
//! @d found1=41 {like |found|, when there's more than one per routine}
//! @d found2=42 {like |found|, when there's more than two per routine}
//! @d not_found=45 {go here when you've found nothing}
//! @d common_ending=50 {go here when you want to merge with another branch}
//!
