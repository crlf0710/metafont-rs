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
