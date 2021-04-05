//! @ The present implementation has a long ancestry, beginning in the spring
//! of~1977, when its author wrote a prototype set of subroutines and macros
//! @^Knuth, Donald Ervin@>
//! that were used to develop the first Computer Modern fonts.
//! This original proto-\MF\ required the user to recompile a {\mc SAIL} program
//! whenever any character was changed, because it was not a ``language'' for
//! font design; the language was {\mc SAIL}. After several hundred characters
//! had been designed in that way, the author developed an interpretable language
//! called \MF, in which it was possible to express the Computer Modern programs
//! less cryptically. A complete \MF\ processor was designed and coded by the
//! author in 1979. This program, written in {\mc SAIL}, was adapted for use
//! with a variety of typesetting equipment and display terminals by Leo Guibas,
//! Lyle Ramshaw, and David Fuchs.
//! @^Guibas, Leonidas Ioannis@>
//! @^Ramshaw, Lyle Harold@>
//! @^Fuchs, David Raymond@>
//! Major improvements to the design of Computer Modern fonts were made in the
//! spring of 1982, after which it became clear that a new language would
//! better express the needs of letterform designers. Therefore an entirely
//! new \MF\ language and system were developed in 1984; the present system
//! retains the name and some of the spirit of \MF79, but all of the details
//! have changed.
//!
//! No doubt there still is plenty of room for improvement, but the author
//! is firmly committed to keeping \MF84 ``frozen'' from now on; stability
//! and reliability are to be its main virtues.
//!
//! On the other hand, the \.{WEB} description can be extended without changing
//! the core of \MF84 itself, and the program has been designed so that such
//! extensions are not extremely difficult to make.
//! The |banner| string defined here should be changed whenever \MF\
//! undergoes any modifications, so that it will be clear which version of
//! \MF\ might be the guilty party when a problem arises.
//! @^extensions to \MF@>
//! @^system dependencies@>
//!
//! If this program is changed, the resulting system should not be called
//! `\MF\kern.5pt'; the official name `\MF\kern.5pt' by itself is reserved
//! for software systems that are fully compatible with each other.
//! A special test suite called the ``\.{TRAP} test'' is available for
//! helping to determine whether an implementation deserves to be
//! known as `\MF\kern.5pt' [cf.~Stanford Computer Science report CS1095,
//! January 1986].
//
// @d banner=='This is METAFONT, Version 2.71828182' {printed when \MF\ starts}
/// printed when `METAFONT` starts
pub(crate) const banner: &'static str = "This is METAFONT-rs, Version 2.71828182";

migration_complete!();
