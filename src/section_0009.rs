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
