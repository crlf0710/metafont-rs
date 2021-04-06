//! @* \[6] Reporting errors.
//! When something anomalous is detected, \MF\ typically does something like this:
//! $$\vbox{\halign{#\hfil\cr
//! |print_err("Something anomalous has been detected");|\cr
//! |help3("This is the first line of my offer to help.")|\cr
//! |("This is the second line. I'm trying to")|\cr
//! |("explain the best way for you to proceed.");|\cr
//! |error;|\cr}}$$
//! A two-line help message would be given using |help2|, etc.; these informal
//! helps should use simple vocabulary that complements the words used in the
//! official error message that was printed. (Outside the U.S.A., the help
//! messages should preferably be translated into the local vernacular. Each
//! line of help is at most 60 characters long, in the present implementation,
//! so that |max_print_line| will not be exceeded.)
//!
//! The |print_err| procedure supplies a `\.!' before the official message,
//! and makes sure that the terminal is awake if a stop is going to occur.
//! The |error| procedure supplies a `\..' after the official message, then it
//! shows the location of the error; and if |interaction=error_stop_mode|,
//! it also enters into a dialog with the user, during which time the help
//! message may be printed.
//! @^system dependencies@>
//!
//! @ The global variable |interaction| has four settings, representing increasing
//! amounts of user interaction:
//!
//! @d batch_mode=0 {omits all stops and omits terminal output}
//! @d nonstop_mode=1 {omits all stops}
//! @d scroll_mode=2 {omits error stops}
//! @d error_stop_mode=3 {stops at every opportunity to interact}
//! @d print_err(#)==begin if interaction=error_stop_mode then wake_up_terminal;
//!   print_nl("! "); print(#);
//! @.!\relax@>
//!   end
//!
//! @<Glob...@>=
//! @!interaction:batch_mode..error_stop_mode; {current level of interaction}
//!
//! @ @<Set init...@>=interaction:=error_stop_mode;
//!
//! @ \MF\ is careful not to call |error| when the print |selector| setting
//! might be unusual. The only possible values of |selector| at the time of
//! error messages are
//!
//! \yskip\hang|no_print| (when |interaction=batch_mode|
//!   and |log_file| not yet open);
//!
//! \hang|term_only| (when |interaction>batch_mode| and |log_file| not yet open);
//!
//! \hang|log_only| (when |interaction=batch_mode| and |log_file| is open);
//!
//! \hang|term_and_log| (when |interaction>batch_mode| and |log_file| is open).
//!
//! @<Initialize the print |selector| based on |interaction|@>=
//! if interaction=batch_mode then selector:=no_print@+else selector:=term_only
//!
