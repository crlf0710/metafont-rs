//! % Unlimited copying and redistribution of the original `mf.web` file
//! % are permitted as long as this file is not modified.
//! % Modifications are permitted, but only if the resulting file is not named mf.web.
//! % (The WEB system provides for alterations via an auxiliary file;
//! % the master file should stay intact.)
//! % In other words, METAFONT is under essentially the same ground rules as TeX.
//!
//! % Version 0 was completed on July 28, 1984.
//! % Version 1 was completed on January 4, 1986; it corresponds to "Volume D".
//! % Version 1.1 trivially corrected the punctuation in one message (June 1986).
//! % Version 1.2 corrected an arithmetic overflow problem (July 1986).
//! % Version 1.3 improved rounding when elliptical pens are made (November 1986).
//! % Version 1.4 corrected scan_declared_variable timing (May 1988).
//! % Version 1.5 fixed negative halving in allocator when mem_min<0 (June 1988).
//! % Version 1.6 kept open_log_file from calling fatal_error (November 1988).
//! % Version 1.7 solved that problem a better way (December 1988).
//! % Version 1.8 introduced major changes for 8-bit extensions (September 1989).
//! % Version 1.9 improved skimping and was edited for style (December 1989).
//! % Version 2.0 fixed bug in addto; released with TeX version 3.0 (March 1990).
//! % Version 2.7 made consistent with TeX version 3.1 (September 1990).
//! % Version 2.71 fixed bug in draw, allowed unprintable filenames (March 1992).
//! % Version 2.718 fixed bug in <Choose a dependent...> (March 1995).
//! % Version 2.7182 fixed bugs related to "<unprintable char>" (August 1996).
//! % Version 2.71828 suppressed autorounding in dangerous cases (June 2003).
//! % Version 2.718281 was a general cleanup with minor fixes (February 2008).
//! % Version 2.7182818 was similar (January 2014).
//! % Version 2.71828182 was similar (January 2021).
//!
//! % A reward of $327.68 will be paid to the first finder of any remaining bug of
//! % the original METAFONT program.
//!
//! % Although considerable effort has been expended to make the METAFONT program
//! % correct and reliable, no warranty is implied; the author disclaims any
//! % obligation or liability for damages, including but not limited to
//! % special, indirect, or consequential damages arising out of or in
//! % connection with the use or performance of this software. This work has
//! % been a ``labor of love'' and the author hopes that users enjoy it.
//!
#![macro_use]

macro_rules! migration_complete {
    () => {};
}

macro_rules! eliminated_text {
    () => {};
}

macro_rules! impl_debug_with_literal {
    ($impl_type:ident, $literal: expr) => {
        impl core::fmt::Debug for $impl_type {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                write!(f, $literal)?;
                Ok(())
            }
        }
    };
    ($impl_type:ident [ $($generics:tt)* ] , $literal: expr) => {
        impl<$($generics)*> core::fmt::Debug for $impl_type<$($generics)*> {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                write!(f, $literal)?;
                Ok(())
            }
        }
    };
}

macro_rules! assign {
    ($assignment:expr) => {
        {
            $assignment
        }
    };
}

macro_rules! region_forward_label {
    (|$lbl_:lifetime| {$($s: stmt)*} $lbl:lifetime <- ) => {
        #[allow(redundant_semicolons, unused_labels, unreachable_code)]
        $lbl : loop {
            $($s)*;
            break;
        }
    };
}

macro_rules! region_backward_label {
    ($lbl:lifetime <- {$($s: stmt)*} |$lbl_:lifetime| ) => {
        #[allow(redundant_semicolons, unused_labels, unreachable_code)]
        $lbl : loop {
            $($s)*;
            break;
        }
    };
}

macro_rules! goto_forward_label {
    ($lbl:lifetime) => {
        break $lbl;
    };
}

macro_rules! goto_backward_label {
    ($lbl:lifetime) => {
        continue $lbl;
    };
}

macro_rules! region_debug {
    ($($statements:tt)* ) => {
        #[cfg(all(feature = "debugging", debug_assertions))]
        {
            $($statements)*
        }
    };
}

macro_rules! region_stat {
    ($($statements:tt)* ) => {
        #[cfg(feature = "statistics")]
        {
            $($statements)*
        }
    };
}
