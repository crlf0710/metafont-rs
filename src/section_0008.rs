//! @ This program has two important variations: (1) There is a long and slow
//! version called \.{INIMF}, which does the extra calculations needed to
//! @.INIMF@>
//! initialize \MF's internal tables; and (2)~there is a shorter and faster
//! production version, which cuts the initialization to a bare minimum.
//! Parts of the program that are needed in (1) but not in (2) are delimited by
//! the codewords `$|init|\ldots|tini|$'.
//
// @d init== {change this to `$\\{init}\equiv\.{@@\{}$' in the production version}
// @d tini== {change this to `$\\{tini}\equiv\.{@@\}}$' in the production version}
// @f init==begin
// @f tini==end
pub(crate) macro_rules! region_init {
    ($($statements:tt)* ) => {
        #[cfg(not(feature = "no_init"))]
        {
            $($statements)*
        }
    };
}

pub(crate) macro_rules! items_init {
    ($($single_item:item)*) => {
        $(#[cfg(not(feature = "no_init"))]
            $single_item)*
    };
}