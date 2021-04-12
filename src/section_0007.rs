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
