//! ` `

#[globals_struct_field(MetafontSystem)]
pub(crate) static string_pool: StringPool = StringPool::default();

#[globals_struct_use(MetafontSystem)]
use crate::section_0038::StringPool;

#[globals_struct]
#[globals_struct_field_view(StringPoolView, make_string_pool_view)]
pub(crate) mod StringPool {
    include!("src/section_0038.rs");
}

// @<Glob...@>=
// @!str_pool:packed array[pool_pointer] of packed_ASCII_code; {the characters}
/// the characters
#[globals_struct_field(StringPool)]
pub(crate) static str_pool: Box<pool_pointer_indexed_array<packed_ASCII_code>> = ZeroedDefault::zeroed_default();
// @!str_start : array[str_number] of pool_pointer; {the starting pointers}
/// the starting pointers
#[globals_struct_field(StringPool)]
pub(crate) static str_start: Box<str_number_indexed_array<pool_pointer>> = ZeroedDefault::zeroed_default();
// @!pool_ptr : pool_pointer; {first unused position in |str_pool|}
/// first unused position in `str_pool`
#[globals_struct_field(StringPool)]
pub(crate) static pool_ptr: pool_pointer = pool_pointer::default();
// @!str_ptr : str_number; {number of the current string being created}
/// number of the current string being created
#[globals_struct_field(StringPool)]
pub(crate) static str_ptr: str_number = str_number::default();
// @!init_pool_ptr : pool_pointer; {the starting value of |pool_ptr|}
/// the starting value of `pool_ptr`
#[globals_struct_field(StringPool)]
pub(crate) static init_pool_ptr: pool_pointer = pool_pointer::default();
// @!init_str_ptr : str_number; {the starting value of |str_ptr|}
/// the starting value of `str_ptr`
#[globals_struct_field(StringPool)]
pub(crate) static init_str_ptr: str_number = str_number::default();
// @!max_pool_ptr : pool_pointer; {the maximum so far of |pool_ptr|}
/// the maximum so far of `pool_ptr`
#[globals_struct_field(StringPool)]
pub(crate) static max_pool_ptr: pool_pointer = pool_pointer::default();
// @!max_str_ptr : str_number; {the maximum so far of |str_ptr|}
/// the maximum so far of `str_ptr`
#[globals_struct_field(StringPool)]
pub(crate) static max_str_ptr: str_number = str_number::default();

#[globals_struct_use(StringPool)]
use crate::pascal::ZeroedDefault;

#[globals_struct_use(StringPool)]
use crate::section_0037::pool_pointer;

#[globals_struct_use(StringPool)]
use crate::section_0037::str_number;

#[globals_struct_use(StringPool)]
use crate::section_0037::pool_pointer_indexed_array;

#[globals_struct_use(StringPool)]
use crate::section_0037::str_number_indexed_array;

#[globals_struct_use(StringPool)]
use crate::section_0037::packed_ASCII_code;

use globals_struct::{globals_struct, globals_struct_field, globals_struct_use};
