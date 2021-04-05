//! @ We want to finish the \.{GF} file if and only if it has already been started;
//! this will be true if and only if |gf_prev_ptr| is positive.
//! We want to produce a \.{TFM} file if and only if |fontmaking| is positive.
//! The \.{TFM} widths must be computed if there's a \.{GF} file, even if
//! there's going to be no \.{TFM}~file.
//!
//! We reclaim all of the variable-size memory at this point, so that
//! there is no chance of another memory overflow after the memory capacity
//! has already been exceeded.
//!
//! @<Finish the \.{TFM} and \.{GF} files@>=
//! if (gf_prev_ptr>0)or(internal[fontmaking]>0) then
//!   begin @<Make the dynamic memory into one big available node@>;
//!   @<Massage the \.{TFM} widths@>;
//!   fix_design_size; fix_check_sum;
//!   if internal[fontmaking]>0 then
//!     begin @<Massage the \.{TFM} heights, depths, and italic corrections@>;
//!     internal[fontmaking]:=0; {avoid loop in case of fatal error}
//!     @<Finish the \.{TFM} file@>;
//!     end;
//!   if gf_prev_ptr>0 then @<Finish the \.{GF} file@>;
//!   end
//!
//! @ @<Make the dynamic memory into one big available node@>=
//! rover:=lo_mem_stat_max+1; link(rover):=empty_flag; lo_mem_max:=hi_mem_min-1;
//! if lo_mem_max-rover>max_halfword then lo_mem_max:=max_halfword+rover;
//! node_size(rover):=lo_mem_max-rover; llink(rover):=rover; rlink(rover):=rover;
//! link(lo_mem_max):=null; info(lo_mem_max):=null
//!
//! @ The present section goes directly to the log file instead of using
//! |print| commands, because there's no need for these strings to take
//! up |str_pool| memory when a non-{\bf stat} version of \MF\ is being used.
//!
//! @<Output statistics...@>=
//! if log_opened then
//!   begin wlog_ln(' ');
//!   wlog_ln('Here is how much of METAFONT''s memory',' you used:');
//! @.Here is how much...@>
//!   wlog(' ',max_str_ptr-init_str_ptr:1,' string');
//!   if max_str_ptr<>init_str_ptr+1 then wlog('s');
//!   wlog_ln(' out of ', max_strings-init_str_ptr:1);@/
//!   wlog_ln(' ',max_pool_ptr-init_pool_ptr:1,' string characters out of ',
//!     pool_size-init_pool_ptr:1);@/
//!   wlog_ln(' ',lo_mem_max-mem_min+mem_end-hi_mem_min+2:1,@|
//!     ' words of memory out of ',mem_end+1-mem_min:1);@/
//!   wlog_ln(' ',st_count:1,' symbolic tokens out of ',
//!     hash_size:1);@/
//!   wlog_ln(' ',max_in_stack:1,'i,',@|
//!     int_ptr:1,'n,',@|
//!     max_rounding_ptr:1,'r,',@|
//!     max_param_stack:1,'p,',@|
//!     max_buf_stack+1:1,'b stack positions out of ',@|
//!     stack_size:1,'i,',
//!     max_internal:1,'n,',
//!     max_wiggle:1,'r,',
//!     param_size:1,'p,',
//!     buf_size:1,'b');
//!   end
//!
