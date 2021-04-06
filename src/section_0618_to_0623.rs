//! @* \[29] Dynamic nonlinear equations.
//! Variables of numeric type are maintained by the general scheme of
//! independent, dependent, and known values that we have just studied;
//! and the components of pair and transform variables are handled in the
//! same way. But \MF\ also has five other types of values: \&{boolean},
//! \&{string}, \&{pen}, \&{path}, and \&{picture}; what about them?
//!
//! Equations are allowed between nonlinear quantities, but only in a
//! simple form. Two variables that haven't yet been assigned values are
//! either equal to each other, or they're not.
//!
//! Before a boolean variable has received a value, its type is |unknown_boolean|;
//! similarly, there are variables whose type is |unknown_string|, |unknown_pen|,
//! |unknown_path|, and |unknown_picture|. In such cases the value is either
//! |null| (which means that no other variables are equivalent to this one), or
//! it points to another variable of the same undefined type. The pointers in the
//! latter case form a cycle of nodes, which we shall call a ``ring.''
//! Rings of undefined variables may include capsules, which arise as
//! intermediate results within expressions or as \&{expr} parameters to macros.
//!
//! When one member of a ring receives a value, the same value is given to
//! all the other members. In the case of paths and pictures, this implies
//! making separate copies of a potentially large data structure; users should
//! restrain their enthusiasm for such generality, unless they have lots and
//! lots of memory space.
//!
//! @ The following procedure is called when a capsule node is being
//! added to a ring (e.g., when an unknown variable is mentioned in an expression).
//!
//! @p function new_ring_entry(@!p:pointer):pointer;
//! var q:pointer; {the new capsule node}
//! begin q:=get_node(value_node_size); name_type(q):=capsule;
//! type(q):=type(p);
//! if value(p)=null then value(q):=p@+else value(q):=value(p);
//! value(p):=q;
//! new_ring_entry:=q;
//! end;
//!
//! @ Conversely, we might delete a capsule or a variable before it becomes known.
//! The following procedure simply detaches a quantity from its ring,
//! without recycling the storage.
//!
//! @<Declare the recycling subroutines@>=
//! procedure ring_delete(@!p:pointer);
//! var @!q:pointer;
//! begin q:=value(p);
//! if q<>null then if q<>p then
//!   begin while value(q)<>p do q:=value(q);
//!   value(q):=value(p);
//!   end;
//! end;
//!
//! @ Eventually there might be an equation that assigns values to all of the
//! variables in a ring. The |nonlinear_eq| subroutine does the necessary
//! propagation of values.
//!
//! If the parameter |flush_p| is |true|, node |p| itself needn't receive a
//! value; it will soon be recycled.
//!
//! @p procedure nonlinear_eq(@!v:integer;@!p:pointer;@!flush_p:boolean);
//! var @!t:small_number; {the type of ring |p|}
//! @!q,@!r:pointer; {link manipulation registers}
//! begin t:=type(p)-unknown_tag; q:=value(p);
//! if flush_p then type(p):=vacuous@+else p:=q;
//! repeat r:=value(q); type(q):=t;
//! case t of
//! boolean_type: value(q):=v;
//! string_type: begin value(q):=v; add_str_ref(v);
//!   end;
//! pen_type: begin value(q):=v; add_pen_ref(v);
//!   end;
//! path_type: value(q):=copy_path(v);
//! picture_type: value(q):=copy_edges(v);
//! end; {there ain't no more cases}
//! q:=r;
//! until q=p;
//! end;
//!
//! @ If two members of rings are equated, and if they have the same type,
//! the |ring_merge| procedure is called on to make them equivalent.
//!
//! @p procedure ring_merge(@!p,@!q:pointer);
//! label exit;
//! var @!r:pointer; {traverses one list}
//! begin r:=value(p);
//! while r<>p do
//!   begin if r=q then
//!     begin @<Exclaim about a redundant equation@>;
//!     return;
//!     end;
//!   r:=value(r);
//!   end;
//! r:=value(p); value(p):=value(q); value(q):=r;
//! exit:end;
//!
//! @ @<Exclaim about a redundant equation@>=
//! begin print_err("Redundant equation");@/
//! @.Redundant equation@>
//! help2("I already knew that this equation was true.")@/
//!   ("But perhaps no harm has been done; let's continue.");@/
//! put_get_error;
//! end
//!
