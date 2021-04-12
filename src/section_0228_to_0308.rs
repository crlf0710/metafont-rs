//! @* \[15] Data structures for variables.
//! The variables of \MF\ programs can be simple, like `\.x', or they can
//! combine the structural properties of arrays and records, like `\.{x20a.b}'.
//! A \MF\ user assigns a type to a variable like \.{x20a.b} by saying, for
//! example, `\.{boolean} \.{x[]a.b}'. It's time for us to study how such
//! things are represented inside of the computer.
//!
//! Each variable value occupies two consecutive words, either in a two-word
//! node called a value node, or as a two-word subfield of a larger node.  One
//! of those two words is called the |value| field; it is an integer,
//! containing either a |scaled| numeric value or the representation of some
//! other type of quantity. (It might also be subdivided into halfwords, in
//! which case it is referred to by other names instead of |value|.) The other
//! word is broken into subfields called |type|, |name_type|, and |link|.  The
//! |type| field is a quarterword that specifies the variable's type, and
//! |name_type| is a quarterword from which \MF\ can reconstruct the
//! variable's name (sometimes by using the |link| field as well).  Thus, only
//! 1.25 words are actually devoted to the value itself; the other
//! three-quarters of a word are overhead, but they aren't wasted because they
//! allow \MF\ to deal with sparse arrays and to provide meaningful diagnostics.
//!
//! In this section we shall be concerned only with the structural aspects of
//! variables, not their values. Later parts of the program will change the
//! |type| and |value| fields, but we shall treat those fields as black boxes
//! whose contents should not be touched.
//!
//! However, if the |type| field is |structured|, there is no |value| field,
//! and the second word is broken into two pointer fields called |attr_head|
//! and |subscr_head|. Those fields point to additional nodes that
//! contain structural information, as we shall see.
//!
//! @d subscr_head_loc(#) == #+1 {where |value|, |subscr_head|, and |attr_head| are}
//! @d attr_head(#) == info(subscr_head_loc(#)) {pointer to attribute info}
//! @d subscr_head(#) == link(subscr_head_loc(#)) {pointer to subscript info}
//! @d value_node_size=2 {the number of words in a value node}
//!
//! @ An attribute node is three words long. Two of these words contain |type|
//! and |value| fields as described above, and the third word contains
//! additional information:  There is an |attr_loc| field, which contains the
//! hash address of the token that names this attribute; and there's also a
//! |parent| field, which points to the value node of |structured| type at the
//! next higher level (i.e., at the level to which this attribute is
//! subsidiary).  The |name_type| in an attribute node is `|attr|'.  The
//! |link| field points to the next attribute with the same parent; these are
//! arranged in increasing order, so that |attr_loc(link(p))>attr_loc(p)|. The
//! final attribute node links to the constant |end_attr|, whose |attr_loc|
//! field is greater than any legal hash address. The |attr_head| in the
//! parent points to a node whose |name_type| is |structured_root|; this
//! node represents the null attribute, i.e., the variable that is relevant
//! when no attributes are attached to the parent. The |attr_head| node
//! has the fields of either
//! a value node, a subscript node, or an attribute node, depending on what
//! the parent would be if it were not structured; but the subscript and
//! attribute fields are ignored, so it effectively contains only the data of
//! a value node. The |link| field in this special node points to an attribute
//! node whose |attr_loc| field is zero; the latter node represents a collective
//! subscript `\.{[]}' attached to the parent, and its |link| field points to
//! the first non-special attribute node (or to |end_attr| if there are none).
//!
//! A subscript node likewise occupies three words, with |type| and |value| fields
//! plus extra information; its |name_type| is |subscr|. In this case the
//! third word is called the |subscript| field, which is a |scaled| integer.
//! The |link| field points to the subscript node with the next larger
//! subscript, if any; otherwise the |link| points to the attribute node
//! for collective subscripts at this level. We have seen that the latter node
//! contains an upward pointer, so that the parent can be deduced.
//!
//! The |name_type| in a parent-less value node is |root|, and the |link|
//! is the hash address of the token that names this value.
//!
//! In other words, variables have a hierarchical structure that includes
//! enough threads running around so that the program is able to move easily
//! between siblings, parents, and children. An example should be helpful:
//! (The reader is advised to draw a picture while reading the following
//! description, since that will help to firm up the ideas.)
//! Suppose that `\.x' and `\.{x.a}' and `\.{x[]b}' and `\.{x5}'
//! and `\.{x20b}' have been mentioned in a user's program, where
//! \.{x[]b} has been declared to be of \&{boolean} type. Let |h(x)|, |h(a)|,
//! and |h(b)| be the hash addresses of \.x, \.a, and~\.b. Then
//! |eq_type(h(x))=tag_token| and |equiv(h(x))=p|, where |p|~is a two-word value
//! node with |name_type(p)=root| and |link(p)=h(x)|. We have |type(p)=structured|,
//! |attr_head(p)=q|, and |subscr_head(p)=r|, where |q| points to a value
//! node and |r| to a subscript node. (Are you still following this? Use
//! a pencil to draw a diagram.) The lone variable `\.x' is represented by
//! |type(q)| and |value(q)|; furthermore
//! |name_type(q)=structured_root| and |link(q)=q1|, where |q1| points
//! to an attribute node representing `\.{x[]}'. Thus |name_type(q1)=attr|,
//! |attr_loc(q1)=collective_subscript=0|, |parent(q1)=p|,
//! |type(q1)=structured|, |attr_head(q1)=qq|, and |subscr_head(q1)=qq1|;
//! |qq| is a three-word ``attribute-as-value'' node with |type(qq)=numeric_type|
//! (assuming that \.{x5} is numeric, because |qq| represents `\.{x[]}'
//! with no further attributes), |name_type(qq)=structured_root|,
//! |attr_loc(qq)=0|, |parent(qq)=p|, and
//! |link(qq)=qq1|. (Now pay attention to the next part.) Node |qq1| is
//! an attribute node representing `\.{x[][]}', which has never yet
//! occurred; its |type| field is |undefined|, and its |value| field is
//! undefined. We have |name_type(qq1)=attr|, |attr_loc(qq1)=collective_subscript|,
//! |parent(qq1)=q1|, and |link(qq1)=qq2|. Since |qq2| represents
//! `\.{x[]b}', |type(qq2)=unknown_boolean|; also |attr_loc(qq2)=h(b)|,
//! |parent(qq2)=q1|, |name_type(qq2)=attr|, |link(qq2)=end_attr|.
//! (Maybe colored lines will help untangle your picture.)
//!  Node |r| is a subscript node with |type| and |value|
//! representing `\.{x5}'; |name_type(r)=subscr|, |subscript(r)=5.0|,
//! and |link(r)=r1| is another subscript node. To complete the picture,
//! see if you can guess what |link(r1)| is; give up? It's~|q1|.
//! Furthermore |subscript(r1)=20.0|, |name_type(r1)=subscr|,
//! |type(r1)=structured|, |attr_head(r1)=qqq|, |subscr_head(r1)=qqq1|,
//! and we finish things off with three more nodes
//! |qqq|, |qqq1|, and |qqq2| hung onto~|r1|. (Perhaps you should start again
//! with a larger sheet of paper.) The value of variable `\.{x20b}'
//! appears in node~|qqq2=link(qqq1)|, as you can well imagine.
//! Similarly, the value of `\.{x.a}' appears in node |q2=link(q1)|, where
//! |attr_loc(q2)=h(a)| and |parent(q2)=p|.
//!
//! If the example in the previous paragraph doesn't make things crystal
//! clear, a glance at some of the simpler subroutines below will reveal how
//! things work out in practice.
//!
//! The only really unusual thing about these conventions is the use of
//! collective subscript attributes. The idea is to avoid repeating a lot of
//! type information when many elements of an array are identical macros
//! (for which distinct values need not be stored) or when they don't have
//! all of the possible attributes. Branches of the structure below collective
//! subscript attributes do not carry actual values except for macro identifiers;
//! branches of the structure below subscript nodes do not carry significant
//! information in their collective subscript attributes.
//!
//! @d attr_loc_loc(#)==#+2 {where the |attr_loc| and |parent| fields are}
//! @d attr_loc(#)==info(attr_loc_loc(#)) {hash address of this attribute}
//! @d parent(#)==link(attr_loc_loc(#)) {pointer to |structured| variable}
//! @d subscript_loc(#)==#+2 {where the |subscript| field lives}
//! @d subscript(#)==mem[subscript_loc(#)].sc {subscript of this variable}
//! @d attr_node_size=3 {the number of words in an attribute node}
//! @d subscr_node_size=3 {the number of words in a subscript node}
//! @d collective_subscript=0 {code for the attribute `\.{[]}'}
//!
//! @<Initialize table...@>=
//! attr_loc(end_attr):=hash_end+1; parent(end_attr):=null;
//!
//! @ Variables of type \&{pair} will have values that point to four-word
//! nodes containing two numeric values. The first of these values has
//! |name_type=x_part_sector| and the second has |name_type=y_part_sector|;
//! the |link| in the first points back to the node whose |value| points
//! to this four-word node.
//!
//! Variables of type \&{transform} are similar, but in this case their
//! |value| points to a 12-word node containing six values, identified by
//! |x_part_sector|, |y_part_sector|, |xx_part_sector|, |xy_part_sector|,
//! |yx_part_sector|, and |yy_part_sector|.
//!
//! When an entire structured variable is saved, the |root| indication
//! is temporarily replaced by |saved_root|.
//!
//! Some variables have no name; they just are used for temporary storage
//! while expressions are being evaluated. We call them {\sl capsules}.
//!
//! @d x_part_loc(#)==# {where the \&{xpart} is found in a pair or transform node}
//! @d y_part_loc(#)==#+2 {where the \&{ypart} is found in a pair or transform node}
//! @d xx_part_loc(#)==#+4 {where the \&{xxpart} is found in a transform node}
//! @d xy_part_loc(#)==#+6 {where the \&{xypart} is found in a transform node}
//! @d yx_part_loc(#)==#+8 {where the \&{yxpart} is found in a transform node}
//! @d yy_part_loc(#)==#+10 {where the \&{yypart} is found in a transform node}
//! @#
//! @d pair_node_size=4 {the number of words in a pair node}
//! @d transform_node_size=12 {the number of words in a transform node}
//!
//! @<Glob...@>=
//! @!big_node_size:array[transform_type..pair_type] of small_number;
//!
//! @ The |big_node_size| array simply contains two constants that \MF\
//! occasionally needs to know.
//!
//! @<Set init...@>=
//! big_node_size[transform_type]:=transform_node_size;
//! big_node_size[pair_type]:=pair_node_size;
//!
//! @ If |type(p)=pair_type| or |transform_type| and if |value(p)=null|, the
//! procedure call |init_big_node(p)| will allocate a pair or transform node
//! for~|p|.  The individual parts of such nodes are initially of type
//! |independent|.
//!
//! @p procedure init_big_node(@!p:pointer);
//! var @!q:pointer; {the new node}
//! @!s:small_number; {its size}
//! begin s:=big_node_size[type(p)]; q:=get_node(s);
//! repeat s:=s-2; @<Make variable |q+s| newly independent@>;
//! name_type(q+s):=half(s)+x_part_sector; link(q+s):=null;
//! until s=0;
//! link(q):=p; value(p):=q;
//! end;
//!
//! @ The |id_transform| function creates a capsule for the
//! identity transformation.
//!
//! @p function id_transform:pointer;
//! var @!p,@!q,@!r:pointer; {list manipulation registers}
//! begin p:=get_node(value_node_size); type(p):=transform_type;
//! name_type(p):=capsule; value(p):=null; init_big_node(p); q:=value(p);
//! r:=q+transform_node_size;
//! repeat r:=r-2;
//! type(r):=known; value(r):=0;
//! until r=q;
//! value(xx_part_loc(q)):=unity; value(yy_part_loc(q)):=unity;
//! id_transform:=p;
//! end;
//!
//! @ Tokens are of type |tag_token| when they first appear, but they point
//! to |null| until they are first used as the root of a variable.
//! The following subroutine establishes the root node on such grand occasions.
//!
//! @p procedure new_root(@!x:pointer);
//! var @!p:pointer; {the new node}
//! begin p:=get_node(value_node_size); type(p):=undefined; name_type(p):=root;
//! link(p):=x; equiv(x):=p;
//! end;
//!
//! @ These conventions for variable representation are illustrated by the
//! |print_variable_name| routine, which displays the full name of a
//! variable given only a pointer to its two-word value packet.
//!
//! @p procedure print_variable_name(@!p:pointer);
//! label found,exit;
//! var @!q:pointer; {a token list that will name the variable's suffix}
//! @!r:pointer; {temporary for token list creation}
//! begin while name_type(p)>=x_part_sector do
//!   @<Preface the output with a part specifier; |return| in the
//!     case of a capsule@>;
//! q:=null;
//! while name_type(p)>saved_root do
//!   @<Ascend one level, pushing a token onto list |q|
//!    and replacing |p| by its parent@>;
//! r:=get_avail; info(r):=link(p); link(r):=q;
//! if name_type(p)=saved_root then print("(SAVED)");
//! @.SAVED@>
//! show_token_list(r,null,el_gordo,tally); flush_token_list(r);
//! exit:end;
//!
//! @ @<Ascend one level, pushing a token onto list |q|...@>=
//! begin if name_type(p)=subscr then
//!   begin r:=new_num_tok(subscript(p));
//!   repeat p:=link(p);
//!   until name_type(p)=attr;
//!   end
//! else if name_type(p)=structured_root then
//!     begin p:=link(p); goto found;
//!     end
//! else  begin if name_type(p)<>attr then confusion("var");
//! @:this can't happen var}{\quad var@>
//!   r:=get_avail; info(r):=attr_loc(p);
//!   end;
//! link(r):=q; q:=r;
//! found:  p:=parent(p);
//! end
//!
//! @ @<Preface the output with a part specifier...@>=
//! begin case name_type(p) of
//! x_part_sector: print_char("x");
//! y_part_sector: print_char("y");
//! xx_part_sector: print("xx");
//! xy_part_sector: print("xy");
//! yx_part_sector: print("yx");
//! yy_part_sector: print("yy");
//! capsule: begin print("%CAPSULE"); print_int(p-null); return;
//! @.CAPSULE@>
//!   end;
//! end; {there are no other cases}
//! print("part "); p:=link(p-2*(name_type(p)-x_part_sector));
//! end
//!
//! @ The |interesting| function returns |true| if a given variable is not
//! in a capsule, or if the user wants to trace capsules.
//!
//! @p function interesting(@!p:pointer):boolean;
//! var @!t:small_number; {a |name_type|}
//! begin if internal[tracing_capsules]>0 then interesting:=true
//! else  begin t:=name_type(p);
//!   if t>=x_part_sector then if t<>capsule then
//!     t:=name_type(link(p-2*(t-x_part_sector)));
//!   interesting:=(t<>capsule);
//!   end;
//! end;
//!
//! @ Now here is a subroutine that converts an unstructured type into an
//! equivalent structured type, by inserting a |structured| node that is
//! capable of growing. This operation is done only when |name_type(p)=root|,
//! |subscr|, or |attr|.
//!
//! The procedure returns a pointer to the new node that has taken node~|p|'s
//! place in the structure. Node~|p| itself does not move, nor are its
//! |value| or |type| fields changed in any way.
//!
//! @p function new_structure(@!p:pointer):pointer;
//! var @!q,@!r:pointer; {list manipulation registers}
//! begin case name_type(p) of
//! root: begin q:=link(p); r:=get_node(value_node_size); equiv(q):=r;
//!   end;
//! subscr: @<Link a new subscript node |r| in place of node |p|@>;
//! attr: @<Link a new attribute node |r| in place of node |p|@>;
//! othercases confusion("struct")
//! @:this can't happen struct}{\quad struct@>
//! endcases;@/
//! link(r):=link(p); type(r):=structured; name_type(r):=name_type(p);
//! attr_head(r):=p; name_type(p):=structured_root;@/
//! q:=get_node(attr_node_size); link(p):=q; subscr_head(r):=q;
//! parent(q):=r; type(q):=undefined; name_type(q):=attr; link(q):=end_attr;
//! attr_loc(q):=collective_subscript; new_structure:=r;
//! end;
//!
//! @ @<Link a new subscript node |r| in place of node |p|@>=
//! begin q:=p;
//! repeat q:=link(q);
//! until name_type(q)=attr;
//! q:=parent(q); r:=subscr_head_loc(q); {|link(r)=subscr_head(q)|}
//! repeat q:=r; r:=link(r);
//! until r=p;
//! r:=get_node(subscr_node_size);
//! link(q):=r; subscript(r):=subscript(p);
//! end
//!
//! @ If the attribute is |collective_subscript|, there are two pointers to
//! node~|p|, so we must change both of them.
//!
//! @<Link a new attribute node |r| in place of node |p|@>=
//! begin q:=parent(p); r:=attr_head(q);
//! repeat q:=r; r:=link(r);
//! until r=p;
//! r:=get_node(attr_node_size); link(q):=r;@/
//! mem[attr_loc_loc(r)]:=mem[attr_loc_loc(p)]; {copy |attr_loc| and |parent|}
//! if attr_loc(p)=collective_subscript then
//!   begin q:=subscr_head_loc(parent(p));
//!   while link(q)<>p do q:=link(q);
//!   link(q):=r;
//!   end;
//! end
//!
//! @ The |find_variable| routine is given a pointer~|t| to a nonempty token
//! list of suffixes; it returns a pointer to the corresponding two-word
//! value. For example, if |t| points to token \.x followed by a numeric
//! token containing the value~7, |find_variable| finds where the value of
//! \.{x7} is stored in memory. This may seem a simple task, and it
//! usually is, except when \.{x7} has never been referenced before.
//! Indeed, \.x may never have even been subscripted before; complexities
//! arise with respect to updating the collective subscript information.
//!
//! If a macro type is detected anywhere along path~|t|, or if the first
//! item on |t| isn't a |tag_token|, the value |null| is returned.
//! Otherwise |p| will be a non-null pointer to a node such that
//! |undefined<type(p)<structured|.
//!
//! @d abort_find==begin find_variable:=null; return;@+end
//!
//! @p function find_variable(@!t:pointer):pointer;
//! label exit;
//! var @!p,@!q,@!r,@!s:pointer; {nodes in the ``value'' line}
//! @!pp,@!qq,@!rr,@!ss:pointer; {nodes in the ``collective'' line}
//! @!n:integer; {subscript or attribute}
//! @!save_word:memory_word; {temporary storage for a word of |mem|}
//! @^inner loop@>
//! begin p:=info(t); t:=link(t);
//! if eq_type(p) mod outer_tag<>tag_token then abort_find;
//! if equiv(p)=null then new_root(p);
//! p:=equiv(p); pp:=p;
//! while t<>null do
//!   begin @<Make sure that both nodes |p| and |pp| are of |structured| type@>;
//!   if t<hi_mem_min then
//!     @<Descend one level for the subscript |value(t)|@>
//!   else @<Descend one level for the attribute |info(t)|@>;
//!   t:=link(t);
//!   end;
//! if type(pp)>=structured then
//!   if type(pp)=structured then pp:=attr_head(pp)@+else abort_find;
//! if type(p)=structured then p:=attr_head(p);
//! if type(p)=undefined then
//!   begin if type(pp)=undefined then
//!     begin type(pp):=numeric_type; value(pp):=null;
//!     end;
//!   type(p):=type(pp); value(p):=null;
//!   end;
//! find_variable:=p;
//! exit:end;
//!
//! @ Although |pp| and |p| begin together, they diverge when a subscript occurs;
//! |pp|~stays in the collective line while |p|~goes through actual subscript
//! values.
//!
//! @<Make sure that both nodes |p| and |pp|...@>=
//! if type(pp)<>structured then
//!   begin if type(pp)>structured then abort_find;
//!   ss:=new_structure(pp);
//!   if p=pp then p:=ss;
//!   pp:=ss;
//!   end; {now |type(pp)=structured|}
//! if type(p)<>structured then {it cannot be |>structured|}
//!   p:=new_structure(p) {now |type(p)=structured|}
//!
//! @ We want this part of the program to be reasonably fast, in case there are
//! @^inner loop@>
//! lots of subscripts at the same level of the data structure. Therefore
//! we store an ``infinite'' value in the word that appears at the end of the
//! subscript list, even though that word isn't part of a subscript node.
//!
//! @<Descend one level for the subscript |value(t)|@>=
//! begin n:=value(t);
//! pp:=link(attr_head(pp)); {now |attr_loc(pp)=collective_subscript|}
//! q:=link(attr_head(p)); save_word:=mem[subscript_loc(q)];
//! subscript(q):=el_gordo; s:=subscr_head_loc(p); {|link(s)=subscr_head(p)|}
//! repeat r:=s; s:=link(s);
//! until n<=subscript(s);
//! if n=subscript(s) then p:=s
//! else  begin p:=get_node(subscr_node_size); link(r):=p; link(p):=s;
//!   subscript(p):=n; name_type(p):=subscr; type(p):=undefined;
//!   end;
//! mem[subscript_loc(q)]:=save_word;
//! end
//!
//! @ @<Descend one level for the attribute |info(t)|@>=
//! begin n:=info(t);
//! ss:=attr_head(pp);
//! repeat rr:=ss; ss:=link(ss);
//! until n<=attr_loc(ss);
//! if n<attr_loc(ss) then
//!   begin qq:=get_node(attr_node_size); link(rr):=qq; link(qq):=ss;
//!   attr_loc(qq):=n; name_type(qq):=attr; type(qq):=undefined;
//!   parent(qq):=pp; ss:=qq;
//!   end;
//! if p=pp then
//!   begin p:=ss; pp:=ss;
//!   end
//! else  begin pp:=ss; s:=attr_head(p);
//!   repeat r:=s; s:=link(s);
//!   until n<=attr_loc(s);
//!   if n=attr_loc(s) then p:=s
//!   else  begin q:=get_node(attr_node_size); link(r):=q; link(q):=s;
//!     attr_loc(q):=n; name_type(q):=attr; type(q):=undefined;
//!     parent(q):=p; p:=q;
//!     end;
//!   end;
//! end
//!
//! @ Variables lose their former values when they appear in a type declaration,
//! or when they are defined to be macros or \&{let} equal to something else.
//! A subroutine will be defined later that recycles the storage associated
//! with any particular |type| or |value|; our goal now is to study a higher
//! level process called |flush_variable|, which selectively frees parts of a
//! variable structure.
//!
//! This routine has some complexity because of examples such as
//! `\hbox{\tt numeric x[]a[]b}',
//! which recycles all variables of the form \.{x[i]a[j]b} (and no others), while
//! `\hbox{\tt vardef x[]a[]=...}'
//! discards all variables of the form \.{x[i]a[j]} followed by an arbitrary
//! suffix, except for the collective node \.{x[]a[]} itself. The obvious way
//! to handle such examples is to use recursion; so that's what we~do.
//! @^recursion@>
//!
//! Parameter |p| points to the root information of the variable;
//! parameter |t| points to a list of one-word nodes that represent
//! suffixes, with |info=collective_subscript| for subscripts.
//!
//! @p @t\4@>@<Declare subroutines for printing expressions@>@;@/
//! @t\4@>@<Declare basic dependency-list subroutines@>@;
//! @t\4@>@<Declare the recycling subroutines@>@;
//! @t\4@>@<Declare the procedure called |flush_cur_exp|@>@;
//! @t\4@>@<Declare the procedure called |flush_below_variable|@>@;
//! procedure flush_variable(@!p,@!t:pointer;@!discard_suffixes:boolean);
//! label exit;
//! var @!q,@!r:pointer; {list manipulation}
//! @!n:halfword; {attribute to match}
//! begin while t<>null do
//!   begin if type(p)<>structured then return;
//!   n:=info(t); t:=link(t);
//!   if n=collective_subscript then
//!     begin r:=subscr_head_loc(p); q:=link(r); {|q=subscr_head(p)|}
//!     while name_type(q)=subscr do
//!       begin flush_variable(q,t,discard_suffixes);
//!       if t=null then
//!         if type(q)=structured then r:=q
//!         else  begin link(r):=link(q); free_node(q,subscr_node_size);
//!           end
//!       else r:=q;
//!       q:=link(r);
//!       end;
//!     end;
//!   p:=attr_head(p);
//!   repeat r:=p; p:=link(p);
//!   until attr_loc(p)>=n;
//!   if attr_loc(p)<>n then return;
//!   end;
//! if discard_suffixes then flush_below_variable(p)
//! else  begin if type(p)=structured then p:=attr_head(p);
//!   recycle_value(p);
//!   end;
//! exit:end;
//!
//! @ The next procedure is simpler; it wipes out everything but |p| itself,
//! which becomes undefined.
//!
//! @<Declare the procedure called |flush_below_variable|@>=
//! procedure flush_below_variable(@!p:pointer);
//! var @!q,@!r:pointer; {list manipulation registers}
//! begin if type(p)<>structured then
//!   recycle_value(p) {this sets |type(p)=undefined|}
//! else  begin q:=subscr_head(p);
//!   while name_type(q)=subscr do
//!     begin flush_below_variable(q); r:=q; q:=link(q);
//!     free_node(r,subscr_node_size);
//!     end;
//!   r:=attr_head(p); q:=link(r); recycle_value(r);
//!   if name_type(p)<=saved_root then free_node(r,value_node_size)
//!   else free_node(r,subscr_node_size);
//!     {we assume that |subscr_node_size=attr_node_size|}
//!   repeat flush_below_variable(q); r:=q; q:=link(q); free_node(r,attr_node_size);
//!   until q=end_attr;
//!   type(p):=undefined;
//!   end;
//! end;
//!
//! @ Just before assigning a new value to a variable, we will recycle the
//! old value and make the old value undefined. The |und_type| routine
//! determines what type of undefined value should be given, based on
//! the current type before recycling.
//!
//! @p function und_type(@!p:pointer):small_number;
//! begin case type(p) of
//! undefined,vacuous:und_type:=undefined;
//! boolean_type,unknown_boolean:und_type:=unknown_boolean;
//! string_type,unknown_string:und_type:=unknown_string;
//! pen_type,unknown_pen,future_pen:und_type:=unknown_pen;
//! path_type,unknown_path:und_type:=unknown_path;
//! picture_type,unknown_picture:und_type:=unknown_picture;
//! transform_type,pair_type,numeric_type:und_type:=type(p);
//! known,dependent,proto_dependent,independent:und_type:=numeric_type;
//! end; {there are no other cases}
//! end;
//!
//! @ The |clear_symbol| routine is used when we want to redefine the equivalent
//! of a symbolic token. It must remove any variable structure or macro
//! definition that is currently attached to that symbol. If the |saving|
//! parameter is true, a subsidiary structure is saved instead of destroyed.
//!
//! @p procedure clear_symbol(@!p:pointer;@!saving:boolean);
//! var @!q:pointer; {|equiv(p)|}
//! begin q:=equiv(p);
//! case eq_type(p) mod outer_tag of
//! defined_macro,secondary_primary_macro,tertiary_secondary_macro,
//!  expression_tertiary_macro: if not saving then delete_mac_ref(q);
//! tag_token:if q<>null then
//!   if saving then name_type(q):=saved_root
//!   else  begin flush_below_variable(q); free_node(q,value_node_size);
//!     end;@;
//! othercases do_nothing
//! endcases;@/
//! eqtb[p]:=eqtb[frozen_undefined];
//! end;
//!
//! @* \[16] Saving and restoring equivalents.
//! The nested structure provided by \&{begingroup} and \&{endgroup}
//! allows |eqtb| entries to be saved and restored, so that temporary changes
//! can be made without difficulty.  When the user requests a current value to
//! be saved, \MF\ puts that value into its ``save stack.'' An appearance of
//! \&{endgroup} ultimately causes the old values to be removed from the save
//! stack and put back in their former places.
//!
//! The save stack is a linked list containing three kinds of entries,
//! distinguished by their |info| fields. If |p| points to a saved item,
//! then
//!
//! \smallskip\hang
//! |info(p)=0| stands for a group boundary; each \&{begingroup} contributes
//! such an item to the save stack and each \&{endgroup} cuts back the stack
//! until the most recent such entry has been removed.
//!
//! \smallskip\hang
//! |info(p)=q|, where |1<=q<=hash_end|, means that |mem[p+1]| holds the former
//! contents of |eqtb[q]|. Such save stack entries are generated by \&{save}
//! commands.
//!
//! \smallskip\hang
//! |info(p)=hash_end+q|, where |q>0|, means that |value(p)| is a |scaled|
//! integer to be restored to internal parameter number~|q|. Such entries
//! are generated by \&{interim} commands.
//!
//! \smallskip\noindent
//! The global variable |save_ptr| points to the top item on the save stack.
//!
//! @d save_node_size=2 {number of words per non-boundary save-stack node}
//! @d saved_equiv(#)==mem[#+1].hh {where an |eqtb| entry gets saved}
//! @d save_boundary_item(#)==begin #:=get_avail; info(#):=0;
//!   link(#):=save_ptr; save_ptr:=#;
//!   end
//!
//! @<Glob...@>=@!save_ptr:pointer; {the most recently saved item}
//!
//! @ @<Set init...@>=save_ptr:=null;
//!
//! @ The |save_variable| routine is given a hash address |q|; it salts this
//! address away in the save stack, together with its current equivalent,
//! then makes token~|q| behave as though it were brand new.
//!
//! Nothing is stacked when |save_ptr=null|, however; there's no way to remove
//! things from the stack when the program is not inside a group, so there's
//! no point in wasting the space.
//!
//! @p procedure save_variable(@!q:pointer);
//! var @!p:pointer; {temporary register}
//! begin if save_ptr<>null then
//!   begin p:=get_node(save_node_size); info(p):=q; link(p):=save_ptr;
//!   saved_equiv(p):=eqtb[q]; save_ptr:=p;
//!   end;
//! clear_symbol(q,(save_ptr<>null));
//! end;
//!
//! @ Similarly, |save_internal| is given the location |q| of an internal
//! quantity like |tracing_pens|. It creates a save stack entry of the
//! third kind.
//!
//! @p procedure save_internal(@!q:halfword);
//! var @!p:pointer; {new item for the save stack}
//! begin if save_ptr<>null then
//!   begin p:=get_node(save_node_size); info(p):=hash_end+q;
//!   link(p):=save_ptr; value(p):=internal[q]; save_ptr:=p;
//!   end;
//! end;
//!
//! @ At the end of a group, the |unsave| routine restores all of the saved
//! equivalents in reverse order. This routine will be called only when there
//! is at least one boundary item on the save stack.
//!
//! @p procedure unsave;
//! var @!q:pointer; {index to saved item}
//! @!p:pointer; {temporary register}
//! begin while info(save_ptr)<>0 do
//!   begin q:=info(save_ptr);
//!   if q>hash_end then
//!     begin if internal[tracing_restores]>0 then
//!       begin begin_diagnostic; print_nl("{restoring ");
//!       slow_print(int_name[q-(hash_end)]); print_char("=");
//!       print_scaled(value(save_ptr)); print_char("}");
//!       end_diagnostic(false);
//!       end;
//!     internal[q-(hash_end)]:=value(save_ptr);
//!     end
//!   else  begin if internal[tracing_restores]>0 then
//!       begin begin_diagnostic; print_nl("{restoring ");
//!       slow_print(text(q)); print_char("}");
//!       end_diagnostic(false);
//!       end;
//!     clear_symbol(q,false);
//!     eqtb[q]:=saved_equiv(save_ptr);
//!     if eq_type(q) mod outer_tag=tag_token then
//!       begin p:=equiv(q);
//!       if p<>null then name_type(p):=root;
//!       end;
//!     end;
//!   p:=link(save_ptr); free_node(save_ptr,save_node_size); save_ptr:=p;
//!   end;
//! p:=link(save_ptr); free_avail(save_ptr); save_ptr:=p;
//! end;
//!
//! @* \[17] Data structures for paths.
//! When a \MF\ user specifies a path, \MF\ will create a list of knots
//! and control points for the associated cubic spline curves. If the
//! knots are $z_0$, $z_1$, \dots, $z_n$, there are control points
//! $z_k^+$ and $z_{k+1}^-$ such that the cubic splines between knots
//! $z_k$ and $z_{k+1}$ are defined by B\'ezier's formula
//! @:Bezier}{B\'ezier, Pierre Etienne@>
//! $$\eqalign{z(t)&=B(z_k,z_k^+,z_{k+1}^-,z_{k+1};t)\cr
//! &=(1-t)^3z_k+3(1-t)^2tz_k^++3(1-t)t^2z_{k+1}^-+t^3z_{k+1}\cr}$$
//! for |0<=t<=1|.
//!
//! There is a 7-word node for each knot $z_k$, containing one word of
//! control information and six words for the |x| and |y| coordinates
//! of $z_k^-$ and $z_k$ and~$z_k^+$. The control information appears
//! in the |left_type| and |right_type| fields, which each occupy
//! a quarter of the first word in the node; they specify properties
//! of the curve as it enters and leaves the knot. There's also a
//! halfword |link| field, which points to the following knot.
//!
//! If the path is a closed contour, knots 0 and |n| are identical;
//! i.e., the |link| in knot |n-1| points to knot~0. But if the path
//! is not closed, the |left_type| of knot~0 and the |right_type| of knot~|n|
//! are equal to |endpoint|. In the latter case the |link| in knot~|n| points
//! to knot~0, and the control points $z_0^-$ and $z_n^+$ are not used.
//!
//! @d left_type(#) == mem[#].hh.b0 {characterizes the path entering this knot}
//! @d right_type(#) == mem[#].hh.b1 {characterizes the path leaving this knot}
//! @d endpoint=0 {|left_type| at path beginning and |right_type| at path end}
//! @d x_coord(#) == mem[#+1].sc {the |x| coordinate of this knot}
//! @d y_coord(#) == mem[#+2].sc {the |y| coordinate of this knot}
//! @d left_x(#) == mem[#+3].sc {the |x| coordinate of previous control point}
//! @d left_y(#) == mem[#+4].sc {the |y| coordinate of previous control point}
//! @d right_x(#) == mem[#+5].sc {the |x| coordinate of next control point}
//! @d right_y(#) == mem[#+6].sc {the |y| coordinate of next control point}
//! @d knot_node_size=7 {number of words in a knot node}
//!
//! @ Before the B\'ezier control points have been calculated, the memory
//! space they will ultimately occupy is taken up by information that can be
//! used to compute them. There are four cases:
//!
//! \yskip
//! \textindent{$\bullet$} If |right_type=open|, the curve should leave
//! the knot in the same direction it entered; \MF\ will figure out a
//! suitable direction.
//!
//! \yskip
//! \textindent{$\bullet$} If |right_type=curl|, the curve should leave the
//! knot in a direction depending on the angle at which it enters the next
//! knot and on the curl parameter stored in |right_curl|.
//!
//! \yskip
//! \textindent{$\bullet$} If |right_type=given|, the curve should leave the
//! knot in a nonzero direction stored as an |angle| in |right_given|.
//!
//! \yskip
//! \textindent{$\bullet$} If |right_type=explicit|, the B\'ezier control
//! point for leaving this knot has already been computed; it is in the
//! |right_x| and |right_y| fields.
//!
//! \yskip\noindent
//! The rules for |left_type| are similar, but they refer to the curve entering
//! the knot, and to \\{left} fields instead of \\{right} fields.
//!
//! Non-|explicit| control points will be chosen based on ``tension'' parameters
//! in the |left_tension| and |right_tension| fields. The
//! `\&{atleast}' option is represented by negative tension values.
//! @:at_least_}{\&{atleast} primitive@>
//!
//! For example, the \MF\ path specification
//! $$\.{z0..z1..tension atleast 1..\{curl 2\}z2..z3\{-1,-2\}..tension
//!   3 and 4..p},$$
//! where \.p is the path `\.{z4..controls z45 and z54..z5}', will be represented
//! by the six knots
//! \def\lodash{\hbox to 1.1em{\thinspace\hrulefill\thinspace}}
//! $$\vbox{\halign{#\hfil&&\qquad#\hfil\cr
//! |left_type|&\\{left} info&|x_coord,y_coord|&|right_type|&\\{right} info\cr
//! \noalign{\yskip}
//! |endpoint|&\lodash$,\,$\lodash&$x_0,y_0$&|curl|&$1.0,1.0$\cr
//! |open|&\lodash$,1.0$&$x_1,y_1$&|open|&\lodash$,-1.0$\cr
//! |curl|&$2.0,-1.0$&$x_2,y_2$&|curl|&$2.0,1.0$\cr
//! |given|&$d,1.0$&$x_3,y_3$&|given|&$d,3.0$\cr
//! |open|&\lodash$,4.0$&$x_4,y_4$&|explicit|&$x_{45},y_{45}$\cr
//! |explicit|&$x_{54},y_{54}$&$x_5,y_5$&|endpoint|&\lodash$,\,$\lodash\cr}}$$
//! Here |d| is the |angle| obtained by calling |n_arg(-unity,-two)|.
//! Of course, this example is more complicated than anything a normal user
//! would ever write.
//!
//! These types must satisfy certain restrictions because of the form of \MF's
//! path syntax:
//! (i)~|open| type never appears in the same node together with |endpoint|,
//! |given|, or |curl|.
//! (ii)~The |right_type| of a node is |explicit| if and only if the
//! |left_type| of the following node is |explicit|.
//! (iii)~|endpoint| types occur only at the ends, as mentioned above.
//!
//! @d left_curl==left_x {curl information when entering this knot}
//! @d left_given==left_x {given direction when entering this knot}
//! @d left_tension==left_y {tension information when entering this knot}
//! @d right_curl==right_x {curl information when leaving this knot}
//! @d right_given==right_x {given direction when leaving this knot}
//! @d right_tension==right_y {tension information when leaving this knot}
//! @d explicit=1 {|left_type| or |right_type| when control points are known}
//! @d given=2 {|left_type| or |right_type| when a direction is given}
//! @d curl=3 {|left_type| or |right_type| when a curl is desired}
//! @d open=4 {|left_type| or |right_type| when \MF\ should choose the direction}
//!
//! @ Here is a diagnostic routine that prints a given knot list
//! in symbolic form. It illustrates the conventions discussed above,
//! and checks for anomalies that might arise while \MF\ is being debugged.
//!
//! @<Declare subroutines for printing expressions@>=
//! procedure print_path(@!h:pointer;@!s:str_number;@!nuline:boolean);
//! label done,done1;
//! var @!p,@!q:pointer; {for list traversal}
//! begin print_diagnostic("Path",s,nuline); print_ln;
//! @.Path at line...@>
//! p:=h;
//! repeat q:=link(p);
//! if (p=null)or(q=null) then
//!   begin print_nl("???"); goto done; {this won't happen}
//! @.???@>
//!   end;
//! @<Print information for adjacent knots |p| and |q|@>;
//! p:=q;
//! if (p<>h)or(left_type(h)<>endpoint) then
//!   @<Print two dots, followed by |given| or |curl| if present@>;
//! until p=h;
//! if left_type(h)<>endpoint then print("cycle");
//! done:end_diagnostic(true);
//! end;
//!
//! @ @<Print information for adjacent knots...@>=
//! print_two(x_coord(p),y_coord(p));
//! case right_type(p) of
//! endpoint: begin if left_type(p)=open then print("{open?}"); {can't happen}
//! @.open?@>
//!   if (left_type(q)<>endpoint)or(q<>h) then q:=null; {force an error}
//!   goto done1;
//!   end;
//! explicit: @<Print control points between |p| and |q|, then |goto done1|@>;
//! open: @<Print information for a curve that begins |open|@>;
//! curl,given: @<Print information for a curve that begins |curl| or |given|@>;
//! othercases print("???") {can't happen}
//! @.???@>
//! endcases;@/
//! if left_type(q)<=explicit then print("..control?") {can't happen}
//! @.control?@>
//! else if (right_tension(p)<>unity)or(left_tension(q)<>unity) then
//!   @<Print tension between |p| and |q|@>;
//! done1:
//!
//! @ Since |n_sin_cos| produces |fraction| results, which we will print as if they
//! were |scaled|, the magnitude of a |given| direction vector will be~4096.
//!
//! @<Print two dots...@>=
//! begin print_nl(" ..");
//! if left_type(p)=given then
//!   begin n_sin_cos(left_given(p)); print_char("{");
//!   print_scaled(n_cos); print_char(",");
//!   print_scaled(n_sin); print_char("}");
//!   end
//! else if left_type(p)=curl then
//!   begin print("{curl "); print_scaled(left_curl(p)); print_char("}");
//!   end;
//! end
//!
//! @ @<Print tension between |p| and |q|@>=
//! begin print("..tension ");
//! if right_tension(p)<0 then print("atleast");
//! print_scaled(abs(right_tension(p)));
//! if right_tension(p)<>left_tension(q) then
//!   begin print(" and ");
//!   if left_tension(q)<0 then print("atleast");
//!   print_scaled(abs(left_tension(q)));
//!   end;
//! end
//!
//! @ @<Print control points between |p| and |q|, then |goto done1|@>=
//! begin print("..controls "); print_two(right_x(p),right_y(p)); print(" and ");
//! if left_type(q)<>explicit then print("??") {can't happen}
//! @.??@>
//! else print_two(left_x(q),left_y(q));
//! goto done1;
//! end
//!
//! @ @<Print information for a curve that begins |open|@>=
//! if (left_type(p)<>explicit)and(left_type(p)<>open) then
//!   print("{open?}") {can't happen}
//! @.open?@>
//!
//! @ A curl of 1 is shown explicitly, so that the user sees clearly that
//! \MF's default curl is present.
//!
//! @<Print information for a curve that begins |curl|...@>=
//! begin if left_type(p)=open then print("??"); {can't happen}
//! @.??@>
//! if right_type(p)=curl then
//!   begin print("{curl "); print_scaled(right_curl(p));
//!   end
//! else  begin n_sin_cos(right_given(p)); print_char("{");
//!   print_scaled(n_cos); print_char(","); print_scaled(n_sin);
//!   end;
//! print_char("}");
//! end
//!
//! @ If we want to duplicate a knot node, we can say |copy_knot|:
//!
//! @p function copy_knot(@!p:pointer):pointer;
//! var @!q:pointer; {the copy}
//! @!k:0..knot_node_size-1; {runs through the words of a knot node}
//! begin q:=get_node(knot_node_size);
//! for k:=0 to knot_node_size-1 do mem[q+k]:=mem[p+k];
//! copy_knot:=q;
//! end;
//!
//! @ The |copy_path| routine makes a clone of a given path.
//!
//! @p function copy_path(@!p:pointer):pointer;
//! label exit;
//! var @!q,@!pp,@!qq:pointer; {for list manipulation}
//! begin q:=get_node(knot_node_size); {this will correspond to |p|}
//! qq:=q; pp:=p;
//! loop@+  begin left_type(qq):=left_type(pp);
//!   right_type(qq):=right_type(pp);@/
//!   x_coord(qq):=x_coord(pp); y_coord(qq):=y_coord(pp);@/
//!   left_x(qq):=left_x(pp); left_y(qq):=left_y(pp);@/
//!   right_x(qq):=right_x(pp); right_y(qq):=right_y(pp);@/
//!   if link(pp)=p then
//!     begin link(qq):=q; copy_path:=q; return;
//!     end;
//!   link(qq):=get_node(knot_node_size); qq:=link(qq); pp:=link(pp);
//!   end;
//! exit:end;
//!
//! @ Similarly, there's a way to copy the {\sl reverse\/} of a path. This procedure
//! returns a pointer to the first node of the copy, if the path is a cycle,
//! but to the final node of a non-cyclic copy. The global
//! variable |path_tail| will point to the final node of the original path;
//! this trick makes it easier to implement `\&{doublepath}'.
//!
//! All node types are assumed to be |endpoint| or |explicit| only.
//!
//! @p function htap_ypoc(@!p:pointer):pointer;
//! label exit;
//! var @!q,@!pp,@!qq,@!rr:pointer; {for list manipulation}
//! begin q:=get_node(knot_node_size); {this will correspond to |p|}
//! qq:=q; pp:=p;
//! loop@+  begin right_type(qq):=left_type(pp); left_type(qq):=right_type(pp);@/
//!   x_coord(qq):=x_coord(pp); y_coord(qq):=y_coord(pp);@/
//!   right_x(qq):=left_x(pp); right_y(qq):=left_y(pp);@/
//!   left_x(qq):=right_x(pp); left_y(qq):=right_y(pp);@/
//!   if link(pp)=p then
//!     begin link(q):=qq; path_tail:=pp; htap_ypoc:=q; return;
//!     end;
//!   rr:=get_node(knot_node_size); link(rr):=qq; qq:=rr; pp:=link(pp);
//!   end;
//! exit:end;
//!
//! @ @<Glob...@>=
//! @!path_tail:pointer; {the node that links to the beginning of a path}
//!
//! @ When a cyclic list of knot nodes is no longer needed, it can be recycled by
//! calling the following subroutine.
//!
//! @<Declare the recycling subroutines@>=
//! procedure toss_knot_list(@!p:pointer);
//! var @!q:pointer; {the node being freed}
//! @!r:pointer; {the next node}
//! begin q:=p;
//! repeat r:=link(q); free_node(q,knot_node_size); q:=r;
//! until q=p;
//! end;
//!
//! @* \[18] Choosing control points.
//! Now we must actually delve into one of \MF's more difficult routines,
//! the |make_choices| procedure that chooses angles and control points for
//! the splines of a curve when the user has not specified them explicitly.
//! The parameter to |make_choices| points to a list of knots and
//! path information, as described above.
//!
//! A path decomposes into independent segments at ``breakpoint'' knots,
//! which are knots whose left and right angles are both prespecified in
//! some way (i.e., their |left_type| and |right_type| aren't both open).
//!
//! @p @t\4@>@<Declare the procedure called |solve_choices|@>@;
//! procedure make_choices(@!knots:pointer);
//! label done;
//! var @!h:pointer; {the first breakpoint}
//! @!p,@!q:pointer; {consecutive breakpoints being processed}
//! @<Other local variables for |make_choices|@>@;
//! begin check_arith; {make sure that |arith_error=false|}
//! if internal[tracing_choices]>0 then
//!   print_path(knots,", before choices",true);
//! @<If consecutive knots are equal, join them explicitly@>;
//! @<Find the first breakpoint, |h|, on the path;
//!   insert an artificial breakpoint if the path is an unbroken cycle@>;
//! p:=h;
//! repeat @<Fill in the control points between |p| and the next breakpoint,
//!   then advance |p| to that breakpoint@>;
//! until p=h;
//! if internal[tracing_choices]>0 then
//!   print_path(knots,", after choices",true);
//! if arith_error then @<Report an unexpected problem during the choice-making@>;
//! end;
//!
//! @ @<Report an unexpected problem during the choice...@>=
//! begin print_err("Some number got too big");
//! @.Some number got too big@>
//! help2("The path that I just computed is out of range.")@/
//!   ("So it will probably look funny. Proceed, for a laugh.");
//! put_get_error; arith_error:=false;
//! end
//!
//! @ Two knots in a row with the same coordinates will always be joined
//! by an explicit ``curve'' whose control points are identical with the
//! knots.
//!
//! @<If consecutive knots are equal, join them explicitly@>=
//! p:=knots;
//! repeat q:=link(p);
//! if x_coord(p)=x_coord(q) then if y_coord(p)=y_coord(q) then
//!  if right_type(p)>explicit then
//!   begin right_type(p):=explicit;
//!   if left_type(p)=open then
//!     begin left_type(p):=curl; left_curl(p):=unity;
//!     end;
//!   left_type(q):=explicit;
//!   if right_type(q)=open then
//!     begin right_type(q):=curl; right_curl(q):=unity;
//!     end;
//!   right_x(p):=x_coord(p); left_x(q):=x_coord(p);@/
//!   right_y(p):=y_coord(p); left_y(q):=y_coord(p);
//!   end;
//! p:=q;
//! until p=knots
//!
//! @ If there are no breakpoints, it is necessary to compute the direction
//! angles around an entire cycle. In this case the |left_type| of the first
//! node is temporarily changed to |end_cycle|.
//!
//! @d end_cycle=open+1
//!
//! @<Find the first breakpoint, |h|, on the path...@>=
//! h:=knots;
//! loop@+  begin if left_type(h)<>open then goto done;
//!   if right_type(h)<>open then goto done;
//!   h:=link(h);
//!   if h=knots then
//!     begin left_type(h):=end_cycle; goto done;
//!     end;
//!   end;
//! done:
//!
//! @ If |right_type(p)<given| and |q=link(p)|, we must have
//! |right_type(p)=left_type(q)=explicit| or |endpoint|.
//!
//! @<Fill in the control points between |p| and the next breakpoint...@>=
//! q:=link(p);
//! if right_type(p)>=given then
//!   begin while (left_type(q)=open)and(right_type(q)=open) do q:=link(q);
//!   @<Fill in the control information between
//!     consecutive breakpoints |p| and |q|@>;
//!   end;
//! p:=q
//!
//! @ Before we can go further into the way choices are made, we need to
//! consider the underlying theory. The basic ideas implemented in |make_choices|
//! are due to John Hobby, who introduced the notion of ``mock curvature''
//! @^Hobby, John Douglas@>
//! at a knot. Angles are chosen so that they preserve mock curvature when
//! a knot is passed, and this has been found to produce excellent results.
//!
//! It is convenient to introduce some notations that simplify the necessary
//! formulas. Let $d_{k,k+1}=\vert z\k-z_k\vert$ be the (nonzero) distance
//! between knots |k| and |k+1|; and let
//! $${z\k-z_k\over z_k-z_{k-1}}={d_{k,k+1}\over d_{k-1,k}}e^{i\psi_k}$$
//! so that a polygonal line from $z_{k-1}$ to $z_k$ to $z\k$ turns left
//! through an angle of~$\psi_k$. We assume that $\vert\psi_k\vert\L180^\circ$.
//! The control points for the spline from $z_k$ to $z\k$ will be denoted by
//! $$\eqalign{z_k^+&=z_k+
//!   \textstyle{1\over3}\rho_k e^{i\theta_k}(z\k-z_k),\cr
//!  z\k^-&=z\k-
//!   \textstyle{1\over3}\sigma\k e^{-i\phi\k}(z\k-z_k),\cr}$$
//! where $\rho_k$ and $\sigma\k$ are nonnegative ``velocity ratios'' at the
//! beginning and end of the curve, while $\theta_k$ and $\phi\k$ are the
//! corresponding ``offset angles.'' These angles satisfy the condition
//! $$\theta_k+\phi_k+\psi_k=0,\eqno(*)$$
//! whenever the curve leaves an intermediate knot~|k| in the direction that
//! it enters.
//!
//! @ Let $\alpha_k$ and $\beta\k$ be the reciprocals of the ``tension'' of
//! the curve at its beginning and ending points. This means that
//! $\rho_k=\alpha_k f(\theta_k,\phi\k)$ and $\sigma\k=\beta\k f(\phi\k,\theta_k)$,
//! where $f(\theta,\phi)$ is \MF's standard velocity function defined in
//! the |velocity| subroutine. The cubic spline $B(z_k^{\phantom+},z_k^+,
//! z\k^-,z\k^{\phantom+};t)$
//! has curvature
//! @^curvature@>
//! $${2\sigma\k\sin(\theta_k+\phi\k)-6\sin\theta_k\over\rho_k^2d_{k,k+1}}
//! \qquad{\rm and}\qquad
//! {2\rho_k\sin(\theta_k+\phi\k)-6\sin\phi\k\over\sigma\k^2d_{k,k+1}}$$
//! at |t=0| and |t=1|, respectively. The mock curvature is the linear
//! @^mock curvature@>
//! approximation to this true curvature that arises in the limit for
//! small $\theta_k$ and~$\phi\k$, if second-order terms are discarded.
//! The standard velocity function satisfies
//! $$f(\theta,\phi)=1+O(\theta^2+\theta\phi+\phi^2);$$
//! hence the mock curvatures are respectively
//! $${2\beta\k(\theta_k+\phi\k)-6\theta_k\over\alpha_k^2d_{k,k+1}}
//! \qquad{\rm and}\qquad
//! {2\alpha_k(\theta_k+\phi\k)-6\phi\k\over\beta\k^2d_{k,k+1}}.\eqno(**)$$
//!
//! @ The turning angles $\psi_k$ are given, and equation $(*)$ above
//! determines $\phi_k$ when $\theta_k$ is known, so the task of
//! angle selection is essentially to choose appropriate values for each
//! $\theta_k$. When equation~$(*)$ is used to eliminate $\phi$~variables
//! from $(**)$, we obtain a system of linear equations of the form
//! $$A_k\theta_{k-1}+(B_k+C_k)\theta_k+D_k\theta\k=-B_k\psi_k-D_k\psi\k,$$
//! where
//! $$A_k={\alpha_{k-1}\over\beta_k^2d_{k-1,k}},
//! \qquad B_k={3-\alpha_{k-1}\over\beta_k^2d_{k-1,k}},
//! \qquad C_k={3-\beta\k\over\alpha_k^2d_{k,k+1}},
//! \qquad D_k={\beta\k\over\alpha_k^2d_{k,k+1}}.$$
//! The tensions are always $3\over4$ or more, hence each $\alpha$ and~$\beta$
//! will be at most $4\over3$. It follows that $B_k\G{5\over4}A_k$ and
//! $C_k\G{5\over4}D_k$; hence the equations are diagonally dominant;
//! hence they have a unique solution. Moreover, in most cases the tensions
//! are equal to~1, so that $B_k=2A_k$ and $C_k=2D_k$. This makes the
//! solution numerically stable, and there is an exponential damping
//! effect: The data at knot $k\pm j$ affects the angle at knot~$k$ by
//! a factor of~$O(2^{-j})$.
//!
//! @ However, we still must consider the angles at the starting and ending
//! knots of a non-cyclic path. These angles might be given explicitly, or
//! they might be specified implicitly in terms of an amount of ``curl.''
//!
//! Let's assume that angles need to be determined for a non-cyclic path
//! starting at $z_0$ and ending at~$z_n$. Then equations of the form
//! $$A_k\theta_{k-1}+(B_k+C_k)\theta_k+D_k\theta_{k+1}=R_k$$
//! have been given for $0<k<n$, and it will be convenient to introduce
//! equations of the same form for $k=0$ and $k=n$, where
//! $$A_0=B_0=C_n=D_n=0.$$
//! If $\theta_0$ is supposed to have a given value $E_0$, we simply
//! define $C_0=1$, $D_0=0$, and $R_0=E_0$. Otherwise a curl
//! parameter, $\gamma_0$, has been specified at~$z_0$; this means
//! that the mock curvature at $z_0$ should be $\gamma_0$ times the
//! mock curvature at $z_1$; i.e.,
//! $${2\beta_1(\theta_0+\phi_1)-6\theta_0\over\alpha_0^2d_{01}}
//! =\gamma_0{2\alpha_0(\theta_0+\phi_1)-6\phi_1\over\beta_1^2d_{01}}.$$
//! This equation simplifies to
//! $$(\alpha_0\chi_0+3-\beta_1)\theta_0+
//!  \bigl((3-\alpha_0)\chi_0+\beta_1\bigr)\theta_1=
//!  -\bigl((3-\alpha_0)\chi_0+\beta_1\bigr)\psi_1,$$
//! where $\chi_0=\alpha_0^2\gamma_0/\beta_1^2$; so we can set $C_0=
//! \chi_0\alpha_0+3-\beta_1$, $D_0=(3-\alpha_0)\chi_0+\beta_1$, $R_0=-D_0\psi_1$.
//! It can be shown that $C_0>0$ and $C_0B_1-A_1D_0>0$ when $\gamma_0\G0$,
//! hence the linear equations remain nonsingular.
//!
//! Similar considerations apply at the right end, when the final angle $\phi_n$
//! may or may not need to be determined. It is convenient to let $\psi_n=0$,
//! hence $\theta_n=-\phi_n$. We either have an explicit equation $\theta_n=E_n$,
//! or we have
//! $$\bigl((3-\beta_n)\chi_n+\alpha_{n-1}\bigr)\theta_{n-1}+
//! (\beta_n\chi_n+3-\alpha_{n-1})\theta_n=0,\qquad
//!   \chi_n={\beta_n^2\gamma_n\over\alpha_{n-1}^2}.$$
//!
//! When |make_choices| chooses angles, it must compute the coefficients of
//! these linear equations, then solve the equations. To compute the coefficients,
//! it is necessary to compute arctangents of the given turning angles~$\psi_k$.
//! When the equations are solved, the chosen directions $\theta_k$ are put
//! back into the form of control points by essentially computing sines and
//! cosines.
//!
//! @ OK, we are ready to make the hard choices of |make_choices|.
//! Most of the work is relegated to an auxiliary procedure
//! called |solve_choices|, which has been introduced to keep
//! |make_choices| from being extremely long.
//!
//! @<Fill in the control information between...@>=
//! @<Calculate the turning angles $\psi_k$ and the distances $d_{k,k+1}$;
//!   set $n$ to the length of the path@>;
//! @<Remove |open| types at the breakpoints@>;
//! solve_choices(p,q,n)
//!
//! @ It's convenient to precompute quantities that will be needed several
//! times later. The values of |delta_x[k]| and |delta_y[k]| will be the
//! coordinates of $z\k-z_k$, and the magnitude of this vector will be
//! |delta[k]=@t$d_{k,k+1}$@>|. The path angle $\psi_k$ between $z_k-z_{k-1}$
//! and $z\k-z_k$ will be stored in |psi[k]|.
//!
//! @<Glob...@>=
//! @!delta_x,@!delta_y,@!delta:array[0..path_size] of scaled; {knot differences}
//! @!psi:array[1..path_size] of angle; {turning angles}
//!
//! @ @<Other local variables for |make_choices|@>=
//! @!k,@!n:0..path_size; {current and final knot numbers}
//! @!s,@!t:pointer; {registers for list traversal}
//! @!delx,@!dely:scaled; {directions where |open| meets |explicit|}
//! @!sine,@!cosine:fraction; {trig functions of various angles}
//!
//! @ @<Calculate the turning angles...@>=
//! k:=0; s:=p; n:=path_size;
//! repeat t:=link(s);
//! delta_x[k]:=x_coord(t)-x_coord(s);
//! delta_y[k]:=y_coord(t)-y_coord(s);
//! delta[k]:=pyth_add(delta_x[k],delta_y[k]);
//! if k>0 then
//!   begin sine:=make_fraction(delta_y[k-1],delta[k-1]);
//!   cosine:=make_fraction(delta_x[k-1],delta[k-1]);
//!   psi[k]:=n_arg(take_fraction(delta_x[k],cosine)+
//!       take_fraction(delta_y[k],sine),
//!     take_fraction(delta_y[k],cosine)-
//!       take_fraction(delta_x[k],sine));
//!   end;
//! @:METAFONT capacity exceeded path size}{\quad path size@>
//! incr(k); s:=t;
//! if k=path_size then overflow("path size",path_size);
//! if s=q then n:=k;
//! until (k>=n)and(left_type(s)<>end_cycle);
//! if k=n then psi[n]:=0@+else psi[k]:=psi[1]
//!
//! @ When we get to this point of the code, |right_type(p)| is either
//! |given| or |curl| or |open|. If it is |open|, we must have
//! |left_type(p)=end_cycle| or |left_type(p)=explicit|. In the latter
//! case, the |open| type is converted to |given|; however, if the
//! velocity coming into this knot is zero, the |open| type is
//! converted to a |curl|, since we don't know the incoming direction.
//!
//! Similarly, |left_type(q)| is either |given| or |curl| or |open| or
//! |end_cycle|. The |open| possibility is reduced either to |given| or to |curl|.
//!
//! @<Remove |open| types at the breakpoints@>=
//! if left_type(q)=open then
//!   begin delx:=right_x(q)-x_coord(q); dely:=right_y(q)-y_coord(q);
//!   if (delx=0)and(dely=0) then
//!     begin left_type(q):=curl; left_curl(q):=unity;
//!     end
//!   else  begin left_type(q):=given; left_given(q):=n_arg(delx,dely);
//!     end;
//!   end;
//! if (right_type(p)=open)and(left_type(p)=explicit) then
//!   begin delx:=x_coord(p)-left_x(p); dely:=y_coord(p)-left_y(p);
//!   if (delx=0)and(dely=0) then
//!     begin right_type(p):=curl; right_curl(p):=unity;
//!     end
//!   else  begin right_type(p):=given; right_given(p):=n_arg(delx,dely);
//!     end;
//!   end
//!
//! @ Linear equations need to be solved whenever |n>1|; and also when |n=1|
//! and exactly one of the breakpoints involves a curl. The simplest case occurs
//! when |n=1| and there is a curl at both breakpoints; then we simply draw
//! a straight line.
//!
//! But before coding up the simple cases, we might as well face the general case,
//! since we must deal with it sooner or later, and since the general case
//! is likely to give some insight into the way simple cases can be handled best.
//!
//! When there is no cycle, the linear equations to be solved form a tri-diagonal
//! system, and we can apply the standard technique of Gaussian elimination
//! to convert that system to a sequence of equations of the form
//! $$\theta_0+u_0\theta_1=v_0,\quad
//! \theta_1+u_1\theta_2=v_1,\quad\ldots,\quad
//! \theta_{n-1}+u_{n-1}\theta_n=v_{n-1},\quad
//! \theta_n=v_n.$$
//! It is possible to do this diagonalization while generating the equations.
//! Once $\theta_n$ is known, it is easy to determine $\theta_{n-1}$, \dots,
//! $\theta_1$, $\theta_0$; thus, the equations will be solved.
//!
//! The procedure is slightly more complex when there is a cycle, but the
//! basic idea will be nearly the same. In the cyclic case the right-hand
//! sides will be $v_k+w_k\theta_0$ instead of simply $v_k$, and we will start
//! the process off with $u_0=v_0=0$, $w_0=1$. The final equation will be not
//! $\theta_n=v_n$ but $\theta_n+u_n\theta_1=v_n+w_n\theta_0$; an appropriate
//! ending routine will take account of the fact that $\theta_n=\theta_0$ and
//! eliminate the $w$'s from the system, after which the solution can be
//! obtained as before.
//!
//! When $u_k$, $v_k$, and $w_k$ are being computed, the three pointer
//! variables |r|, |s|,~|t| will point respectively to knots |k-1|, |k|,
//! and~|k+1|. The $u$'s and $w$'s are scaled by $2^{28}$, i.e., they are
//! of type |fraction|; the $\theta$'s and $v$'s are of type |angle|.
//!
//! @<Glob...@>=
//! @!theta:array[0..path_size] of angle; {values of $\theta_k$}
//! @!uu:array[0..path_size] of fraction; {values of $u_k$}
//! @!vv:array[0..path_size] of angle; {values of $v_k$}
//! @!ww:array[0..path_size] of fraction; {values of $w_k$}
//!
//! @ Our immediate problem is to get the ball rolling by setting up the
//! first equation or by realizing that no equations are needed, and to fit
//! this initialization into a framework suitable for the overall computation.
//!
//! @<Declare the procedure called |solve_choices|@>=
//! @t\4@>@<Declare subroutines needed by |solve_choices|@>@;
//! procedure solve_choices(@!p,@!q:pointer;@!n:halfword);
//! label found,exit;
//! var @!k:0..path_size; {current knot number}
//! @!r,@!s,@!t:pointer; {registers for list traversal}
//! @<Other local variables for |solve_choices|@>@;
//! begin k:=0; s:=p;
//! loop@+  begin t:=link(s);
//!   if k=0 then @<Get the linear equations started; or |return|
//!     with the control points in place, if linear equations
//!     needn't be solved@>
//!   else  case left_type(s) of
//!     end_cycle,open:@<Set up equation to match mock curvatures
//!       at $z_k$; then |goto found| with $\theta_n$
//!       adjusted to equal $\theta_0$, if a cycle has ended@>;
//!     curl:@<Set up equation for a curl at $\theta_n$
//!       and |goto found|@>;
//!     given:@<Calculate the given value of $\theta_n$
//!       and |goto found|@>;
//!     end; {there are no other cases}
//!   r:=s; s:=t; incr(k);
//!   end;
//! found:@<Finish choosing angles and assigning control points@>;
//! exit:end;
//!
//! @ On the first time through the loop, we have |k=0| and |r| is not yet
//! defined. The first linear equation, if any, will have $A_0=B_0=0$.
//!
//! @<Get the linear equations started...@>=
//! case right_type(s) of
//! given: if left_type(t)=given then @<Reduce to simple case of two givens
//!     and |return|@>
//!   else @<Set up the equation for a given value of $\theta_0$@>;
//! curl: if left_type(t)=curl then @<Reduce to simple case of straight line
//!     and |return|@>
//!   else @<Set up the equation for a curl at $\theta_0$@>;
//! open: begin uu[0]:=0; vv[0]:=0; ww[0]:=fraction_one;
//!   end; {this begins a cycle}
//! end {there are no other cases}
//!
//! @ The general equation that specifies equality of mock curvature at $z_k$ is
//! $$A_k\theta_{k-1}+(B_k+C_k)\theta_k+D_k\theta\k=-B_k\psi_k-D_k\psi\k,$$
//! as derived above. We want to combine this with the already-derived equation
//! $\theta_{k-1}+u_{k-1}\theta_k=v_{k-1}+w_{k-1}\theta_0$ in order to obtain
//! a new equation
//! $\theta_k+u_k\theta\k=v_k+w_k\theta_0$. This can be done by dividing the
//! equation
//! $$(B_k-u_{k-1}A_k+C_k)\theta_k+D_k\theta\k=-B_k\psi_k-D_k\psi\k-A_kv_{k-1}
//!     -A_kw_{k-1}\theta_0$$
//! by $B_k-u_{k-1}A_k+C_k$. The trick is to do this carefully with
//! fixed-point arithmetic, avoiding the chance of overflow while retaining
//! suitable precision.
//!
//! The calculations will be performed in several registers that
//! provide temporary storage for intermediate quantities.
//!
//! @<Other local variables for |solve_choices|@>=
//! @!aa,@!bb,@!cc,@!ff,@!acc:fraction; {temporary registers}
//! @!dd,@!ee:scaled; {likewise, but |scaled|}
//! @!lt,@!rt:scaled; {tension values}
//!
//! @ @<Set up equation to match mock curvatures...@>=
//! begin @<Calculate the values $\\{aa}=A_k/B_k$, $\\{bb}=D_k/C_k$,
//!   $\\{dd}=(3-\alpha_{k-1})d_{k,k+1}$, $\\{ee}=(3-\beta\k)d_{k-1,k}$,
//!   and $\\{cc}=(B_k-u_{k-1}A_k)/B_k$@>;
//! @<Calculate the ratio $\\{ff}=C_k/(C_k+B_k-u_{k-1}A_k)$@>;
//! uu[k]:=take_fraction(ff,bb);
//! @<Calculate the values of $v_k$ and $w_k$@>;
//! if left_type(s)=end_cycle then
//!   @<Adjust $\theta_n$ to equal $\theta_0$ and |goto found|@>;
//! end
//!
//! @ Since tension values are never less than 3/4, the values |aa| and
//! |bb| computed here are never more than 4/5.
//!
//! @<Calculate the values $\\{aa}=...@>=
//! if abs(right_tension(r))=unity then
//!   begin aa:=fraction_half; dd:=2*delta[k];
//!   end
//! else  begin aa:=make_fraction(unity,3*abs(right_tension(r))-unity);
//!   dd:=take_fraction(delta[k],
//!     fraction_three-make_fraction(unity,abs(right_tension(r))));
//!   end;
//! if abs(left_tension(t))=unity then
//!   begin bb:=fraction_half; ee:=2*delta[k-1];
//!   end
//! else  begin bb:=make_fraction(unity,3*abs(left_tension(t))-unity);
//!   ee:=take_fraction(delta[k-1],
//!     fraction_three-make_fraction(unity,abs(left_tension(t))));
//!   end;
//! cc:=fraction_one-take_fraction(uu[k-1],aa)
//!
//! @ The ratio to be calculated in this step can be written in the form
//! $$\beta_k^2\cdot\\{ee}\over\beta_k^2\cdot\\{ee}+\alpha_k^2\cdot
//!   \\{cc}\cdot\\{dd},$$
//! because of the quantities just calculated. The values of |dd| and |ee|
//! will not be needed after this step has been performed.
//!
//! @<Calculate the ratio $\\{ff}=C_k/(C_k+B_k-u_{k-1}A_k)$@>=
//! dd:=take_fraction(dd,cc); lt:=abs(left_tension(s)); rt:=abs(right_tension(s));
//! if lt<>rt then {$\beta_k^{-1}\ne\alpha_k^{-1}$}
//!   if lt<rt then
//!     begin ff:=make_fraction(lt,rt);
//!     ff:=take_fraction(ff,ff); {$\alpha_k^2/\beta_k^2$}
//!     dd:=take_fraction(dd,ff);
//!     end
//!   else  begin ff:=make_fraction(rt,lt);
//!     ff:=take_fraction(ff,ff); {$\beta_k^2/\alpha_k^2$}
//!     ee:=take_fraction(ee,ff);
//!     end;
//! ff:=make_fraction(ee,ee+dd)
//!
//! @ The value of $u_{k-1}$ will be |<=1| except when $k=1$ and the previous
//! equation was specified by a curl. In that case we must use a special
//! method of computation to prevent overflow.
//!
//! Fortunately, the calculations turn out to be even simpler in this ``hard''
//! case. The curl equation makes $w_0=0$ and $v_0=-u_0\psi_1$, hence
//! $-B_1\psi_1-A_1v_0=-(B_1-u_0A_1)\psi_1=-\\{cc}\cdot B_1\psi_1$.
//!
//! @<Calculate the values of $v_k$ and $w_k$@>=
//! acc:=-take_fraction(psi[k+1],uu[k]);
//! if right_type(r)=curl then
//!   begin ww[k]:=0;
//!   vv[k]:=acc-take_fraction(psi[1],fraction_one-ff);
//!   end
//! else  begin ff:=make_fraction(fraction_one-ff,cc); {this is
//!     $B_k/(C_k+B_k-u_{k-1}A_k)<5$}
//!   acc:=acc-take_fraction(psi[k],ff);
//!   ff:=take_fraction(ff,aa); {this is $A_k/(C_k+B_k-u_{k-1}A_k)$}
//!   vv[k]:=acc-take_fraction(vv[k-1],ff);
//!   if ww[k-1]=0 then ww[k]:=0
//!   else ww[k]:=-take_fraction(ww[k-1],ff);
//!   end
//!
//! @ When a complete cycle has been traversed, we have $\theta_k+u_k\theta\k=
//! v_k+w_k\theta_0$, for |1<=k<=n|. We would like to determine the value of
//! $\theta_n$ and reduce the system to the form $\theta_k+u_k\theta\k=v_k$
//! for |0<=k<n|, so that the cyclic case can be finished up just as if there
//! were no cycle.
//!
//! The idea in the following code is to observe that
//! $$\eqalign{\theta_n&=v_n+w_n\theta_0-u_n\theta_1=\cdots\cr
//! &=v_n+w_n\theta_0-u_n\bigl(v_1+w_1\theta_0-u_1(v_2+\cdots
//!   -u_{n-2}(v_{n-1}+w_{n-1}\theta_0-u_{n-1}\theta_0)\ldots{})\bigr),\cr}$$
//! so we can solve for $\theta_n=\theta_0$.
//!
//! @<Adjust $\theta_n$ to equal $\theta_0$ and |goto found|@>=
//! begin aa:=0; bb:=fraction_one; {we have |k=n|}
//! repeat decr(k);
//! if k=0 then k:=n;
//! aa:=vv[k]-take_fraction(aa,uu[k]);
//! bb:=ww[k]-take_fraction(bb,uu[k]);
//! until k=n; {now $\theta_n=\\{aa}+\\{bb}\cdot\theta_n$}
//! aa:=make_fraction(aa,fraction_one-bb);
//! theta[n]:=aa; vv[0]:=aa;
//! for k:=1 to n-1 do vv[k]:=vv[k]+take_fraction(aa,ww[k]);
//! goto found;
//! end
//!
//! @ @d reduce_angle(#)==if abs(#)>one_eighty_deg then
//!   if #>0 then #:=#-three_sixty_deg@+else #:=#+three_sixty_deg
//!
//! @<Calculate the given value of $\theta_n$...@>=
//! begin theta[n]:=left_given(s)-n_arg(delta_x[n-1],delta_y[n-1]);
//! reduce_angle(theta[n]);
//! goto found;
//! end
//!
//! @ @<Set up the equation for a given value of $\theta_0$@>=
//! begin vv[0]:=right_given(s)-n_arg(delta_x[0],delta_y[0]);
//! reduce_angle(vv[0]);
//! uu[0]:=0; ww[0]:=0;
//! end
//!
//! @ @<Set up the equation for a curl at $\theta_0$@>=
//! begin cc:=right_curl(s); lt:=abs(left_tension(t)); rt:=abs(right_tension(s));
//! if (rt=unity)and(lt=unity) then
//!   uu[0]:=make_fraction(cc+cc+unity,cc+two)
//! else uu[0]:=curl_ratio(cc,rt,lt);
//! vv[0]:=-take_fraction(psi[1],uu[0]); ww[0]:=0;
//! end
//!
//! @ @<Set up equation for a curl at $\theta_n$...@>=
//! begin cc:=left_curl(s); lt:=abs(left_tension(s)); rt:=abs(right_tension(r));
//! if (rt=unity)and(lt=unity) then
//!   ff:=make_fraction(cc+cc+unity,cc+two)
//! else ff:=curl_ratio(cc,lt,rt);
//! theta[n]:=-make_fraction(take_fraction(vv[n-1],ff),
//!     fraction_one-take_fraction(ff,uu[n-1]));
//! goto found;
//! end
//!
//! @ The |curl_ratio| subroutine has three arguments, which our previous notation
//! encourages us to call $\gamma$, $\alpha^{-1}$, and $\beta^{-1}$. It is
//! a somewhat tedious program to calculate
//! $${(3-\alpha)\alpha^2\gamma+\beta^3\over
//!   \alpha^3\gamma+(3-\beta)\beta^2},$$
//! with the result reduced to 4 if it exceeds 4. (This reduction of curl
//! is necessary only if the curl and tension are both large.)
//! The values of $\alpha$ and $\beta$ will be at most~4/3.
//!
//! @<Declare subroutines needed by |solve_choices|@>=
//! function curl_ratio(@!gamma,@!a_tension,@!b_tension:scaled):fraction;
//! var @!alpha,@!beta,@!num,@!denom,@!ff:fraction; {registers}
//! begin alpha:=make_fraction(unity,a_tension);
//! beta:=make_fraction(unity,b_tension);@/
//! if alpha<=beta then
//!   begin ff:=make_fraction(alpha,beta); ff:=take_fraction(ff,ff);
//!   gamma:=take_fraction(gamma,ff);@/
//!   beta:=beta div @'10000; {convert |fraction| to |scaled|}
//!   denom:=take_fraction(gamma,alpha)+three-beta;
//!   num:=take_fraction(gamma,fraction_three-alpha)+beta;
//!   end
//! else  begin ff:=make_fraction(beta,alpha); ff:=take_fraction(ff,ff);
//!   beta:=take_fraction(beta,ff) div @'10000; {convert |fraction| to |scaled|}
//!   denom:=take_fraction(gamma,alpha)+(ff div 1365)-beta;
//!     {$1365\approx 2^{12}/3$}
//!   num:=take_fraction(gamma,fraction_three-alpha)+beta;
//!   end;
//! if num>=denom+denom+denom+denom then curl_ratio:=fraction_four
//! else curl_ratio:=make_fraction(num,denom);
//! end;
//!
//! @ We're in the home stretch now.
//!
//! @<Finish choosing angles and assigning control points@>=
//! for k:=n-1 downto 0 do theta[k]:=vv[k]-take_fraction(theta[k+1],uu[k]);
//! s:=p; k:=0;
//! repeat t:=link(s);@/
//! n_sin_cos(theta[k]); st:=n_sin; ct:=n_cos;@/
//! n_sin_cos(-psi[k+1]-theta[k+1]); sf:=n_sin; cf:=n_cos;@/
//! set_controls(s,t,k);@/
//! incr(k); s:=t;
//! until k=n
//!
//! @ The |set_controls| routine actually puts the control points into
//! a pair of consecutive nodes |p| and~|q|. Global variables are used to
//! record the values of $\sin\theta$, $\cos\theta$, $\sin\phi$, and
//! $\cos\phi$ needed in this calculation.
//!
//! @<Glob...@>=
//! @!st,@!ct,@!sf,@!cf:fraction; {sines and cosines}
//!
//! @ @<Declare subroutines needed by |solve_choices|@>=
//! procedure set_controls(@!p,@!q:pointer;@!k:integer);
//! var @!rr,@!ss:fraction; {velocities, divided by thrice the tension}
//! @!lt,@!rt:scaled; {tensions}
//! @!sine:fraction; {$\sin(\theta+\phi)$}
//! begin lt:=abs(left_tension(q)); rt:=abs(right_tension(p));
//! rr:=velocity(st,ct,sf,cf,rt);
//! ss:=velocity(sf,cf,st,ct,lt);
//! if (right_tension(p)<0)or(left_tension(q)<0) then @<Decrease the velocities,
//!   if necessary, to stay inside the bounding triangle@>;
//! right_x(p):=x_coord(p)+take_fraction(
//!   take_fraction(delta_x[k],ct)-take_fraction(delta_y[k],st),rr);
//! right_y(p):=y_coord(p)+take_fraction(
//!   take_fraction(delta_y[k],ct)+take_fraction(delta_x[k],st),rr);
//! left_x(q):=x_coord(q)-take_fraction(
//!   take_fraction(delta_x[k],cf)+take_fraction(delta_y[k],sf),ss);
//! left_y(q):=y_coord(q)-take_fraction(
//!   take_fraction(delta_y[k],cf)-take_fraction(delta_x[k],sf),ss);
//! right_type(p):=explicit; left_type(q):=explicit;
//! end;
//!
//! @ The boundedness conditions $\\{rr}\L\sin\phi\,/\sin(\theta+\phi)$ and
//! $\\{ss}\L\sin\theta\,/\sin(\theta+\phi)$ are to be enforced if $\sin\theta$,
//! $\sin\phi$, and $\sin(\theta+\phi)$ all have the same sign. Otherwise
//! there is no ``bounding triangle.''
//!
//! @<Decrease the velocities, if necessary...@>=
//! if((st>=0)and(sf>=0))or((st<=0)and(sf<=0)) then
//!   begin sine:=take_fraction(abs(st),cf)+take_fraction(abs(sf),ct);
//!   if sine>0 then
//!     begin sine:=take_fraction(sine,fraction_one+unity); {safety factor}
//!     if right_tension(p)<0 then
//!      if ab_vs_cd(abs(sf),fraction_one,rr,sine)<0 then
//!       rr:=make_fraction(abs(sf),sine);
//!     if left_tension(q)<0 then
//!      if ab_vs_cd(abs(st),fraction_one,ss,sine)<0 then
//!       ss:=make_fraction(abs(st),sine);
//!     end;
//!   end
//!
//! @ Only the simple cases remain to be handled.
//!
//! @<Reduce to simple case of two givens and |return|@>=
//! begin aa:=n_arg(delta_x[0],delta_y[0]);@/
//! n_sin_cos(right_given(p)-aa); ct:=n_cos; st:=n_sin;@/
//! n_sin_cos(left_given(q)-aa); cf:=n_cos; sf:=-n_sin;@/
//! set_controls(p,q,0); return;
//! end
//!
//! @ @<Reduce to simple case of straight line and |return|@>=
//! begin right_type(p):=explicit; left_type(q):=explicit;
//! lt:=abs(left_tension(q)); rt:=abs(right_tension(p));
//! if rt=unity then
//!   begin if delta_x[0]>=0 then right_x(p):=x_coord(p)+((delta_x[0]+1) div 3)
//!   else right_x(p):=x_coord(p)+((delta_x[0]-1) div 3);
//!   if delta_y[0]>=0 then right_y(p):=y_coord(p)+((delta_y[0]+1) div 3)
//!   else right_y(p):=y_coord(p)+((delta_y[0]-1) div 3);
//!   end
//! else  begin ff:=make_fraction(unity,3*rt); {$\alpha/3$}
//!   right_x(p):=x_coord(p)+take_fraction(delta_x[0],ff);
//!   right_y(p):=y_coord(p)+take_fraction(delta_y[0],ff);
//!   end;
//! if lt=unity then
//!   begin if delta_x[0]>=0 then left_x(q):=x_coord(q)-((delta_x[0]+1) div 3)
//!   else left_x(q):=x_coord(q)-((delta_x[0]-1) div 3);
//!   if delta_y[0]>=0 then left_y(q):=y_coord(q)-((delta_y[0]+1) div 3)
//!   else left_y(q):=y_coord(q)-((delta_y[0]-1) div 3);
//!   end
//! else  begin ff:=make_fraction(unity,3*lt); {$\beta/3$}
//!   left_x(q):=x_coord(q)-take_fraction(delta_x[0],ff);
//!   left_y(q):=y_coord(q)-take_fraction(delta_y[0],ff);
//!   end;
//! return;
//! end
//!
//! @* \[19] Generating discrete moves.
//! The purpose of the next part of \MF\ is to compute discrete approximations
//! to curves described as parametric polynomial functions $z(t)$.
//! We shall start with the low level first, because an efficient ``engine''
//! is needed to support the high-level constructions.
//!
//! Most of the subroutines are based on variations of a single theme,
//! namely the idea of {\sl bisection}. Given a Bernshte{\u\i}n polynomial
//! @^Bernshte{\u\i}n, Serge{\u\i} Natanovich@>
//! $$B(z_0,z_1,\ldots,z_n;t)=\sum_k{n\choose k}t^k(1-t)^{n-k}z_k,$$
//! we can conveniently bisect its range as follows:
//!
//! \smallskip
//! \textindent{1)} Let $z_k^{(0)}=z_k$, for |0<=k<=n|.
//!
//! \smallskip
//! \textindent{2)} Let $z_k^{(j+1)}={1\over2}(z_k^{(j)}+z\k^{(j)})$, for
//! |0<=k<n-j|, for |0<=j<n|.
//!
//! \smallskip\noindent
//! Then
//! $$B(z_0,z_1,\ldots,z_n;t)=B(z_0^{(0)},z_0^{(1)},\ldots,z_0^{(n)};2t)
//!  =B(z_0^{(n)},z_1^{(n-1)},\ldots,z_n^{(0)};2t-1).$$
//! This formula gives us the coefficients of polynomials to use over the ranges
//! $0\L t\L{1\over2}$ and ${1\over2}\L t\L1$.
//!
//! In our applications it will usually be possible to work indirectly with
//! numbers that allow us to deduce relevant properties of the polynomials
//! without actually computing the polynomial values. We will deal with
//! coefficients $Z_k=2^l(z_k-z_{k-1})$ for |1<=k<=n|, instead of
//! the actual numbers $z_0$, $z_1$, \dots,~$z_n$, and the value of~|l| will
//! increase by~1 at each bisection step. This technique reduces the
//! amount of calculation needed for bisection and also increases the
//! accuracy of evaluation (since one bit of precision is gained at each
//! bisection). Indeed, the bisection process now becomes one level shorter:
//!
//! \smallskip
//! \textindent{$1'$)} Let $Z_k^{(1)}=Z_k$, for |1<=k<=n|.
//!
//! \smallskip
//! \textindent{$2'$)} Let $Z_k^{(j+1)}={1\over2}(Z_k^{(j)}+Z\k^{(j)})$, for
//! |1<=k<=n-j|, for |1<=j<n|.
//!
//! \smallskip\noindent
//! The relevant coefficients $(Z'_1,\ldots,Z'_n)$ and $(Z''_1,\ldots,Z''_n)$
//! for the two subintervals after bisection are respectively
//! $(Z_1^{(1)},Z_1^{(2)},\ldots,Z_1^{(n)})$ and
//! $(Z_1^{(n)},Z_2^{(n-1)},\ldots,Z_n^{(1)})$.
//! And the values of $z_0$ appropriate for the bisected interval are $z'_0=z_0$
//! and $z''_0=z_0+(Z'_1+Z'_2+\cdots+Z'_n)/2^{l+1}$.
//!
//! Step $2'$ involves division by~2, which introduces computational errors
//! of at most $1\over2$ at each step; thus after $l$~levels of bisection the
//! integers $Z_k$ will differ from their true values by at most $(n-1)l/2$.
//! This error rate is quite acceptable, considering that we have $l$~more
//! bits of precision in the $Z$'s by comparison with the~$z$'s.  Note also
//! that the $Z$'s remain bounded; there's no danger of integer overflow, even
//! though we have the identity $Z_k=2^l(z_k-z_{k-1})$ for arbitrarily large~$l$.
//!
//! In fact, we can show not only that the $Z$'s remain bounded, but also that
//! they become nearly equal, since they are control points for a polynomial
//! of one less degree. If $\vert Z\k-Z_k\vert\L M$ initially, it is possible
//! to prove that $\vert Z\k-Z_k\vert\L\lceil M/2^l\rceil$ after $l$~levels
//! of bisection, even in the presence of rounding errors. Here's the
//! proof [cf.~Lane and Riesenfeld, {\sl IEEE Trans.\ on Pattern Analysis
//! @^Lane, Jeffrey Michael@>
//! @^Riesenfeld, Richard Franklin@>
//! and Machine Intelligence\/ \bf PAMI-2} (1980), 35--46]: Assuming that
//! $\vert Z\k-Z_k\vert\L M$ before bisection, we want to prove that
//! $\vert Z\k-Z_k\vert\L\lceil M/2\rceil$ afterward. First we show that
//! $\vert Z\k^{(j)}-Z_k^{(j)}\vert\L M$ for all $j$ and~$k$, by induction
//! on~$j$; this follows from the fact that
//! $$\bigl\vert\\{half}(a+b)-\\{half}(b+c)\bigr\vert\L
//!  \max\bigl(\vert a-b\vert,\vert b-c\vert\bigr)$$
//! holds for both of the rounding rules $\\{half}(x)=\lfloor x/2\rfloor$
//! and $\\{half}(x)={\rm sign}(x)\lfloor\vert x/2\vert\rfloor$.
//! (If $\vert a-b\vert$ and $\vert b-c\vert$ are equal, then
//! $a+b$ and $b+c$ are both even or both odd. The rounding errors either
//! cancel or round the numbers toward each other; hence
//! $$\eqalign{\bigl\vert\\{half}(a+b)-\\{half}(b+c)\bigr\vert
//! &\L\textstyle\bigl\vert{1\over2}(a+b)-{1\over2}(b+c)\bigr\vert\cr
//! &=\textstyle\bigl\vert{1\over2}(a-b)+{1\over2}(b-c)\bigr\vert
//! \L\max\bigl(\vert a-b\vert,\vert b-c\vert\bigr),\cr}$$
//! as required. A simpler argument applies if $\vert a-b\vert$ and
//! $\vert b-c\vert$ are unequal.)  Now it is easy to see that
//! $\vert Z_1^{(j+1)}-Z_1^{(j)}\vert\L\bigl\lfloor{1\over2}
//! \vert Z_2^{(j)}-Z_1^{(j)}\vert+{1\over2}\bigr\rfloor
//! \L\bigl\lfloor{1\over2}(M+1)\bigr\rfloor=\lceil M/2\rceil$.
//!
//! Another interesting fact about bisection is the identity
//! $$Z_1'+\cdots+Z_n'+Z_1''+\cdots+Z_n''=2(Z_1+\cdots+Z_n+E),$$
//! where $E$ is the sum of the rounding errors in all of the halving
//! operations ($\vert E\vert\L n(n-1)/4$).
//!
//! @ We will later reduce the problem of digitizing a complex cubic
//! $z(t)=B(z_0,z_1,z_2,z_3;t)$ to the following simpler problem:
//! Given two real cubics
//! $x(t)=B(x_0,x_1,x_2,x_3;t)$
//! and $y(t)=B(y_0,y_1,y_2,y_3;t)$ that are monotone nondecreasing,
//! determine the set of integer points
//! $$P=\bigl\{\bigl(\lfloor x(t)\rfloor,\lfloor y(t)\rfloor\bigr)
//! \bigm\vert 0\L t\L 1\bigr\}.$$
//! Well, the problem isn't actually quite so clean as this; when the path
//! goes very near an integer point $(a,b)$, computational errors may
//! make us think that $P$ contains $(a-1,b)$ while in reality it should
//! contain $(a,b-1)$. Furthermore, if the path goes {\sl exactly\/}
//! through the integer points $(a-1,b-1)$ and
//! $(a,b)$, we will want $P$ to contain one
//! of the two points $(a-1,b)$ or $(a,b-1)$, so that $P$ can be described
//! entirely by ``rook moves'' upwards or to the right; no diagonal
//! moves from $(a-1,b-1)$ to~$(a,b)$ will be allowed.
//!
//! Thus, the set $P$ we wish to compute will merely be an approximation
//! to the set described in the formula above. It will consist of
//! $\lfloor x(1)\rfloor-\lfloor x(0)\rfloor$ rightward moves and
//! $\lfloor y(1)\rfloor-\lfloor y(0)\rfloor$ upward moves, intermixed
//! in some order. Our job will be to figure out a suitable order.
//!
//! The following recursive strategy suggests itself, when we recall that
//! $x(0)=x_0$, $x(1)=x_3$, $y(0)=y_0$, and $y(1)=y_3$:
//!
//! \smallskip
//! If $\lfloor x_0\rfloor=\lfloor x_3\rfloor$ then take
//! $\lfloor y_3\rfloor-\lfloor y_0\rfloor$ steps up.
//!
//! Otherwise if $\lfloor y_0\rfloor=\lfloor y_3\rfloor$ then take
//! $\lfloor x_3\rfloor-\lfloor x_0\rfloor$ steps to the right.
//!
//! Otherwise bisect the current cubics and repeat the process on both halves.
//!
//! \yskip\noindent
//! This intuitively appealing formulation does not quite solve the problem,
//! because it may never terminate. For example, it's not hard to see that
//! no steps will {\sl ever\/} be taken if $(x_0,x_1,x_2,x_3)=(y_0,y_1,y_2,y_3)$!
//! However, we can surmount this difficulty with a bit of care; so let's
//! proceed to flesh out the algorithm as stated, before worrying about
//! such details.
//!
//! The bisect-and-double strategy discussed above suggests that we represent
//! $(x_0,x_1,x_2,x_3)$ by $(X_1,X_2,X_3)$, where $X_k=2^l(x_k-x_{k-1})$
//! for some~$l$. Initially $l=16$, since the $x$'s are |scaled|.
//! In order to deal with other aspects of the algorithm we will want to
//! maintain also the quantities $m=\lfloor x_3\rfloor-\lfloor x_0\rfloor$
//! and $R=2^l(x_0\bmod 1)$. Similarly,
//! $(y_0,y_1,y_2,y_3)$ will be represented by $(Y_1,Y_2,Y_3)$,
//! $n=\lfloor y_3\rfloor-\lfloor y_0\rfloor$,
//! and $S=2^l(y_0\bmod 1)$. The algorithm now takes the following form:
//!
//! \smallskip
//! If $m=0$ then take $n$ steps up.
//!
//! Otherwise if $n=0$ then take $m$ steps to the right.
//!
//! Otherwise bisect the current cubics and repeat the process on both halves.
//!
//! \smallskip\noindent
//! The bisection process for $(X_1,X_2,X_3,m,R,l)$ reduces, in essence,
//! to the following formulas:
//! $$\vbox{\halign{$#\hfil$\cr
//! X_2'=\\{half}(X_1+X_2),\quad
//! X_2''=\\{half}(X_2+X_3),\quad
//! X_3'=\\{half}(X_2'+X_2''),\cr
//! X_1'=X_1,\quad
//! X_1''=X_3',\quad
//! X_3''=X_3,\cr
//! R'=2R,\quad
//! T=X_1'+X_2'+X_3'+R',\quad
//! R''=T\bmod 2^{l+1},\cr
//! m'=\lfloor T/2^{l+1}\rfloor,\quad
//! m''=m-m'.\cr}}$$
//!
//! @ When $m=n=1$, the computation can be speeded up because we simply
//! need to decide between two alternatives, (up,\thinspace right)
//! versus (right,\thinspace up). There appears to be no simple, direct
//! way to make the correct decision by looking at the values of
//! $(X_1,X_2,X_3,R)$ and
//! $(Y_1,Y_2,Y_3,S)$; but we can streamline the bisection process, and
//! we can use the fact that only one of the two descendants needs to
//! be examined after each bisection. Furthermore, we observed earlier
//! that after several levels of bisection the $X$'s and $Y$'s will be nearly
//! equal; so we will be justified in assuming that the curve is essentially a
//! straight line. (This, incidentally, solves the problem of infinite
//! recursion mentioned earlier.)
//!
//! It is possible to show that
//! $$m=\bigl\lfloor(X_1+X_2+X_3+R+E)\,/\,2^l\bigr\rfloor,$$
//! where $E$ is an accumulated rounding error that is at most
//! $3\cdot(2^{l-16}-1)$ in absolute value. We will make sure that
//! the $X$'s are less than $2^{28}$; hence when $l=30$ we must
//! have |m<=1|. This proves that the special case $m=n=1$ is
//! bound to be reached by the time $l=30$. Furthermore $l=30$ is
//! a suitable time to make the straight line approximation,
//! if the recursion hasn't already died out, because the maximum
//! difference between $X$'s will then be $<2^{14}$; this corresponds
//! to an error of $<1$ with respect to the original scaling.
//! (Stating this another way, each bisection makes the curve two bits
//! closer to a straight line, hence 14 bisections are sufficient for
//! 28-bit accuracy.)
//!
//! In the case of a straight line, the curve goes first right, then up,
//! if and only if $(T-2^l)(2^l-S)>(U-2^l)(2^l-R)$, where
//! $T=X_1+X_2+X_3+R$ and $U=Y_1+Y_2+Y_3+S$. For the actual curve
//! essentially runs from $(R/2^l,S/2^l)$ to $(T/2^l,U/2^l)$, and
//! we are testing whether or not $(1,1)$ is above the straight
//! line connecting these two points. (This formula assumes that $(1,1)$
//! is not exactly on the line.)
//!
//! @ We have glossed over the problem of tie-breaking in ambiguous
//! cases when the cubic curve passes exactly through integer points.
//! \MF\ finesses this problem by assuming that coordinates
//! $(x,y)$ actually stand for slightly perturbed values $(x+\xi,y+\eta)$,
//! where $\xi$ and~$\eta$ are infinitesimals whose signs will determine
//! what to do when $x$ and/or~$y$ are exact integers. The quantities
//! $\lfloor x\rfloor$ and~$\lfloor y\rfloor$ in the formulas above
//! should actually read $\lfloor x+\xi\rfloor$ and $\lfloor y+\eta\rfloor$.
//!
//! If $x$ is a |scaled| value, we have $\lfloor x+\xi\rfloor=\lfloor x\rfloor$
//! if $\xi>0$, and $\lfloor x+\xi\rfloor=\lfloor x-2^{-16}\rfloor$ if
//! $\xi<0$. It is convenient to represent $\xi$ by the integer |xi_corr|,
//! defined to be 0~if $\xi>0$ and 1~if $\xi<0$; then, for example, the
//! integer $\lfloor x+\xi\rfloor$ can be computed as
//! |floor_unscaled(x-xi_corr)|. Similarly, $\eta$ is conveniently
//! represented by~|eta_corr|.
//!
//! In our applications the sign of $\xi-\eta$ will always be the same as
//! the sign of $\xi$. Therefore it turns out that the rule for straight
//! lines, as stated above, should be modified as follows in the case of
//! ties: The line goes first right, then up, if and only if
//! $(T-2^l)(2^l-S)+\xi>(U-2^l)(2^l-R)$. And this relation holds iff
//! $|ab_vs_cd|(T-2^l,2^l-S,U-2^l,2^l-R)-|xi_corr|\ge0$.
//!
//! These conventions for rounding are symmetrical, in the sense that the
//! digitized moves obtained from $(x_0,x_1,x_2,x_3,y_0,y_1,y_2,y_3,\xi,\eta)$
//! will be exactly complementary to the moves that would be obtained from
//! $(-x_3,-x_2,-x_1,-x_0,-y_3,-y_2,-y_1,-y_0,-\xi,-\eta)$, if arithmetic
//! is exact. However, truncation errors in the bisection process might
//! upset the symmetry. We can restore much of the lost symmetry by adding
//! |xi_corr| or |eta_corr| when halving the data.
//!
//! @ One further possibility needs to be mentioned: The algorithm
//! will be applied only to cubic polynomials $B(x_0,x_1,x_2,x_3;t)$ that
//! are nondecreasing as $t$~varies from 0 to~1; this condition turns
//! out to hold if and only if $x_0\L x_1$ and $x_2\L x_3$, and either
//! $x_1\L x_2$ or $(x_1-x_2)^2\L(x_1-x_0)(x_3-x_2)$. If bisection were
//! carried out with perfect accuracy, these relations would remain
//! invariant. But rounding errors can creep in, hence the bisection
//! algorithm can produce non-monotonic subproblems from monotonic
//! initial conditions. This leads to the potential danger that $m$ or~$n$
//! could become negative in the algorithm described above.
//!
//! For example, if we start with $(x_1-x_0,x_2-x_1,x_3-x_2)=
//! (X_1,X_2,X_3)=(7,-16,39)$, the corresponding polynomial is
//! monotonic, because $16^2<7\cdot39$. But the bisection algorithm
//! produces the left descendant $(7,-5,3)$, which is nonmonotonic;
//! its right descendant is~$(0,-1,3)$.
//!
//! \def\xt{{\tilde x}}
//! Fortunately we can prove that such rounding errors will never cause
//! the algorithm to make a tragic mistake. At every stage we are working
//! with numbers corresponding to a cubic polynomial $B(\xt_0,
//! \xt_1,\xt_2,\xt_3)$ that approximates some
//! monotonic polynomial $B(x_0,x_1,x_2,x_3)$. The accumulated errors are
//! controlled so that $\vert x_k-\xt_k\vert<\epsilon=3\cdot2^{-16}$.
//! If bisection is done at some stage of the recursion, we have
//! $m=\lfloor\xt_3\rfloor-\lfloor\xt_0\rfloor>0$, and the algorithm
//! computes a bisection value $\bar x$ such that $m'=\lfloor\bar x\rfloor-
//! \lfloor\xt_0\rfloor$
//! and $m''=\lfloor\xt_3\rfloor-\lfloor\bar x\rfloor$. We want to prove
//! that neither $m'$ nor $m''$ can be negative. Since $\bar x$ is an
//! approximation to a value in the interval $[x_0,x_3]$, we have
//! $\bar x>x_0-\epsilon$ and $\bar x<x_3+\epsilon$, hence $\bar x>
//! \xt_0-2\epsilon$ and $\bar x<\xt_3+2\epsilon$.
//! If $m'$ is negative we must have $\xt_0\bmod 1<2\epsilon$;
//! if $m''$ is negative we must have $\xt_3\bmod 1>1-2\epsilon$.
//! In either case the condition $\lfloor\xt_3\rfloor-\lfloor\xt_0\rfloor>0$
//! implies that $\xt_3-\xt_0>1-2\epsilon$, hence $x_3-x_0>1-4\epsilon$.
//! But it can be shown that if $B(x_0,x_1,x_2,x_3;t)$ is a monotonic
//! cubic, then $B(x_0,x_1,x_2,x_3;{1\over2})$ is always between
//! $.06[x_0,x_3]$ and $.94[x_0,x_3]$; and it is impossible for $\bar x$
//! to be within~$\epsilon$ of such a number. Contradiction!
//! (The constant .06 is actually $(2-\sqrt3\,)/4$; the worst case
//! occurs for polynomials like $B(0,2-\sqrt3,1-\sqrt3,3;t)$.)
//!
//! @ OK, now that a long theoretical preamble has justified the
//! bisection-and-doubling algorithm, we are ready to proceed with
//! its actual coding. But we still haven't discussed the
//! form of the output.
//!
//! For reasons to be discussed later, we shall find it convenient to
//! record the output as follows: Moving one step up is represented by
//! appending a `1' to a list; moving one step right is represented by
//! adding unity to the element at the end of the list. Thus, for example,
//! the net effect of ``(up, right, right, up, right)'' is to append
//! $(3,2)$.
//!
//! The list is kept in a global array called |move|. Before starting the
//! algorithm, \MF\ should check that $\\{move\_ptr}+\lfloor y_3\rfloor
//! -\lfloor y_0\rfloor\L\\{move\_size}$, so that the list won't exceed
//! the bounds of this array.
//!
//! @<Glob...@>=
//! @!move:array[0..move_size] of integer; {the recorded moves}
//! @!move_ptr:0..move_size; {the number of items in the |move| list}
//!
