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
//! @ When bisection occurs, we ``push'' the subproblem corresponding
//! to the right-hand subinterval onto the |bisect_stack| while
//! we continue to work on the left-hand subinterval. Thus, the |bisect_stack|
//! will hold $(X_1,X_2,X_3,R,m,Y_1,Y_2,Y_3,S,n,l)$ values for
//! subproblems yet to be tackled.
//!
//! At most 15 subproblems will be on the stack at once (namely, for
//! $l=15$,~16, \dots,~29); but the stack is bigger than this, because
//! it is used also for more complicated bisection algorithms.
//!
//! @d stack_x1==bisect_stack[bisect_ptr] {stacked value of $X_1$}
//! @d stack_x2==bisect_stack[bisect_ptr+1] {stacked value of $X_2$}
//! @d stack_x3==bisect_stack[bisect_ptr+2] {stacked value of $X_3$}
//! @d stack_r==bisect_stack[bisect_ptr+3] {stacked value of $R$}
//! @d stack_m==bisect_stack[bisect_ptr+4] {stacked value of $m$}
//! @d stack_y1==bisect_stack[bisect_ptr+5] {stacked value of $Y_1$}
//! @d stack_y2==bisect_stack[bisect_ptr+6] {stacked value of $Y_2$}
//! @d stack_y3==bisect_stack[bisect_ptr+7] {stacked value of $Y_3$}
//! @d stack_s==bisect_stack[bisect_ptr+8] {stacked value of $S$}
//! @d stack_n==bisect_stack[bisect_ptr+9] {stacked value of $n$}
//! @d stack_l==bisect_stack[bisect_ptr+10] {stacked value of $l$}
//! @d move_increment=11 {number of items pushed by |make_moves|}
//!
//! @<Glob...@>=
//! @!bisect_stack:array[0..bistack_size] of integer;
//! @!bisect_ptr:0..bistack_size;
//!
//! @ @<Check the ``constant'' values...@>=
//! if 15*move_increment>bistack_size then bad:=31;
//!
//! @ The |make_moves| subroutine is given |scaled| values $(x_0,x_1,x_2,x_3)$
//! and $(y_0,y_1,y_2,y_3)$ that represent monotone-nondecreasing polynomials;
//! it makes $\lfloor x_3+\xi\rfloor-\lfloor x_0+\xi\rfloor$ rightward moves
//! and $\lfloor y_3+\eta\rfloor-\lfloor y_0+\eta\rfloor$ upward moves, as
//! explained earlier.  (Here $\lfloor x+\xi\rfloor$ actually stands for
//! $\lfloor x/2^{16}-|xi_corr|\rfloor$, if $x$ is regarded as an integer
//! without scaling.) The unscaled integers $x_k$ and~$y_k$ should be less
//! than $2^{28}$ in magnitude.
//!
//! It is assumed that $|move_ptr| + \lfloor y_3+\eta\rfloor -
//! \lfloor y_0+\eta\rfloor < |move_size|$ when this procedure is called,
//! so that the capacity of the |move| array will not be exceeded.
//!
//! The variables |r| and |s| in this procedure stand respectively for
//! $R-|xi_corr|$ and $S-|eta_corr|$ in the theory discussed above.
//!
//! @p procedure make_moves(@!xx0,@!xx1,@!xx2,@!xx3,@!yy0,@!yy1,@!yy2,@!yy3:
//!   scaled;@!xi_corr,@!eta_corr:small_number);
//! label continue, done, exit;
//! var @!x1,@!x2,@!x3,@!m,@!r,@!y1,@!y2,@!y3,@!n,@!s,@!l:integer;
//!   {bisection variables explained above}
//! @!q,@!t,@!u,@!x2a,@!x3a,@!y2a,@!y3a:integer; {additional temporary registers}
//! begin if (xx3<xx0)or(yy3<yy0) then confusion("m");
//! @:this can't happen m}{\quad m@>
//! l:=16; bisect_ptr:=0;@/
//! x1:=xx1-xx0; x2:=xx2-xx1; x3:=xx3-xx2;
//! if xx0>=xi_corr then r:=(xx0-xi_corr) mod unity
//! else r:=unity-1-((-xx0+xi_corr-1) mod unity);
//! m:=(xx3-xx0+r) div unity;@/
//! y1:=yy1-yy0; y2:=yy2-yy1; y3:=yy3-yy2;
//! if yy0>=eta_corr then s:=(yy0-eta_corr) mod unity
//! else s:=unity-1-((-yy0+eta_corr-1) mod unity);
//! n:=(yy3-yy0+s) div unity;@/
//! if (xx3-xx0>=fraction_one)or(yy3-yy0>=fraction_one) then
//!   @<Divide the variables by two, to avoid overflow problems@>;
//! loop@+  begin continue:@<Make moves for current subinterval;
//!     if bisection is necessary, push the second subinterval
//!     onto the stack, and |goto continue| in order to handle
//!     the first subinterval@>;
//!   if bisect_ptr=0 then return;
//!   @<Remove a subproblem for |make_moves| from the stack@>;
//!   end;
//! exit: end;
//!
//! @ @<Remove a subproblem for |make_moves| from the stack@>=
//! bisect_ptr:=bisect_ptr-move_increment;@/
//! x1:=stack_x1; x2:=stack_x2; x3:=stack_x3; r:=stack_r; m:=stack_m;@/
//! y1:=stack_y1; y2:=stack_y2; y3:=stack_y3; s:=stack_s; n:=stack_n;@/
//! l:=stack_l
//!
//! @ Our variables |(x1,x2,x3)| correspond to $(X_1,X_2,X_3)$ in the notation
//! of the theory developed above. We need to keep them less than $2^{28}$
//! in order to avoid integer overflow in weird circumstances.
//! For example, data like $x_0=-2^{28}+2^{16}-1$ and $x_1=x_2=x_3=2^{28}-1$
//! would otherwise be problematical. Hence this part of the code is
//! needed, if only to thwart malicious users.
//!
//! @<Divide the variables by two, to avoid overflow problems@>=
//! begin x1:=half(x1+xi_corr); x2:=half(x2+xi_corr); x3:=half(x3+xi_corr);
//! r:=half(r+xi_corr);@/
//! y1:=half(y1+eta_corr); y2:=half(y2+eta_corr); y3:=half(y3+eta_corr);
//! s:=half(s+eta_corr);@/
//! l:=15;
//! end
//!
//! @ @<Make moves...@>=
//! if m=0 then @<Move upward |n| steps@>
//! else if n=0 then @<Move to the right |m| steps@>
//! else if m+n=2 then @<Make one move of each kind@>
//! else  begin incr(l); stack_l:=l;@/
//!   stack_x3:=x3; stack_x2:=half(x2+x3+xi_corr); x2:=half(x1+x2+xi_corr);
//!   x3:=half(x2+stack_x2+xi_corr); stack_x1:=x3;@/
//!   r:=r+r+xi_corr; t:=x1+x2+x3+r;@/
//!   q:=t div two_to_the[l]; stack_r:=t mod two_to_the[l];@/
//!   stack_m:=m-q; m:=q;@/
//!   stack_y3:=y3; stack_y2:=half(y2+y3+eta_corr); y2:=half(y1+y2+eta_corr);
//!   y3:=half(y2+stack_y2+eta_corr); stack_y1:=y3;@/
//!   s:=s+s+eta_corr; u:=y1+y2+y3+s;@/
//!   q:=u div two_to_the[l]; stack_s:=u mod two_to_the[l];@/
//!   stack_n:=n-q; n:=q;@/
//!   bisect_ptr:=bisect_ptr+move_increment; goto continue;
//!   end
//!
//! @ @<Move upward |n| steps@>=
//! while n>0 do
//!   begin incr(move_ptr); move[move_ptr]:=1; decr(n);
//!   end
//!
//! @ @<Move to the right |m| steps@>=
//! move[move_ptr]:=move[move_ptr]+m
//!
//! @ @<Make one move of each kind@>=
//! begin r:=two_to_the[l]-r; s:=two_to_the[l]-s;@/
//! while l<30 do
//!   begin x3a:=x3; x2a:=half(x2+x3+xi_corr); x2:=half(x1+x2+xi_corr);
//!   x3:=half(x2+x2a+xi_corr);
//!   t:=x1+x2+x3; r:=r+r-xi_corr;@/
//!   y3a:=y3; y2a:=half(y2+y3+eta_corr); y2:=half(y1+y2+eta_corr);
//!   y3:=half(y2+y2a+eta_corr);
//!   u:=y1+y2+y3; s:=s+s-eta_corr;@/
//!   if t<r then if u<s then @<Switch to the right subinterval@>
//!     else  begin @<Move up then right@>; goto done;
//!       end
//!   else if u<s then
//!     begin @<Move right then up@>; goto done;
//!     end;
//!   incr(l);
//!   end;
//! r:=r-xi_corr; s:=s-eta_corr;
//! if ab_vs_cd(x1+x2+x3,s,y1+y2+y3,r)-xi_corr>=0 then @<Move right then up@>
//!   else @<Move up then right@>;
//! done:
//! end
//!
//! @ @<Switch to the right subinterval@>=
//! begin x1:=x3; x2:=x2a; x3:=x3a; r:=r-t;
//! y1:=y3; y2:=y2a; y3:=y3a; s:=s-u;
//! end
//!
//! @ @<Move right then up@>=
//! begin incr(move[move_ptr]); incr(move_ptr); move[move_ptr]:=1;
//! end
//!
//! @ @<Move up then right@>=
//! begin incr(move_ptr); move[move_ptr]:=2;
//! end
//!
//! @ After |make_moves| has acted, possibly for several curves that move toward
//! the same octant, a ``smoothing'' operation might be done on the |move| array.
//! This removes optical glitches that can arise even when the curve has been
//! digitized without rounding errors.
//!
//! The smoothing process replaces the integers $a_0\ldots a_n$ in
//! |move[b..t]| by ``smoothed'' integers $a_0'\ldots a_n'$ defined as
//! follows:
//! $$a_k'=a_k+\delta\k-\delta_k;\qquad
//! \delta_k=\cases{+1,&if $1<k<n$ and $a_{k-2}\G a_{k-1}\ll a_k\G a\k$;\cr
//! -1,&if $1<k<n$ and $a_{k-2}\L a_{k-1}\gg a_k\L a\k$;\cr
//! 0,&otherwise.\cr}$$
//! Here $a\ll b$ means that $a\L b-2$, and $a\gg b$ means that $a\G b+2$.
//!
//! The smoothing operation is symmetric in the sense that, if $a_0\ldots a_n$
//! smooths to $a_0'\ldots a_n'$, then the reverse sequence $a_n\ldots a_0$
//! smooths to $a_n'\ldots a_0'$; also the complementary sequence
//! $(m-a_0)\ldots(m-a_n)$ smooths to $(m-a_0')\ldots(m-a_n')$.
//! We have $a_0'+\cdots+a_n'=a_0+\cdots+a_n$ because $\delta_0=\delta_{n+1}=0$.
//!
//! @p procedure smooth_moves(@!b,@!t:integer);
//! var@!k:1..move_size; {index into |move|}
//! @!a,@!aa,@!aaa:integer; {original values of |move[k],move[k-1],move[k-2]|}
//! begin if t-b>=3 then
//!   begin k:=b+2; aa:=move[k-1]; aaa:=move[k-2];
//!   repeat a:=move[k];
//!   if abs(a-aa)>1 then
//!     @<Increase and decrease |move[k-1]| and |move[k]| by $\delta_k$@>;
//!   incr(k); aaa:=aa; aa:=a;
//!   until k=t;
//!   end;
//! end;
//!
//! @ @<Increase and decrease |move[k-1]| and |move[k]| by $\delta_k$@>=
//! if a>aa then
//!   begin if aaa>=aa then if a>=move[k+1] then
//!     begin incr(move[k-1]); move[k]:=a-1;
//!     end;
//!   end
//! else  begin if aaa<=aa then if a<=move[k+1] then
//!     begin decr(move[k-1]); move[k]:=a+1;
//!     end;
//!   end
//!
//! @* \[20] Edge structures.
//! Now we come to \MF's internal scheme for representing what the user can
//! actually ``see,'' the edges between pixels. Each pixel has an integer
//! weight, obtained by summing the weights on all edges to its left. \MF\
//! represents only the nonzero edge weights, since most of the edges are
//! weightless; in this way, the data storage requirements grow only linearly
//! with respect to the number of pixels per point, even though two-dimensional
//! data is being represented. (Well, the actual dependence on the underlying
//! resolution is order $n\log n$, but the $\log n$ factor is buried in our
//! implicit restriction on the maximum raster size.) The sum of all edge
//! weights in each row should be zero.
//!
//! The data structure for edge weights must be compact and flexible,
//! yet it should support efficient updating and display operations. We
//! want to be able to have many different edge structures in memory at
//! once, and we want the computer to be able to translate them, reflect them,
//! and/or merge them together with relative ease.
//!
//! \MF's solution to this problem requires one single-word node per
//! nonzero edge weight, plus one two-word node for each row in a contiguous
//! set of rows. There's also a header node that provides global information
//! about the entire structure.
//!
//! @ Let's consider the edge-weight nodes first. The |info| field of such
//! nodes contains both an $m$~value and a weight~$w$, in the form
//! $8m+w+c$, where $c$ is a constant that depends on data found in the header.
//! We shall consider $c$ in detail later; for now, it's best just to think
//! of it as a way to compensate for the fact that $m$ and~$w$ can be negative,
//! together with the fact that an |info| field must have a value between
//! |min_halfword| and |max_halfword|. The $m$ value is an unscaled $x$~coordinate,
//! so it satisfies $\vert m\vert<
//! 4096$; the $w$ value is always in the range $1\L\vert w\vert\L3$. We can
//! unpack the data in the |info| field by fetching |ho(info(p))=
//! info(p)-min_halfword| and dividing this nonnegative number by~8;
//! the constant~$c$ will be chosen so that the remainder of this division
//! is $4+w$. Thus, for example, a remainder of~3 will correspond to
//! the edge weight $w=-1$.
//!
//! Every row of an edge structure contains two lists of such edge-weight
//! nodes, called the |sorted| and |unsorted| lists, linked together by their
//! |link| fields in the normal way. The difference between them is that we
//! always have |info(p)<=info(link(p))| in the |sorted| list, but there's no
//! such restriction on the elements of the |unsorted| list. The reason for
//! this distinction is that it would take unnecessarily long to maintain
//! edge-weight lists in sorted order while they're being updated; but when we
//! need to process an entire row from left to right in order of the
//! $m$~values, it's fairly easy and quick to sort a short list of unsorted
//! elements and to merge them into place among their sorted cohorts.
//! Furthermore, the fact that the |unsorted| list is empty can sometimes be
//! used to good advantage, because it allows us to conclude that a particular
//! row has not changed since the last time we sorted it.
//!
//! The final |link| of the |sorted| list will be |sentinel|, which points to
//! a special one-word node whose |info| field is essentially infinite; this
//! facilitates the sorting and merging operations. The final |link| of the
//! |unsorted| list will be either |null| or |void|, where |void=null+1|
//! is used to avoid redisplaying data that has not changed:
//! A |void| value is stored at the head of the
//! unsorted list whenever the corresponding row has been displayed.
//!
//! @d zero_w=4
//! @d void==null+1
//!
//! @<Initialize table entries...@>=
//! info(sentinel):=max_halfword; {|link(sentinel)=null|}
//!
//! @ The rows themselves are represented by row header nodes that
//! contain four link fields. Two of these four, |sorted| and |unsorted|,
//! point to the first items of the edge-weight lists just mentioned.
//! The other two, |link| and |knil|, point to the headers of the two
//! adjacent rows. If |p| points to the header for row number~|n|, then
//! |link(p)| points up to the header for row~|n+1|, and |knil(p)| points
//! down to the header for row~|n-1|. This double linking makes it
//! convenient to move through consecutive rows either upward or downward;
//! as usual, we have |link(knil(p))=knil(link(p))=p| for all row headers~|p|.
//!
//! The row associated with a given value of |n| contains weights for
//! edges that run between the lattice points |(m,n)| and |(m,n+1)|.
//!
//! @d knil==info {inverse of the |link| field, in a doubly linked list}
//! @d sorted_loc(#)==#+1 {where the |sorted| link field resides}
//! @d sorted(#)==link(sorted_loc(#)) {beginning of the list of sorted edge weights}
//! @d unsorted(#)==info(#+1) {beginning of the list of unsorted edge weights}
//! @d row_node_size=2 {number of words in a row header node}
//!
//! @ The main header node |h| for an edge structure has |link| and |knil|
//! fields that link it above the topmost row and below the bottommost row.
//! It also has fields called |m_min|, |m_max|, |n_min|, and |n_max| that
//! bound the current extent of the edge data: All |m| values in edge-weight
//! nodes should lie between |m_min(h)-4096| and |m_max(h)-4096|, inclusive.
//! Furthermore the topmost row header, pointed to by |knil(h)|,
//! is for row number |n_max(h)-4096|; the bottommost row header, pointed to by
//! |link(h)|, is for row number |n_min(h)-4096|.
//!
//! The offset constant |c| that's used in all of the edge-weight data is
//! represented implicitly in |m_offset(h)|; its actual value is
//! $$\hbox{|c=min_halfword+zero_w+8*m_offset(h)|.}$$
//! Notice that it's possible to shift an entire edge structure by an
//! amount $(\Delta m,\Delta n)$ by adding $\Delta n$ to |n_min(h)| and |n_max(h)|,
//! adding $\Delta m$ to |m_min(h)| and |m_max(h)|, and subtracting
//! $\Delta m$ from |m_offset(h)|;
//! none of the other edge data needs to be modified. Initially the |m_offset|
//! field is~4096, but it will change if the user requests such a shift.
//! The contents of these five fields should always be positive and less than
//! 8192; |n_max| should, in fact, be less than 8191.  Furthermore
//! |m_min+m_offset-4096| and |m_max+m_offset-4096| must also lie strictly
//! between 0 and 8192, so that the |info| fields of edge-weight nodes will
//! fit in a halfword.
//!
//! The header node of an edge structure also contains two somewhat unusual
//! fields that are called |last_window(h)| and |last_window_time(h)|. When this
//! structure is displayed in window~|k| of the user's screen, after that
//! window has been updated |t| times, \MF\ sets |last_window(h):=k| and
//! |last_window_time(h):=t|; it also sets |unsorted(p):=void| for all row
//! headers~|p|, after merging any existing unsorted weights with the sorted
//! ones.  A subsequent display in the same window will be able to avoid
//! redisplaying rows whose |unsorted| list is still |void|, if the window
//! hasn't been used for something else in the meantime.
//!
//! A pointer to the row header of row |n_pos(h)-4096| is provided in
//! |n_rover(h)|. Most of the algorithms that update an edge structure
//! are able to get by without random row references; they usually
//! access rows that are neighbors of each other or of the current |n_pos| row.
//! Exception: If |link(h)=h| (so that the edge structure contains
//! no rows), we have |n_rover(h)=h|, and |n_pos(h)| is irrelevant.
//!
//! @d zero_field=4096 {amount added to coordinates to make them positive}
//! @d n_min(#)==info(#+1) {minimum row number present, plus |zero_field|}
//! @d n_max(#)==link(#+1) {maximum row number present, plus |zero_field|}
//! @d m_min(#)==info(#+2) {minimum column number present, plus |zero_field|}
//! @d m_max(#)==link(#+2) {maximum column number present, plus |zero_field|}
//! @d m_offset(#)==info(#+3) {translation of $m$ data in edge-weight nodes}
//! @d last_window(#)==link(#+3) {the last display went into this window}
//! @d last_window_time(#)==mem[#+4].int {after this many window updates}
//! @d n_pos(#)==info(#+5) {the row currently in |n_rover|, plus |zero_field|}
//! @d n_rover(#)==link(#+5) {a row recently referenced}
//! @d edge_header_size=6 {number of words in an edge-structure header}
//! @d valid_range(#)==(abs(#-4096)<4096) {is |#| strictly between 0 and 8192?}
//! @d empty_edges(#)==link(#)=# {are there no rows in this edge header?}
//!
//! @p procedure init_edges(@!h:pointer); {initialize an edge header to null values}
//! begin knil(h):=h; link(h):=h;@/
//! n_min(h):=zero_field+4095; n_max(h):=zero_field-4095;
//! m_min(h):=zero_field+4095; m_max(h):=zero_field-4095;
//! m_offset(h):=zero_field;@/
//! last_window(h):=0; last_window_time(h):=0;@/
//! n_rover(h):=h; n_pos(h):=0;@/
//! end;
//!
//! @ When a lot of work is being done on a particular edge structure, we plant
//! a pointer to its main header in the global variable |cur_edges|.
//! This saves us from having to pass this pointer as a parameter over and
//! over again between subroutines.
//!
//! Similarly, |cur_wt| is a global weight that is being used by several
//! procedures at once.
//!
//! @<Glob...@>=
//! @!cur_edges:pointer; {the edge structure of current interest}
//! @!cur_wt:integer; {the edge weight of current interest}
//!
//! @ The |fix_offset| routine goes through all the edge-weight nodes of
//! |cur_edges| and adds a constant to their |info| fields, so that
//! |m_offset(cur_edges)| can be brought back to |zero_field|. (This
//! is necessary only in unusual cases when the offset has gotten too
//! large or too small.)
//!
//! @p procedure fix_offset;
//! var @!p,@!q:pointer; {list traversers}
//! @!delta:integer; {the amount of change}
//! begin delta:=8*(m_offset(cur_edges)-zero_field);
//! m_offset(cur_edges):=zero_field;
//! q:=link(cur_edges);
//! while q<>cur_edges do
//!   begin p:=sorted(q);
//!   while p<>sentinel do
//!     begin info(p):=info(p)-delta; p:=link(p);
//!     end;
//!   p:=unsorted(q);
//!   while p>void do
//!     begin info(p):=info(p)-delta; p:=link(p);
//!     end;
//!   q:=link(q);
//!   end;
//! end;
//!
//! @ The |edge_prep| routine makes the |cur_edges| structure ready to
//! accept new data whose coordinates satisfy |ml<=m<=mr| and |nl<=n<=nr-1|,
//! assuming that |-4096<ml<=mr<4096| and |-4096<nl<=nr<4096|. It makes
//! appropriate adjustments to |m_min|, |m_max|, |n_min|, and |n_max|,
//! adding new empty rows if necessary.
//!
//! @p procedure edge_prep(@!ml,@!mr,@!nl,@!nr:integer);
//! var @!delta:halfword; {amount of change}
//! @!p,@!q:pointer; {for list manipulation}
//! begin ml:=ml+zero_field; mr:=mr+zero_field;
//! nl:=nl+zero_field; nr:=nr-1+zero_field;@/
//! if ml<m_min(cur_edges) then m_min(cur_edges):=ml;
//! if mr>m_max(cur_edges) then m_max(cur_edges):=mr;
//! if not valid_range(m_min(cur_edges)+m_offset(cur_edges)-zero_field) or@|
//!  not valid_range(m_max(cur_edges)+m_offset(cur_edges)-zero_field) then
//!   fix_offset;
//! if empty_edges(cur_edges) then {there are no rows}
//!   begin n_min(cur_edges):=nr+1; n_max(cur_edges):=nr;
//!   end;
//! if nl<n_min(cur_edges) then
//!   @<Insert exactly |n_min(cur_edges)-nl| empty rows at the bottom@>;
//! if nr>n_max(cur_edges) then
//!   @<Insert exactly |nr-n_max(cur_edges)| empty rows at the top@>;
//! end;
//!
//! @ @<Insert exactly |n_min(cur_edges)-nl| empty rows at the bottom@>=
//! begin delta:=n_min(cur_edges)-nl; n_min(cur_edges):=nl;
//! p:=link(cur_edges);
//! repeat q:=get_node(row_node_size); sorted(q):=sentinel; unsorted(q):=void;
//! knil(p):=q; link(q):=p; p:=q; decr(delta);
//! until delta=0;
//! knil(p):=cur_edges; link(cur_edges):=p;
//! if n_rover(cur_edges)=cur_edges then n_pos(cur_edges):=nl-1;
//! end
//!
//! @ @<Insert exactly |nr-n_max(cur_edges)| empty rows at the top@>=
//! begin delta:=nr-n_max(cur_edges); n_max(cur_edges):=nr;
//! p:=knil(cur_edges);
//! repeat q:=get_node(row_node_size); sorted(q):=sentinel; unsorted(q):=void;
//! link(p):=q; knil(q):=p; p:=q; decr(delta);
//! until delta=0;
//! link(p):=cur_edges; knil(cur_edges):=p;
//! if n_rover(cur_edges)=cur_edges then n_pos(cur_edges):=nr+1;
//! end
//!
//! @ The |print_edges| subroutine gives a symbolic rendition of an edge
//! structure, for use in `\&{show}' commands. A rather terse output
//! format has been chosen since edge structures can grow quite large.
//!
//! @<Declare subroutines for printing expressions@>=
//! @t\4@>@<Declare the procedure called |print_weight|@>@;@/
//! procedure print_edges(@!s:str_number;@!nuline:boolean;@!x_off,@!y_off:integer);
//! var @!p,@!q,@!r:pointer; {for list traversal}
//! @!n:integer; {row number}
//! begin print_diagnostic("Edge structure",s,nuline);
//! p:=knil(cur_edges); n:=n_max(cur_edges)-zero_field;
//! while p<>cur_edges do
//!   begin q:=unsorted(p); r:=sorted(p);
//!   if(q>void)or(r<>sentinel) then
//!     begin print_nl("row "); print_int(n+y_off); print_char(":");
//!     while q>void do
//!       begin print_weight(q,x_off); q:=link(q);
//!       end;
//!     print(" |");
//!     while r<>sentinel do
//!       begin print_weight(r,x_off); r:=link(r);
//!       end;
//!     end;
//!   p:=knil(p); decr(n);
//!   end;
//! end_diagnostic(true);
//! end;
//!
//! @ @<Declare the procedure called |print_weight|@>=
//! procedure print_weight(@!q:pointer;@!x_off:integer);
//! var @!w,@!m:integer; {unpacked weight and coordinate}
//! @!d:integer; {temporary data register}
//! begin d:=ho(info(q)); w:=d mod 8; m:=(d div 8)-m_offset(cur_edges);
//! if file_offset>max_print_line-9 then print_nl(" ")
//! else print_char(" ");
//! print_int(m+x_off);
//! while w>zero_w do
//!   begin print_char("+"); decr(w);
//!   end;
//! while w<zero_w do
//!   begin print_char("-"); incr(w);
//!   end;
//! end;
//!
//! @ Here's a trivial subroutine that copies an edge structure. (Let's hope
//! that the given structure isn't too gigantic.)
//!
//! @p function copy_edges(@!h:pointer):pointer;
//! var @!p,@!r:pointer; {variables that traverse the given structure}
//! @!hh,@!pp,@!qq,@!rr,@!ss:pointer; {variables that traverse the new structure}
//! begin hh:=get_node(edge_header_size);
//! mem[hh+1]:=mem[h+1]; mem[hh+2]:=mem[h+2];
//! mem[hh+3]:=mem[h+3]; mem[hh+4]:=mem[h+4]; {we've now copied |n_min|, |n_max|,
//!   |m_min|, |m_max|, |m_offset|, |last_window|, and |last_window_time|}
//! n_pos(hh):=n_max(hh)+1;n_rover(hh):=hh;@/
//! p:=link(h); qq:=hh;
//! while p<>h do
//!   begin pp:=get_node(row_node_size); link(qq):=pp; knil(pp):=qq;
//!   @<Copy both |sorted| and |unsorted| lists of |p| to |pp|@>;
//!   p:=link(p); qq:=pp;
//!   end;
//! link(qq):=hh; knil(hh):=qq;
//! copy_edges:=hh;
//! end;
//!
//! @ @<Copy both |sorted| and |unsorted|...@>=
//! r:=sorted(p); rr:=sorted_loc(pp); {|link(rr)=sorted(pp)|}
//! while r<>sentinel do
//!   begin ss:=get_avail; link(rr):=ss; rr:=ss; info(rr):=info(r);@/
//!   r:=link(r);
//!   end;
//! link(rr):=sentinel;@/
//! r:=unsorted(p); rr:=temp_head;
//! while r>void do
//!   begin ss:=get_avail; link(rr):=ss; rr:=ss; info(rr):=info(r);@/
//!   r:=link(r);
//!   end;
//! link(rr):=r; unsorted(pp):=link(temp_head)
//!
//! @ Another trivial routine flips |cur_edges| about the |x|-axis
//! (i.e., negates all the |y| coordinates), assuming that at least
//! one row is present.
//!
//! @p procedure y_reflect_edges;
//! var @!p,@!q,@!r:pointer; {list manipulation registers}
//! begin p:=n_min(cur_edges);
//! n_min(cur_edges):=zero_field+zero_field-1-n_max(cur_edges);
//! n_max(cur_edges):=zero_field+zero_field-1-p;
//! n_pos(cur_edges):=zero_field+zero_field-1-n_pos(cur_edges);@/
//! p:=link(cur_edges); q:=cur_edges; {we assume that |p<>q|}
//! repeat r:=link(p); link(p):=q; knil(q):=p; q:=p; p:=r;
//! until q=cur_edges;
//! last_window_time(cur_edges):=0;
//! end;
//!
//! @ It's somewhat more difficult, yet not too hard, to reflect about the |y|-axis.
//!
//! @p procedure x_reflect_edges;
//! var @!p,@!q,@!r,@!s:pointer; {list manipulation registers}
//! @!m:integer; {|info| fields will be reflected with respect to this number}
//! begin p:=m_min(cur_edges);
//! m_min(cur_edges):=zero_field+zero_field-m_max(cur_edges);
//! m_max(cur_edges):=zero_field+zero_field-p;
//! m:=(zero_field+m_offset(cur_edges))*8+zero_w+min_halfword+zero_w+min_halfword;
//! m_offset(cur_edges):=zero_field;
//! p:=link(cur_edges);
//! repeat @<Reflect the edge-and-weight data in |sorted(p)|@>;
//! @<Reflect the edge-and-weight data in |unsorted(p)|@>;
//! p:=link(p);
//! until p=cur_edges;
//! last_window_time(cur_edges):=0;
//! end;
//!
//! @ We want to change the sign of the weight as we change the sign of the
//! |x|~coordinate. Fortunately, it's easier to do this than to negate
//! one without the other.
//!
//! @<Reflect the edge-and-weight data in |unsorted(p)|@>=
//! q:=unsorted(p);
//! while q>void do
//!   begin info(q):=m-info(q); q:=link(q);
//!   end
//!
//! @ Reversing the order of a linked list is best thought of as the process of
//! popping nodes off one stack and pushing them on another. In this case we
//! pop from stack~|q| and push to stack~|r|.
//!
//! @<Reflect the edge-and-weight data in |sorted(p)|@>=
//! q:=sorted(p); r:=sentinel;
//! while q<>sentinel do
//!   begin s:=link(q); link(q):=r; r:=q; info(r):=m-info(q); q:=s;
//!   end;
//! sorted(p):=r
//!
//! @ Now let's multiply all the $y$~coordinates of a nonempty edge structure
//! by a small integer $s>1$:
//!
//! @p procedure y_scale_edges(@!s:integer);
//! var @!p,@!q,@!pp,@!r,@!rr,@!ss:pointer; {list manipulation registers}
//! @!t:integer; {replication counter}
//! begin if (s*(n_max(cur_edges)+1-zero_field)>=4096) or@|
//!  (s*(n_min(cur_edges)-zero_field)<=-4096) then
//!   begin print_err("Scaled picture would be too big");
//! @.Scaled picture...big@>
//!   help3("I can't yscale the picture as requested---it would")@/
//!     ("make some coordinates too large or too small.")@/
//!     ("Proceed, and I'll omit the transformation.");
//!   put_get_error;
//!   end
//! else  begin n_max(cur_edges):=s*(n_max(cur_edges)+1-zero_field)-1+zero_field;
//!   n_min(cur_edges):=s*(n_min(cur_edges)-zero_field)+zero_field;
//!   @<Replicate every row exactly $s$ times@>;
//!   last_window_time(cur_edges):=0;
//!   end;
//! end;
//!
//! @ @<Replicate...@>=
//! p:=cur_edges;
//! repeat q:=p; p:=link(p);
//! for t:=2 to s do
//!   begin pp:=get_node(row_node_size); link(q):=pp; knil(p):=pp;
//!   link(pp):=p; knil(pp):=q; q:=pp;
//!   @<Copy both |sorted| and |unsorted|...@>;
//!   end;
//! until link(p)=cur_edges
//!
//! @ Scaling the $x$~coordinates is, of course, our next task.
//!
//! @p procedure x_scale_edges(@!s:integer);
//! var @!p,@!q:pointer; {list manipulation registers}
//! @!t:0..65535; {unpacked |info| field}
//! @!w:0..7; {unpacked weight}
//! @!delta:integer; {amount added to scaled |info|}
//! begin if (s*(m_max(cur_edges)-zero_field)>=4096) or@|
//!  (s*(m_min(cur_edges)-zero_field)<=-4096) then
//!   begin print_err("Scaled picture would be too big");
//! @.Scaled picture...big@>
//!   help3("I can't xscale the picture as requested---it would")@/
//!     ("make some coordinates too large or too small.")@/
//!     ("Proceed, and I'll omit the transformation.");
//!   put_get_error;
//!   end
//! else if (m_max(cur_edges)<>zero_field)or(m_min(cur_edges)<>zero_field) then
//!   begin m_max(cur_edges):=s*(m_max(cur_edges)-zero_field)+zero_field;
//!   m_min(cur_edges):=s*(m_min(cur_edges)-zero_field)+zero_field;
//!   delta:=8*(zero_field-s*m_offset(cur_edges))+min_halfword;
//!   m_offset(cur_edges):=zero_field;@/
//!   @<Scale the $x$~coordinates of each row by $s$@>;
//!   last_window_time(cur_edges):=0;
//!   end;
//! end;
//!
//! @ The multiplications cannot overflow because we know that |s<4096|.
//!
//! @<Scale the $x$~coordinates of each row by $s$@>=
//! q:=link(cur_edges);
//! repeat p:=sorted(q);
//! while p<>sentinel do
//!   begin t:=ho(info(p)); w:=t mod 8; info(p):=(t-w)*s+w+delta; p:=link(p);
//!   end;
//! p:=unsorted(q);
//! while p>void do
//!   begin t:=ho(info(p)); w:=t mod 8; info(p):=(t-w)*s+w+delta; p:=link(p);
//!   end;
//! q:=link(q);
//! until q=cur_edges
//!
//! @ Here is a routine that changes the signs of all the weights, without
//! changing anything else.
//!
//! @p procedure negate_edges(@!h:pointer);
//! label done;
//! var @!p,@!q,@!r,@!s,@!t,@!u:pointer; {structure traversers}
//! begin p:=link(h);
//! while p<>h do
//!   begin q:=unsorted(p);
//!   while q>void do
//!     begin info(q):=8-2*((ho(info(q))) mod 8)+info(q); q:=link(q);
//!     end;
//!   q:=sorted(p);
//!   if q<>sentinel then
//!     begin repeat info(q):=8-2*((ho(info(q))) mod 8)+info(q); q:=link(q);
//!     until q=sentinel;
//!     @<Put the list |sorted(p)| back into sort@>;
//!     end;
//!   p:=link(p);
//!   end;
//! last_window_time(h):=0;
//! end;
//!
//! @ \MF\ would work even if the code in this section were omitted, because
//! a list of edge-and-weight data that is sorted only by
//! |m| but not~|w| turns out to be good enough for correct operation.
//! However, the author decided not to make the program even trickier than
//! it is already, since |negate_edges| isn't needed very often.
//! The simpler-to-state condition, ``keep the |sorted| list fully sorted,''
//! is therefore being preserved at the cost of extra computation.
//!
//! @<Put the list |sorted(p)|...@>=
//! u:=sorted_loc(p); q:=link(u); r:=q; s:=link(r); {|q=sorted(p)|}
//! loop@+  if info(s)>info(r) then
//!     begin link(u):=q;
//!     if s=sentinel then goto done;
//!     u:=r; q:=s; r:=q; s:=link(r);
//!     end
//!   else  begin t:=s; s:=link(t); link(t):=q; q:=t;
//!     end;
//! done: link(r):=sentinel
//!
//! @ The |unsorted| edges of a row are merged into the |sorted| ones by
//! a subroutine called |sort_edges|. It uses simple insertion sort,
//! followed by a merge, because the unsorted list is supposedly quite short.
//! However, the unsorted list is assumed to be nonempty.
//!
//! @p procedure sort_edges(@!h:pointer); {|h| is a row header}
//! label done;
//! var @!k:halfword; {key register that we compare to |info(q)|}
//! @!p,@!q,@!r,@!s:pointer;
//! begin r:=unsorted(h); unsorted(h):=null;
//! p:=link(r); link(r):=sentinel; link(temp_head):=r;
//! while p>void do {sort node |p| into the list that starts at |temp_head|}
//!   begin k:=info(p); q:=temp_head;
//!   repeat r:=q; q:=link(r);
//!   until k<=info(q);
//!   link(r):=p; r:=link(p); link(p):=q; p:=r;
//!   end;
//! @<Merge the |temp_head| list into |sorted(h)|@>;
//! end;
//!
//! @ In this step we use the fact that |sorted(h)=link(sorted_loc(h))|.
//!
//! @<Merge the |temp_head| list into |sorted(h)|@>=
//! begin r:=sorted_loc(h); q:=link(r); p:=link(temp_head);
//! loop@+  begin k:=info(p);
//!   while k>info(q) do
//!     begin r:=q; q:=link(r);
//!     end;
//!   link(r):=p; s:=link(p); link(p):=q;
//!   if s=sentinel then goto done;
//!   r:=p; p:=s;
//!   end;
//! done:end
//!
//! @ The |cull_edges| procedure ``optimizes'' an edge structure by making all
//! the pixel weights either |w_out| or~|w_in|. The weight will be~|w_in| after the
//! operation if and only if it was in the closed interval |[w_lo,w_hi]|
//! before, where |w_lo<=w_hi|. Either |w_out| or |w_in| is zero, while the other is
//! $\pm1$, $\pm2$, or $\pm3$. The parameters will be such that zero-weight
//! pixels will remain of weight zero.  (This is fortunate,
//! because there are infinitely many of them.)
//!
//! The procedure also computes the tightest possible bounds on the resulting
//! data, by updating |m_min|, |m_max|, |n_min|, and~|n_max|.
//!
//! @p procedure cull_edges(@!w_lo,@!w_hi,@!w_out,@!w_in:integer);
//! label done;
//! var @!p,@!q,@!r,@!s:pointer; {for list manipulation}
//! @!w:integer; {new weight after culling}
//! @!d:integer; {data register for unpacking}
//! @!m:integer; {the previous column number, including |m_offset|}
//! @!mm:integer; {the next column number, including |m_offset|}
//! @!ww:integer; {accumulated weight before culling}
//! @!prev_w:integer; {value of |w| before column |m|}
//! @!n,@!min_n,@!max_n:pointer; {current and extreme row numbers}
//! @!min_d,@!max_d:pointer; {extremes of the new edge-and-weight data}
//! begin min_d:=max_halfword; max_d:=min_halfword;
//! min_n:=max_halfword; max_n:=min_halfword;@/
//! p:=link(cur_edges); n:=n_min(cur_edges);
//! while p<>cur_edges do
//!   begin if unsorted(p)>void then sort_edges(p);
//!   if sorted(p)<>sentinel then
//!     @<Cull superfluous edge-weight entries from |sorted(p)|@>;
//!   p:=link(p); incr(n);
//!   end;
//! @<Delete empty rows at the top and/or bottom;
//!   update the boundary values in the header@>;
//! last_window_time(cur_edges):=0;
//! end;
//!
//! @ The entire |sorted| list is returned to available memory in this step;
//! a new list is built starting (temporarily) at |temp_head|.
//! Since several edges can occur at the same column, we need to be looking
//! ahead of where the actual culling takes place. This means that it's
//! slightly tricky to get the iteration started and stopped.
//!
//! @<Cull superfluous...@>=
//! begin r:=temp_head; q:=sorted(p); ww:=0; m:=1000000; prev_w:=0;
//! loop@+  begin if q=sentinel then mm:=1000000
//!   else  begin d:=ho(info(q)); mm:=d div 8; ww:=ww+(d mod 8)-zero_w;
//!     end;
//!   if mm>m then
//!     begin @<Insert an edge-weight for edge |m|, if the new pixel
//!       weight has changed@>;
//!     if q=sentinel then goto done;
//!     end;
//!   m:=mm;
//!   if ww>=w_lo then if ww<=w_hi then w:=w_in
//!     else w:=w_out
//!   else w:=w_out;
//!   s:=link(q); free_avail(q); q:=s;
//!   end;
//! done: link(r):=sentinel; sorted(p):=link(temp_head);
//! if r<>temp_head then @<Update the max/min amounts@>;
//! end
//!
//! @ @<Insert an edge-weight for edge |m|, if...@>=
//! if w<>prev_w then
//!   begin s:=get_avail; link(r):=s;
//!   info(s):=8*m+min_halfword+zero_w+w-prev_w;
//!   r:=s; prev_w:=w;
//!   end
//!
//! @ @<Update the max/min amounts@>=
//! begin if min_n=max_halfword then min_n:=n;
//! max_n:=n;
//! if min_d>info(link(temp_head)) then min_d:=info(link(temp_head));
//! if max_d<info(r) then max_d:=info(r);
//! end
//!
//! @ @<Delete empty rows at the top and/or bottom...@>=
//! if min_n>max_n then @<Delete all the row headers@>
//! else  begin n:=n_min(cur_edges); n_min(cur_edges):=min_n;
//!   while min_n>n do
//!     begin p:=link(cur_edges); link(cur_edges):=link(p);
//!     knil(link(p)):=cur_edges;
//!     free_node(p,row_node_size); incr(n);
//!     end;
//!   n:=n_max(cur_edges); n_max(cur_edges):=max_n;
//!   n_pos(cur_edges):=max_n+1; n_rover(cur_edges):=cur_edges;
//!   while max_n<n do
//!     begin p:=knil(cur_edges); knil(cur_edges):=knil(p);
//!     link(knil(p)):=cur_edges;
//!     free_node(p,row_node_size); decr(n);
//!     end;
//!   m_min(cur_edges):=((ho(min_d)) div 8)-m_offset(cur_edges)+zero_field;
//!   m_max(cur_edges):=((ho(max_d)) div 8)-m_offset(cur_edges)+zero_field;
//!   end
//!
//! @ We get here if the edges have been entirely culled away.
//!
//! @<Delete all the row headers@>=
//! begin p:=link(cur_edges);
//! while p<>cur_edges do
//!   begin q:=link(p); free_node(p,row_node_size); p:=q;
//!   end;
//! init_edges(cur_edges);
//! end
//!
//!
//! @ The last and most difficult routine for transforming an edge structure---and
//! the most interesting one!---is |xy_swap_edges|, which interchanges the
//! r\^^Doles of rows and columns. Its task can be viewed as the job of
//! creating an edge structure that contains only horizontal edges, linked
//! together in columns, given an edge structure that contains only
//! vertical edges linked together in rows; we must do this without changing
//! the implied pixel weights.
//!
//! Given any two adjacent rows of an edge structure, it is not difficult to
//! determine the horizontal edges that lie ``between'' them: We simply look
//! for vertically adjacent pixels that have different weight, and insert
//! a horizontal edge containing the difference in weights. Every horizontal
//! edge determined in this way should be put into an appropriate linked
//! list. Since random access to these linked lists is desirable, we use
//! the |move| array to hold the list heads. If we work through the given
//! edge structure from top to bottom, the constructed lists will not need
//! to be sorted, since they will already be in order.
//!
//! The following algorithm makes use of some ideas suggested by John Hobby.
//! @^Hobby, John Douglas@>
//! It assumes that the edge structure is non-null, i.e., that |link(cur_edges)
//! <>cur_edges|, hence |m_max(cur_edges)>=m_min(cur_edges)|.
//!
//! @p procedure xy_swap_edges; {interchange |x| and |y| in |cur_edges|}
//! label done;
//! var @!m_magic,@!n_magic:integer; {special values that account for offsets}
//! @!p,@!q,@!r,@!s:pointer; {pointers that traverse the given structure}
//! @<Other local variables for |xy_swap_edges|@>@;
//! begin @<Initialize the array of new edge list heads@>;
//! @<Insert blank rows at the top and bottom, and set |p| to the new top row@>;
//! @<Compute the magic offset values@>;
//! repeat q:=knil(p);@+if unsorted(q)>void then sort_edges(q);
//! @<Insert the horizontal edges defined by adjacent rows |p,q|,
//!   and destroy row~|p|@>;
//! p:=q; n_magic:=n_magic-8;
//! until knil(p)=cur_edges;
//! free_node(p,row_node_size); {now all original rows have been recycled}
//! @<Adjust the header to reflect the new edges@>;
//! end;
//!
//! @ Here we don't bother to keep the |link| entries up to date, since the
//! procedure looks only at the |knil| fields as it destroys the former
//! edge structure.
//!
//! @<Insert blank rows at the top and bottom...@>=
//! p:=get_node(row_node_size); sorted(p):=sentinel; unsorted(p):=null;@/
//! knil(p):=cur_edges; knil(link(cur_edges)):=p; {the new bottom row}
//! p:=get_node(row_node_size); sorted(p):=sentinel;
//! knil(p):=knil(cur_edges); {the new top row}
//!
//! @ The new lists will become |sorted| lists later, so we initialize
//! empty lists to |sentinel|.
//!
//! @<Initialize the array of new edge list heads@>=
//! m_spread:=m_max(cur_edges)-m_min(cur_edges); {this is |>=0| by assumption}
//! if m_spread>move_size then overflow("move table size",move_size);
//! @:METAFONT capacity exceeded move table size}{\quad move table size@>
//! for j:=0 to m_spread do move[j]:=sentinel
//!
//! @ @<Other local variables for |xy_swap_edges|@>=
//! @!m_spread:integer; {the difference between |m_max| and |m_min|}
//! @!j,@!jj:0..move_size; {indices into |move|}
//! @!m,@!mm:integer; {|m| values at vertical edges}
//! @!pd,@!rd:integer; {data fields from edge-and-weight nodes}
//! @!pm,@!rm:integer; {|m| values from edge-and-weight nodes}
//! @!w:integer; {the difference in accumulated weight}
//! @!ww:integer; {as much of |w| that can be stored in a single node}
//! @!dw:integer; {an increment to be added to |w|}
//!
//! @ At the point where we test |w<>0|, variable |w| contains
//! the accumulated weight from edges already passed in
//! row~|p| minus the accumulated weight from edges already passed in row~|q|.
//!
//! @<Insert the horizontal edges defined by adjacent rows |p,q|...@>=
//! r:=sorted(p); free_node(p,row_node_size); p:=r;@/
//! pd:=ho(info(p)); pm:=pd div 8;@/
//! r:=sorted(q); rd:=ho(info(r)); rm:=rd div 8; w:=0;
//! loop@+  begin if pm<rm then mm:=pm@+else mm:=rm;
//!   if w<>0 then
//!     @<Insert horizontal edges of weight |w| between |m| and~|mm|@>;
//!   if pd<rd then
//!     begin dw:=(pd mod 8)-zero_w;
//!     @<Advance pointer |p| to the next vertical edge,
//!       after destroying the previous one@>;
//!     end
//!   else  begin if r=sentinel then goto done; {|rd=pd=ho(max_halfword)|}
//!     dw:=-((rd mod 8)-zero_w);
//!     @<Advance pointer |r| to the next vertical edge@>;
//!     end;
//!   m:=mm; w:=w+dw;
//!   end;
//! done:
//!
//! @ @<Advance pointer |r| to the next vertical edge@>=
//! r:=link(r); rd:=ho(info(r)); rm:=rd div 8
//!
//! @ @<Advance pointer |p| to the next vertical edge...@>=
//! s:=link(p); free_avail(p); p:=s; pd:=ho(info(p)); pm:=pd div 8
//!
//! @ Certain ``magic'' values are needed to make the following code work,
//! because of the various offsets in our data structure. For now, let's not
//! worry about their precise values; we shall compute |m_magic| and |n_magic|
//! later, after we see what the code looks like.
//!
//! @ @<Insert horizontal edges of weight |w| between |m| and~|mm|@>=
//! if m<>mm then
//!   begin if mm-m_magic>=move_size then confusion("xy");
//! @:this can't happen xy}{\quad xy@>
//!   extras:=(abs(w)-1) div 3;
//!   if extras>0 then
//!     begin if w>0 then xw:=+3@+else xw:=-3;
//!     ww:=w-extras*xw;
//!     end
//!   else ww:=w;
//!   repeat j:=m-m_magic;
//!   for k:=1 to extras do
//!     begin s:=get_avail; info(s):=n_magic+xw;
//!     link(s):=move[j]; move[j]:=s;
//!     end;
//!   s:=get_avail; info(s):=n_magic+ww;
//!   link(s):=move[j]; move[j]:=s;@/
//!   incr(m);
//!   until m=mm;
//!   end
//!
//! @ @<Other local variables for |xy...@>=
//! @!extras:integer; {the number of additional nodes to make weights |>3|}
//! @!xw:-3..3; {the additional weight in extra nodes}
//! @!k:integer; {loop counter for inserting extra nodes}
//!
//! @ At the beginning of this step, |move[m_spread]=sentinel|, because no
//! horizontal edges will extend to the right of column |m_max(cur_edges)|.
//!
//! @<Adjust the header to reflect the new edges@>=
//! move[m_spread]:=0; j:=0;
//! while move[j]=sentinel do incr(j);
//! if j=m_spread then init_edges(cur_edges) {all edge weights are zero}
//! else  begin mm:=m_min(cur_edges);
//!   m_min(cur_edges):=n_min(cur_edges);
//!   m_max(cur_edges):=n_max(cur_edges)+1;
//!   m_offset(cur_edges):=zero_field;
//!   jj:=m_spread-1;
//!   while move[jj]=sentinel do decr(jj);
//!   n_min(cur_edges):=j+mm; n_max(cur_edges):=jj+mm; q:=cur_edges;
//!   repeat p:=get_node(row_node_size); link(q):=p; knil(p):=q;
//!   sorted(p):=move[j]; unsorted(p):=null; incr(j); q:=p;
//!   until j>jj;
//!   link(q):=cur_edges; knil(cur_edges):=q;
//!   n_pos(cur_edges):=n_max(cur_edges)+1; n_rover(cur_edges):=cur_edges;
//!   last_window_time(cur_edges):=0;
//!   end;
//!
//! @ The values of |m_magic| and |n_magic| can be worked out by trying the
//! code above on a small example; if they work correctly in simple cases,
//! they should work in general.
//!
//! @<Compute the magic offset values@>=
//! m_magic:=m_min(cur_edges)+m_offset(cur_edges)-zero_field;
//! n_magic:=8*n_max(cur_edges)+8+zero_w+min_halfword
//!
//! @ Now let's look at the subroutine that merges the edges from a given
//! edge structure into |cur_edges|. The given edge structure loses all its
//! edges.
//!
//! @p procedure merge_edges(@!h:pointer);
//! label done;
//! var @!p,@!q,@!r,@!pp,@!qq,@!rr:pointer; {list manipulation registers}
//! @!n:integer; {row number}
//! @!k:halfword; {key register that we compare to |info(q)|}
//! @!delta:integer; {change to the edge/weight data}
//! begin if link(h)<>h then
//!   begin if (m_min(h)<m_min(cur_edges))or(m_max(h)>m_max(cur_edges))or@|
//!     (n_min(h)<n_min(cur_edges))or(n_max(h)>n_max(cur_edges)) then
//!     edge_prep(m_min(h)-zero_field,m_max(h)-zero_field,
//!       n_min(h)-zero_field,n_max(h)-zero_field+1);
//!   if m_offset(h)<>m_offset(cur_edges) then
//!     @<Adjust the data of |h| to account for a difference of offsets@>;
//!   n:=n_min(cur_edges); p:=link(cur_edges); pp:=link(h);
//!   while n<n_min(h) do
//!     begin incr(n); p:=link(p);
//!     end;
//!   repeat @<Merge row |pp| into row |p|@>;
//!   pp:=link(pp); p:=link(p);
//!   until pp=h;
//!   end;
//! end;
//!
//! @ @<Adjust the data of |h| to account for a difference of offsets@>=
//! begin pp:=link(h); delta:=8*(m_offset(cur_edges)-m_offset(h));
//! repeat qq:=sorted(pp);
//! while qq<>sentinel do
//!   begin info(qq):=info(qq)+delta; qq:=link(qq);
//!   end;
//! qq:=unsorted(pp);
//! while qq>void do
//!   begin info(qq):=info(qq)+delta; qq:=link(qq);
//!   end;
//! pp:=link(pp);
//! until pp=h;
//! end
//!
//! @ The |sorted| and |unsorted| lists are merged separately. After this
//! step, row~|pp| will have no edges remaining, since they will all have
//! been merged into row~|p|.
//!
//! @<Merge row |pp|...@>=
//! qq:=unsorted(pp);
//! if qq>void then
//!   if unsorted(p)<=void then unsorted(p):=qq
//!   else  begin while link(qq)>void do qq:=link(qq);
//!     link(qq):=unsorted(p); unsorted(p):=unsorted(pp);
//!     end;
//! unsorted(pp):=null; qq:=sorted(pp);
//! if qq<>sentinel then
//!   begin if unsorted(p)=void then unsorted(p):=null;
//!   sorted(pp):=sentinel; r:=sorted_loc(p); q:=link(r); {|q=sorted(p)|}
//!   if q=sentinel then sorted(p):=qq
//!   else loop@+begin k:=info(qq);
//!     while k>info(q) do
//!       begin r:=q; q:=link(r);
//!       end;
//!     link(r):=qq; rr:=link(qq); link(qq):=q;
//!     if rr=sentinel then goto done;
//!     r:=qq; qq:=rr;
//!     end;
//!   end;
//! done:
//!
//! @ The |total_weight| routine computes the total of all pixel weights
//! in a given edge structure. It's not difficult to prove that this is
//! the sum of $(-w)$ times $x$ taken over all edges,
//! where $w$ and~$x$ are the weight and $x$~coordinates stored in an edge.
//! It's not necessary to worry that this quantity will overflow the
//! size of an |integer| register, because it will be less than~$2^{31}$
//! unless the edge structure has more than 174,762 edges. However, we had
//! better not try to compute it as a |scaled| integer, because a total
//! weight of almost $12\times 2^{12}$ can be produced by only four edges.
//!
//! @p function total_weight(@!h:pointer):integer; {|h| is an edge header}
//! var @!p,@!q:pointer; {variables that traverse the given structure}
//! @!n:integer; {accumulated total so far}
//! @!m:0..65535; {packed $x$ and $w$ values, including offsets}
//! begin n:=0; p:=link(h);
//! while p<>h do
//!   begin q:=sorted(p);
//!   while q<>sentinel do
//!     @<Add the contribution of node |q| to the total weight,
//!       and set |q:=link(q)|@>;
//!   q:=unsorted(p);
//!   while q>void do
//!     @<Add the contribution of node |q| to the total weight,
//!       and set |q:=link(q)|@>;
//!   p:=link(p);
//!   end;
//! total_weight:=n;
//! end;
//!
//! @ It's not necessary to add the offsets to the $x$ coordinates, because
//! an entire edge structure can be shifted without affecting its total weight.
//! Similarly, we don't need to subtract |zero_field|.
//!
//! @<Add the contribution of node |q| to the total weight...@>=
//! begin m:=ho(info(q)); n:=n-((m mod 8)-zero_w)*(m div 8);
//! q:=link(q);
//! end
//!
//! @ So far we've done lots of things to edge structures assuming that
//! edges are actually present, but we haven't seen how edges get created
//! in the first place. Let's turn now to the problem of generating new edges.
//!
//! \MF\ will display new edges as they are being computed, if |tracing_edges|
//! is positive. In order to keep such data reasonably compact, only the
//! points at which the path makes a $90^\circ$ or $180^\circ$ turn are listed.
//!
//! The tracing algorithm must remember some past history in order to suppress
//! unnecessary data. Three variables |trace_x|, |trace_y|, and |trace_yy|
//! provide this history: The last coordinates printed were |(trace_x,trace_y)|,
//! and the previous edge traced ended at |(trace_x,trace_yy)|. Before anything
//! at all has been traced, |trace_x=-4096|.
//!
//! @<Glob...@>=
//! @!trace_x:integer; {$x$~coordinate most recently shown in a trace}
//! @!trace_y:integer; {$y$~coordinate most recently shown in a trace}
//! @!trace_yy:integer; {$y$~coordinate most recently encountered}
//!
//! @ Edge tracing is initiated by the |begin_edge_tracing| routine,
//! continued by the |trace_a_corner| routine, and terminated by the
//! |end_edge_tracing| routine.
//!
//! @p procedure begin_edge_tracing;
//! begin print_diagnostic("Tracing edges","",true);
//! print(" (weight "); print_int(cur_wt); print_char(")"); trace_x:=-4096;
//! end;
//! @#
//! procedure trace_a_corner;
//! begin if file_offset>max_print_line-13 then print_nl("");
//! print_char("("); print_int(trace_x); print_char(","); print_int(trace_yy);
//! print_char(")"); trace_y:=trace_yy;
//! end;
//! @#
//! procedure end_edge_tracing;
//! begin if trace_x=-4096 then print_nl("(No new edges added.)")
//! @.No new edges added@>
//! else  begin trace_a_corner; print_char(".");
//!   end;
//! end_diagnostic(true);
//! end;
//!
//! @ Just after a new edge weight has been put into the |info| field of
//! node~|r|, in row~|n|, the following routine continues an ongoing trace.
//!
//! @p procedure trace_new_edge(@!r:pointer;@!n:integer);
//! var @!d:integer; {temporary data register}
//! @!w:-3..3; {weight associated with an edge transition}
//! @!m,@!n0,@!n1:integer; {column and row numbers}
//! begin d:=ho(info(r)); w:=(d mod 8)-zero_w; m:=(d div 8)-m_offset(cur_edges);
//! if w=cur_wt then
//!   begin n0:=n+1; n1:=n;
//!   end
//! else  begin n0:=n; n1:=n+1;
//!   end; {the edges run from |(m,n0)| to |(m,n1)|}
//! if m<>trace_x then
//!   begin if trace_x=-4096 then
//!     begin print_nl(""); trace_yy:=n0;
//!     end
//!   else if trace_yy<>n0 then print_char("?") {shouldn't happen}
//!   else trace_a_corner;
//!   trace_x:=m; trace_a_corner;
//!   end
//! else  begin if n0<>trace_yy then print_char("!"); {shouldn't happen}
//!   if ((n0<n1)and(trace_y>trace_yy))or((n0>n1)and(trace_y<trace_yy)) then
//!     trace_a_corner;
//!   end;
//! trace_yy:=n1;
//! end;
//!
//! @ One way to put new edge weights into an edge structure is to use the
//! following routine, which simply draws a straight line from |(x0,y0)| to
//! |(x1,y1)|. More precisely, it introduces weights for the edges of the
//! discrete path $\bigl(\lfloor t[x_0,x_1]+{1\over2}+\epsilon\rfloor,
//! \lfloor t[y_0,y_1]+{1\over2}+\epsilon\delta\rfloor\bigr)$,
//! as $t$ varies from 0 to~1, where $\epsilon$ and $\delta$ are extremely small
//! positive numbers.
//!
//! The structure header is assumed to be |cur_edges|; downward edge weights
//! will be |cur_wt|, while upward ones will be |-cur_wt|.
//!
//! Of course, this subroutine will be called only in connection with others
//! that eventually draw a complete cycle, so that the sum of the edge weights
//! in each row will be zero whenever the row is displayed.
//!
//! @p procedure line_edges(@!x0,@!y0,@!x1,@!y1:scaled);
//! label done,done1;
//! var @!m0,@!n0,@!m1,@!n1:integer; {rounded and unscaled coordinates}
//! @!delx,@!dely:scaled; {the coordinate differences of the line}
//! @!yt:scaled; {smallest |y| coordinate that rounds the same as |y0|}
//! @!tx:scaled; {tentative change in |x|}
//! @!p,@!r:pointer; {list manipulation registers}
//! @!base:integer; {amount added to edge-and-weight data}
//! @!n:integer; {current row number}
//! begin n0:=round_unscaled(y0);
//! n1:=round_unscaled(y1);
//! if n0<>n1 then
//!   begin m0:=round_unscaled(x0); m1:=round_unscaled(x1);
//!   delx:=x1-x0; dely:=y1-y0;
//!   yt:=n0*unity-half_unit; y0:=y0-yt; y1:=y1-yt;
//!   if n0<n1 then @<Insert upward edges for a line@>
//!   else @<Insert downward edges for a line@>;
//!   n_rover(cur_edges):=p; n_pos(cur_edges):=n+zero_field;
//!   end;
//! end;
//!
//! @ Here we are careful to cancel any effect of rounding error.
//!
//! @<Insert upward edges for a line@>=
//! begin base:=8*m_offset(cur_edges)+min_halfword+zero_w-cur_wt;
//! if m0<=m1 then edge_prep(m0,m1,n0,n1)@+else edge_prep(m1,m0,n0,n1);
//! @<Move to row |n0|, pointed to by |p|@>;
//! y0:=unity-y0;
//! loop@+  begin r:=get_avail; link(r):=unsorted(p); unsorted(p):=r;@/
//!   tx:=take_fraction(delx,make_fraction(y0,dely));
//!   if ab_vs_cd(delx,y0,dely,tx)<0 then decr(tx);
//!     {now $|tx|=\lfloor|y0|\cdot|delx|/|dely|\rfloor$}
//!   info(r):=8*round_unscaled(x0+tx)+base;@/
//!   y1:=y1-unity;
//!   if internal[tracing_edges]>0 then trace_new_edge(r,n);
//!   if y1<unity then goto done;
//!   p:=link(p); y0:=y0+unity; incr(n);
//!   end;
//! done: end
//!
//! @ @<Insert downward edges for a line@>=
//! begin base:=8*m_offset(cur_edges)+min_halfword+zero_w+cur_wt;
//! if m0<=m1 then edge_prep(m0,m1,n1,n0)@+else edge_prep(m1,m0,n1,n0);
//! decr(n0); @<Move to row |n0|, pointed to by |p|@>;
//! loop@+  begin r:=get_avail; link(r):=unsorted(p); unsorted(p):=r;@/
//!   tx:=take_fraction(delx,make_fraction(y0,dely));
//!   if ab_vs_cd(delx,y0,dely,tx)<0 then incr(tx);
//!     {now $|tx|=\lceil|y0|\cdot|delx|/|dely|\rceil$, since |dely<0|}
//!   info(r):=8*round_unscaled(x0-tx)+base;@/
//!   y1:=y1+unity;
//!   if internal[tracing_edges]>0 then trace_new_edge(r,n);
//!   if y1>=0 then goto done1;
//!   p:=knil(p); y0:=y0+unity; decr(n);
//!   end;
//! done1: end
//!
//! @ @<Move to row |n0|, pointed to by |p|@>=
//! n:=n_pos(cur_edges)-zero_field; p:=n_rover(cur_edges);
//! if n<>n0 then
//!   if n<n0 then
//!     repeat incr(n); p:=link(p);
//!     until n=n0
//!   else  repeat decr(n); p:=knil(p);
//!     until n=n0
//!
//! @ \MF\ inserts most of its edges into edge structures via the
//! |move_to_edges| subroutine, which uses the data stored in the |move| array
//! to specify a sequence of ``rook moves.'' The starting point |(m0,n0)|
//! and finishing point |(m1,n1)| of these moves, as seen from the standpoint
//! of the first octant, are supplied as parameters; the moves should, however,
//! be rotated into a given octant.  (We're going to study octant
//! transformations in great detail later; the reader may wish to come back to
//! this part of the program after mastering the mysteries of octants.)
//!
//! The rook moves themselves are defined as follows, from a |first_octant|
//! point of view: ``Go right |move[k]| steps, then go up one, for |0<=k<n1-n0|;
//! then go right |move[n1-n0]| steps and stop.'' The sum of |move[k]|
//! for |0<=k<=n1-n0| will be equal to |m1-m0|.
//!
//! As in the |line_edges| routine, we use |+cur_wt| as the weight of
//! all downward edges and |-cur_wt| as the weight of all upward edges,
//! after the moves have been rotated to the proper octant direction.
//!
//! There are two main cases to consider: \\{fast\_case} is for moves that
//! travel in the direction of octants 1, 4, 5, and~8, while \\{slow\_case}
//! is for moves that travel toward octants 2, 3, 6, and~7. The latter directions
//! are comparatively cumbersome because they generate more upward or downward
//! edges; a curve that travels horizontally doesn't produce any edges at all,
//! but a curve that travels vertically touches lots of rows.
//!
//! @d fast_case_up=60 {for octants 1 and 4}
//! @d fast_case_down=61 {for octants 5 and 8}
//! @d slow_case_up=62 {for octants 2 and 3}
//! @d slow_case_down=63 {for octants 6 and 7}
//!
//! @p procedure move_to_edges(@!m0,@!n0,@!m1,@!n1:integer);
//! label fast_case_up,fast_case_down,slow_case_up,slow_case_down,done;
//! var @!delta:0..move_size; {extent of |move| data}
//! @!k:0..move_size; {index into |move|}
//! @!p,@!r:pointer; {list manipulation registers}
//! @!dx:integer; {change in edge-weight |info| when |x| changes by 1}
//! @!edge_and_weight:integer; {|info| to insert}
//! @!j:integer; {number of consecutive vertical moves}
//! @!n:integer; {the current row pointed to by |p|}
//! debug @!sum:integer;@+gubed@;@/
//! begin delta:=n1-n0;
//! debug sum:=move[0]; for k:=1 to delta do sum:=sum+abs(move[k]);
//! if sum<>m1-m0 then confusion("0");@+gubed@;@/
//! @:this can't happen 0}{\quad 0@>
//! @<Prepare for and switch to the appropriate case, based on |octant|@>;
//! fast_case_up:@<Add edges for first or fourth octants, then |goto done|@>;
//! fast_case_down:@<Add edges for fifth or eighth octants, then |goto done|@>;
//! slow_case_up:@<Add edges for second or third octants, then |goto done|@>;
//! slow_case_down:@<Add edges for sixth or seventh octants, then |goto done|@>;
//! done: n_pos(cur_edges):=n+zero_field; n_rover(cur_edges):=p;
//! end;
//!
//! @ The current octant code appears in a global variable. If, for example,
//! we have |octant=third_octant|, it means that a curve traveling in a north to
//! north-westerly direction has been rotated for the purposes of internal
//! calculations so that the |move| data travels in an east to north-easterly
//! direction. We want to unrotate as we update the edge structure.
//!
//! @<Glob...@>=
//! @!octant:first_octant..sixth_octant; {the current octant of interest}
//!
//! @ @<Prepare for and switch to the appropriate case, based on |octant|@>=
//! case octant of
//! first_octant:begin dx:=8; edge_prep(m0,m1,n0,n1); goto fast_case_up;
//!   end;
//! second_octant:begin dx:=8; edge_prep(n0,n1,m0,m1); goto slow_case_up;
//!   end;
//! third_octant:begin dx:=-8; edge_prep(-n1,-n0,m0,m1); negate(n0);
//!   goto slow_case_up;
//!   end;
//! fourth_octant:begin dx:=-8; edge_prep(-m1,-m0,n0,n1); negate(m0);
//!   goto fast_case_up;
//!   end;
//! fifth_octant:begin dx:=-8; edge_prep(-m1,-m0,-n1,-n0); negate(m0);
//!   goto fast_case_down;
//!   end;
//! sixth_octant:begin dx:=-8; edge_prep(-n1,-n0,-m1,-m0); negate(n0);
//!   goto slow_case_down;
//!   end;
//! seventh_octant:begin dx:=8; edge_prep(n0,n1,-m1,-m0); goto slow_case_down;
//!   end;
//! eighth_octant:begin dx:=8; edge_prep(m0,m1,-n1,-n0); goto fast_case_down;
//!   end;
//! end; {there are only eight octants}
//!
//! @ @<Add edges for first or fourth octants, then |goto done|@>=
//! @<Move to row |n0|, pointed to by |p|@>;
//! if delta>0 then
//!   begin k:=0;
//!   edge_and_weight:=8*(m0+m_offset(cur_edges))+min_halfword+zero_w-cur_wt;
//!   repeat edge_and_weight:=edge_and_weight+dx*move[k];
//!   fast_get_avail(r); link(r):=unsorted(p); info(r):=edge_and_weight;
//!   if internal[tracing_edges]>0 then trace_new_edge(r,n);
//!   unsorted(p):=r; p:=link(p); incr(k); incr(n);
//!   until k=delta;
//!   end;
//! goto done
//!
//! @ @<Add edges for fifth or eighth octants, then |goto done|@>=
//! n0:=-n0-1; @<Move to row |n0|, pointed to by |p|@>;
//! if delta>0 then
//!   begin k:=0;
//!   edge_and_weight:=8*(m0+m_offset(cur_edges))+min_halfword+zero_w+cur_wt;
//!   repeat edge_and_weight:=edge_and_weight+dx*move[k];
//!   fast_get_avail(r); link(r):=unsorted(p); info(r):=edge_and_weight;
//!   if internal[tracing_edges]>0 then trace_new_edge(r,n);
//!   unsorted(p):=r; p:=knil(p); incr(k); decr(n);
//!   until k=delta;
//!   end;
//! goto done
//!
//! @ @<Add edges for second or third octants, then |goto done|@>=
//! edge_and_weight:=8*(n0+m_offset(cur_edges))+min_halfword+zero_w-cur_wt;
//! n0:=m0; k:=0; @<Move to row |n0|, pointed to by |p|@>;
//! repeat j:=move[k];
//! while j>0 do
//!   begin fast_get_avail(r); link(r):=unsorted(p); info(r):=edge_and_weight;
//!   if internal[tracing_edges]>0 then trace_new_edge(r,n);
//!   unsorted(p):=r; p:=link(p); decr(j); incr(n);
//!   end;
//! edge_and_weight:=edge_and_weight+dx; incr(k);
//! until k>delta;
//! goto done
//!
//! @ @<Add edges for sixth or seventh octants, then |goto done|@>=
//! edge_and_weight:=8*(n0+m_offset(cur_edges))+min_halfword+zero_w+cur_wt;
//! n0:=-m0-1; k:=0; @<Move to row |n0|, pointed to by |p|@>;
//! repeat j:=move[k];
//! while j>0 do
//!   begin fast_get_avail(r); link(r):=unsorted(p); info(r):=edge_and_weight;
//!   if internal[tracing_edges]>0 then trace_new_edge(r,n);
//!   unsorted(p):=r; p:=knil(p); decr(j); decr(n);
//!   end;
//! edge_and_weight:=edge_and_weight+dx; incr(k);
//! until k>delta;
//! goto done
//!
//! @ All the hard work of building an edge structure is undone by the following
//! subroutine.
//!
//! @<Declare the recycling subroutines@>=
//! procedure toss_edges(@!h:pointer);
//! var @!p,@!q:pointer; {for list manipulation}
//! begin q:=link(h);
//! while q<>h do
//!   begin flush_list(sorted(q));
//!   if unsorted(q)>void then flush_list(unsorted(q));
//!   p:=q; q:=link(q); free_node(p,row_node_size);
//!   end;
//! free_node(h,edge_header_size);
//! end;
//!
//! @* \[21] Subdivision into octants.
//! When \MF\ digitizes a path, it reduces the problem to the special
//! case of paths that travel in ``first octant'' directions; i.e.,
//! each cubic $z(t)=\bigl(x(t),y(t)\bigr)$ being digitized will have the property
//! that $0\L y'(t)\L x'(t)$. This assumption makes digitizing simpler
//! and faster than if the direction of motion has to be tested repeatedly.
//!
//! When $z(t)$ is cubic, $x'(t)$ and $y'(t)$ are quadratic, hence the four
//! polynomials $x'(t)$, $y'(t)$, $x'(t)-y'(t)$, and $x'(t)+y'(t)$ cross
//! through~0 at most twice each. If we subdivide the given cubic at these
//! places, we get at most nine subintervals in each of which
//! $x'(t)$, $y'(t)$, $x'(t)-y'(t)$, and $x'(t)+y'(t)$ all have a constant
//! sign. The curve can be transformed in each of these subintervals so that
//! it travels entirely in first octant directions, if we reflect $x\swap-x$,
//! $y\swap-y$, and/or $x\swap y$ as necessary. (Incidentally, it can be
//! shown that a cubic such that $x'(t)=16(2t-1)^2+2(2t-1)-1$ and
//! $y'(t)=8(2t-1)^2+4(2t-1)$ does indeed split into nine subintervals.)
//!
//! @ The transformation that rotates coordinates, so that first octant motion
//! can be assumed, is defined by the |skew| subroutine, which sets global
//! variables |cur_x| and |cur_y| to the values that are appropriate in a
//! given octant.  (Octants are encoded as they were in the |n_arg| subroutine.)
//!
//! This transformation is ``skewed'' by replacing |(x,y)| by |(x-y,y)|,
//! once first octant motion has been established. It turns out that
//! skewed coordinates are somewhat better to work with when curves are
//! actually digitized.
//!
//! @d set_two_end(#)==cur_y:=#;@+end
//! @d set_two(#)==begin cur_x:=#; set_two_end
//!
//! @p procedure skew(@!x,@!y:scaled;@!octant:small_number);
//! begin case octant of
//! first_octant: set_two(x-y)(y);
//! second_octant: set_two(y-x)(x);
//! third_octant: set_two(y+x)(-x);
//! fourth_octant: set_two(-x-y)(y);
//! fifth_octant: set_two(-x+y)(-y);
//! sixth_octant: set_two(-y+x)(-x);
//! seventh_octant: set_two(-y-x)(x);
//! eighth_octant: set_two(x+y)(-y);
//! end; {there are no other cases}
//! end;
//!
//! @ Conversely, the following subroutine sets |cur_x| and
//! |cur_y| to the original coordinate values of a point, given an octant
//! code and the point's coordinates |(x,y)| after they have been mapped into
//! the first octant and skewed.
//!
//! @<Declare subroutines for printing expressions@>=
//! procedure unskew(@!x,@!y:scaled;@!octant:small_number);
//! begin case octant of
//! first_octant: set_two(x+y)(y);
//! second_octant: set_two(y)(x+y);
//! third_octant: set_two(-y)(x+y);
//! fourth_octant: set_two(-x-y)(y);
//! fifth_octant: set_two(-x-y)(-y);
//! sixth_octant: set_two(-y)(-x-y);
//! seventh_octant: set_two(y)(-x-y);
//! eighth_octant: set_two(x+y)(-y);
//! end; {there are no other cases}
//! end;
//!
//! @ @<Glob...@>=
//! @!cur_x,@!cur_y:scaled;
//!   {outputs of |skew|, |unskew|, and a few other routines}
//!
//! @ The conversion to skewed and rotated coordinates takes place in
//! stages, and at one point in the transformation we will have negated the
//! $x$ and/or $y$ coordinates so as to make curves travel in the first
//! {\sl quadrant}. At this point the relevant ``octant'' code will be
//! either |first_octant| (when no transformation has been done),
//! or |fourth_octant=first_octant+negate_x| (when $x$ has been negated),
//! or |fifth_octant=first_octant+negate_x+negate_y| (when both have been
//! negated), or |eighth_octant=first_octant+negate_y| (when $y$ has been
//! negated). The |abnegate| routine is sometimes needed to convert
//! from one of these transformations to another.
//!
//! @p procedure abnegate(@!x,@!y:scaled;
//!   @!octant_before,@!octant_after:small_number);
//! begin if odd(octant_before)=odd(octant_after) then cur_x:=x
//!   else cur_x:=-x;
//! if (octant_before>negate_y)=(octant_after>negate_y) then cur_y:=y
//!   else cur_y:=-y;
//! end;
//!
//! @ Now here's a subroutine that's handy for subdivision: Given a
//! quadratic polynomial $B(a,b,c;t)$, the |crossing_point| function
//! returns the unique |fraction| value |t| between 0 and~1 at which
//! $B(a,b,c;t)$ changes from positive to negative, or returns
//! |t=fraction_one+1| if no such value exists. If |a<0| (so that $B(a,b,c;t)$
//! is already negative at |t=0|), |crossing_point| returns the value zero.
//!
//! @d no_crossing==begin crossing_point:=fraction_one+1; return;
//!   end
//! @d one_crossing==begin crossing_point:=fraction_one; return;
//!   end
//! @d zero_crossing==begin crossing_point:=0; return;
//!   end
//!
//! @p function crossing_point(@!a,@!b,@!c:integer):fraction;
//! label exit;
//! var @!d:integer; {recursive counter}
//! @!x,@!xx,@!x0,@!x1,@!x2:integer; {temporary registers for bisection}
//! begin if a<0 then zero_crossing;
//! if c>=0 then
//!   begin if b>=0 then
//!     if c>0 then no_crossing
//!     else if (a=0)and(b=0) then no_crossing
//!     else one_crossing;
//!   if a=0 then zero_crossing;
//!   end
//! else if a=0 then if b<=0 then zero_crossing;
//! @<Use bisection to find the crossing point, if one exists@>;
//! exit:end;
//!
//! @ The general bisection method is quite simple when $n=2$, hence
//! |crossing_point| does not take much time. At each stage in the
//! recursion we have a subinterval defined by |l| and~|j| such that
//! $B(a,b,c;2^{-l}(j+t))=B(x_0,x_1,x_2;t)$, and we want to ``zero in'' on
//! the subinterval where $x_0\G0$ and $\min(x_1,x_2)<0$.
//!
//! It is convenient for purposes of calculation to combine the values
//! of |l| and~|j| in a single variable $d=2^l+j$, because the operation
//! of bisection then corresponds simply to doubling $d$ and possibly
//! adding~1. Furthermore it proves to be convenient to modify
//! our previous conventions for bisection slightly, maintaining the
//! variables $X_0=2^lx_0$, $X_1=2^l(x_0-x_1)$, and $X_2=2^l(x_1-x_2)$.
//! With these variables the conditions $x_0\ge0$ and $\min(x_1,x_2)<0$ are
//! equivalent to $\max(X_1,X_1+X_2)>X_0\ge0$.
//!
//! The following code maintains the invariant relations
//! $0\L|x0|<\max(|x1|,|x1|+|x2|)$,
//! $\vert|x1|\vert<2^{30}$, $\vert|x2|\vert<2^{30}$;
//! it has been constructed in such a way that no arithmetic overflow
//! will occur if the inputs satisfy
//! $a<2^{30}$, $\vert a-b\vert<2^{30}$, and $\vert b-c\vert<2^{30}$.
//!
//! @<Use bisection to find the crossing point...@>=
//! d:=1; x0:=a; x1:=a-b; x2:=b-c;
//! repeat x:=half(x1+x2);
//! if x1-x0>x0 then
//!   begin x2:=x; double(x0); double(d);
//!   end
//! else  begin xx:=x1+x-x0;
//!   if xx>x0 then
//!     begin x2:=x; double(x0); double(d);
//!     end
//!   else  begin x0:=x0-xx;
//!     if x<=x0 then if x+x2<=x0 then no_crossing;
//!     x1:=x; d:=d+d+1;
//!     end;
//!   end;
//! until d>=fraction_one;
//! crossing_point:=d-fraction_one
//!
//! @ Octant subdivision is applied only to cycles, i.e., to closed paths.
//! A ``cycle spec'' is a data structure that contains specifications of
//! @!@^cycle spec@>
//! cubic curves and octant mappings for the cycle that has been subdivided
//! into segments belonging to single octants. It is composed entirely of
//! knot nodes, similar to those in the representation of paths; but the
//! |explicit| type indications have been replaced by positive numbers
//! that give further information. Additional |endpoint| data is also
//! inserted at the octant boundaries.
//!
//! Recall that a cubic polynomial is represented by four control points
//! that appear in adjacent nodes |p| and~|q| of a knot list. The |x|~coordinates
//! are |x_coord(p)|, |right_x(p)|, |left_x(q)|, and |x_coord(q)|; the
//! |y|~coordinates are similar. We shall call this ``the cubic following~|p|''
//! or ``the cubic between |p| and~|q|'' or ``the cubic preceding~|q|.''
//!
//! Cycle specs are circular lists of cubic curves mixed with octant
//! boundaries. Like cubics, the octant boundaries are represented in
//! consecutive knot nodes |p| and~|q|. In such cases |right_type(p)=
//! left_type(q)=endpoint|, and the fields |right_x(p)|, |right_y(p)|,
//! |left_x(q)|, and |left_y(q)| are replaced by other fields called
//! |right_octant(p)|, |right_transition(p)|, |left_octant(q)|, and
//! |left_transition(q)|, respectively. For example, when the curve direction
//! moves from the third octant to the fourth octant, the boundary nodes say
//! |right_octant(p)=third_octant|, |left_octant(q)=fourth_octant|,
//! and |right_transition(p)=left_transition(q)=diagonal|. A |diagonal|
//! transition occurs when moving between octants 1~\AM~2, 3~\AM~4, 5~\AM~6, or
//! 7~\AM~8; an |axis| transition occurs when moving between octants 8~\AM~1,
//! 2~\AM~3, 4~\AM~5, 6~\AM~7. (Such transition information is redundant
//! but convenient.) Fields |x_coord(p)| and |y_coord(p)| will contain
//! coordinates of the transition point after rotation from third octant
//! to first octant; i.e., if the true coordinates are $(x,y)$, the
//! coordinates $(y,-x)$ will appear in node~|p|. Similarly, a fourth-octant
//! transformation will have been applied after the transition, so
//! we will have |x_coord(q)=@t$-x$@>| and |y_coord(q)=y|.
//!
//! The cubic between |p| and |q| will contain positive numbers in the
//! fields |right_type(p)| and |left_type(q)|; this makes cubics
//! distinguishable from octant boundaries, because |endpoint=0|.
//! The value of |right_type(p)| will be the current octant code,
//! during the time that cycle specs are being constructed; it will
//! refer later to a pen offset position, if the envelope of a cycle is
//! being computed. A cubic that comes from some subinterval of the $k$th
//! step in the original cyclic path will have |left_type(q)=k|.
//!
//! @d right_octant==right_x {the octant code before a transition}
//! @d left_octant==left_x {the octant after a transition}
//! @d right_transition==right_y {the type of transition}
//! @d left_transition==left_y {ditto, either |axis| or |diagonal|}
//! @d axis=0 {a transition across the $x'$- or $y'$-axis}
//! @d diagonal=1 {a transition where $y'=\pm x'$}
//!
//! @ Here's a routine that prints a cycle spec in symbolic form, so that it
//! is possible to see what subdivision has been made.  The point coordinates
//! are converted back from \MF's internal ``rotated'' form to the external
//! ``true'' form. The global variable~|cur_spec| should point to a knot just
//! after the beginning of an octant boundary, i.e., such that
//! |left_type(cur_spec)=endpoint|.
//!
//! @d print_two_true(#)==unskew(#,octant); print_two(cur_x,cur_y)
//!
//! @p procedure print_spec(@!s:str_number);
//! label not_found,done;
//! var @!p,@!q:pointer; {for list traversal}
//! @!octant:small_number; {the current octant code}
//! begin print_diagnostic("Cycle spec",s,true);
//! @.Cycle spec at line...@>
//! p:=cur_spec; octant:=left_octant(p); print_ln;
//! print_two_true(x_coord(cur_spec),y_coord(cur_spec));
//! print(" % beginning in octant `");
//! loop@+  begin print(octant_dir[octant]); print_char("'");
//!   loop@+  begin q:=link(p);
//!     if right_type(p)=endpoint then goto not_found;
//!     @<Print the cubic between |p| and |q|@>;
//!     p:=q;
//!     end;
//! not_found: if q=cur_spec then goto done;
//!   p:=q; octant:=left_octant(p); print_nl("% entering octant `");
//!   end;
//! @.entering the nth octant@>
//! done: print_nl(" & cycle"); end_diagnostic(true);
//! end;
//!
//! @ Symbolic octant direction names are kept in the |octant_dir| array.
//!
//! @<Glob...@>=
//! @!octant_dir:array[first_octant..sixth_octant] of str_number;
//!
//! @ @<Set init...@>=
//! octant_dir[first_octant]:="ENE";
//! octant_dir[second_octant]:="NNE";
//! octant_dir[third_octant]:="NNW";
//! octant_dir[fourth_octant]:="WNW";
//! octant_dir[fifth_octant]:="WSW";
//! octant_dir[sixth_octant]:="SSW";
//! octant_dir[seventh_octant]:="SSE";
//! octant_dir[eighth_octant]:="ESE";
//!
//! @ @<Print the cubic between...@>=
//! begin print_nl("   ..controls ");
//! print_two_true(right_x(p),right_y(p));
//! print(" and ");
//! print_two_true(left_x(q),left_y(q));
//! print_nl(" ..");
//! print_two_true(x_coord(q),y_coord(q));
//! print(" % segment "); print_int(left_type(q)-1);
//! end
//!
//! @ A much more compact version of a spec is printed to help users identify
//! ``strange paths.''
//!
//! @p procedure print_strange(@!s:str_number);
//! var @!p:pointer; {for list traversal}
//! @!f:pointer; {starting point in the cycle}
//! @!q:pointer; {octant boundary to be printed}
//! @!t:integer; {segment number, plus 1}
//! begin if interaction=error_stop_mode then wake_up_terminal;
//! print_nl(">");
//! @.>\relax@>
//! @<Find the starting point, |f|@>;
//! @<Determine the octant boundary |q| that precedes |f|@>;
//! t:=0;
//! repeat if left_type(p)<>endpoint then
//!   begin if left_type(p)<>t then
//!     begin t:=left_type(p); print_char(" "); print_int(t-1);
//!     end;
//!   if q<>null then
//!     begin @<Print the turns, if any, that start at |q|, and advance |q|@>;
//!     print_char(" "); print(octant_dir[left_octant(q)]); q:=null;
//!     end;
//!   end
//! else if q=null then q:=p;
//! p:=link(p);
//! until p=f;
//! print_char(" "); print_int(left_type(p)-1);
//! if q<>null then @<Print the turns...@>;
//! print_err(s);
//! end;
//!
//! @ If the segment numbers on the cycle are $t_1$, $t_2$, \dots, $t_m$,
//! and if |m<=max_quarterword|,
//! we have $t_{k-1}\L t_k$ except for at most one value of~$k$. If there are
//! no exceptions, $f$ will point to $t_1$; otherwise it will point to the
//! exceptional~$t_k$.
//!
//! There is at least one segment number (i.e., we always have $m>0$), because
//! |print_strange| is never called upon to display an entirely ``dead'' cycle.
//!
//! @<Find the starting point, |f|@>=
//! p:=cur_spec; t:=max_quarterword+1;
//! repeat p:=link(p);
//! if left_type(p)<>endpoint then
//!   begin if left_type(p)<t then f:=p;
//!   t:=left_type(p);
//!   end;
//! until p=cur_spec
//!
//! @ @<Determine the octant boundary...@>=
//! p:=cur_spec; q:=p;
//! repeat p:=link(p);
//! if left_type(p)=endpoint then q:=p;
//! until p=f
//!
//! @ When two octant boundaries are adjacent, the path is simply changing direction
//! without moving. Such octant directions are shown in parentheses.
//!
//! @<Print the turns...@>=
//! if left_type(link(q))=endpoint then
//!   begin print(" ("); print(octant_dir[left_octant(q)]); q:=link(q);
//!   while left_type(link(q))=endpoint do
//!     begin print_char(" "); print(octant_dir[left_octant(q)]); q:=link(q);
//!     end;
//!   print_char(")");
//!   end
//!
//! @ The |make_spec| routine is what subdivides paths into octants:
//! Given a pointer |cur_spec| to a cyclic path, |make_spec| mungs the path data
//! and returns a pointer to the corresponding cyclic spec.
//! All ``dead'' cubics (i.e., cubics that don't move at all from
//! their starting points) will have been removed from the result.
//! @!@^dead cubics@>
//!
//! The idea of |make_spec| is fairly simple: Each cubic is first
//! subdivided, if necessary, into pieces belonging to single octants;
//! then the octant boundaries are inserted. But some of the details of
//! this transformation are not quite obvious.
//!
//! If |autorounding>0|, the path will be adjusted so that critical tangent
//! directions occur at ``good'' points with respect to the pen called |cur_pen|.
//!
//! The resulting spec will have all |x| and |y| coordinates at most
//! $2^{28}-|half_unit|-1-|safety_margin|$ in absolute value.  The pointer
//! that is returned will start some octant, as required by |print_spec|.
//!
//! @p @t\4@>@<Declare subroutines needed by |make_spec|@>@;
//! function make_spec(@!h:pointer;
//!   @!safety_margin:scaled;@!tracing:integer):pointer;
//!   {converts a path to a cycle spec}
//! label continue,done;
//! var @!p,@!q,@!r,@!s:pointer; {for traversing the lists}
//! @!k:integer; {serial number of path segment, or octant code}
//! @!chopped:integer; {positive if data truncated,
//!           negative if data dangerously large}
//! @<Other local variables for |make_spec|@>@;
//! begin cur_spec:=h;
//! if tracing>0 then
//!   print_path(cur_spec,", before subdivision into octants",true);
//! max_allowed:=fraction_one-half_unit-1-safety_margin;
//! @<Truncate the values of all coordinates that exceed |max_allowed|, and stamp
//!   segment numbers in each |left_type| field@>;
//! quadrant_subdivide; {subdivide each cubic into pieces belonging to quadrants}
//! if (internal[autorounding]>0)and(chopped=0) then xy_round;
//! octant_subdivide; {complete the subdivision}
//! if (internal[autorounding]>unity)and(chopped=0) then diag_round;
//! @<Remove dead cubics@>;
//! @<Insert octant boundaries and compute the turning number@>;
//! while left_type(cur_spec)<>endpoint do cur_spec:=link(cur_spec);
//! if tracing>0 then
//!   if (internal[autorounding]<=0)or(chopped<>0) then
//!     print_spec(", after subdivision")
//!   else if internal[autorounding]>unity then
//!     print_spec(", after subdivision and double autorounding")
//!   else print_spec(", after subdivision and autorounding");
//! make_spec:=cur_spec;
//! end;
//!
//! @ The |make_spec| routine has an interesting side effect, namely to set
//! the global variable |turning_number| to the number of times the tangent
//! vector of the given cyclic path winds around the origin.
//!
//! Another global variable |cur_spec| points to the specification as it is
//! being made, since several subroutines must go to work on it.
//!
//! And there are two global variables that affect the rounding
//! decisions, as we'll see later; they are called |cur_pen| and |cur_path_type|.
//! The latter will be |double_path_code| if |make_spec| is being
//! applied to a double path.
//!
//! @d double_path_code=0 {command modifier for `\&{doublepath}'}
//! @d contour_code=1 {command modifier for `\&{contour}'}
//! @d also_code=2 {command modifier for `\&{also}'}
//!
//! @<Glob...@>=
//! @!cur_spec:pointer; {the principal output of |make_spec|}
//! @!turning_number:integer; {another output of |make_spec|}
//! @!cur_pen:pointer; {an implicit input of |make_spec|, used in autorounding}
//! @!cur_path_type:double_path_code..contour_code; {likewise}
//! @!max_allowed:scaled; {coordinates must be at most this big}
//!
//! @ First we do a simple preprocessing step. The segment numbers inserted
//! here will propagate to all descendants of cubics that are split into
//! subintervals. These numbers must be nonzero, but otherwise they are
//! present merely for diagnostic purposes. The cubic from |p| to~|q|
//! that represents ``time interval'' |(t-1)..t| usually has |left_type(q)=t|,
//! except when |t| is too large to be stored in a quarterword.
//!
//! @d procrustes(#)==@+if abs(#)>=dmax then
//!   if abs(#)>max_allowed then
//!     begin chopped:=1;
//!     if #>0 then #:=max_allowed@+else #:=-max_allowed;
//!     end
//!   else if chopped=0 then chopped:=-1
//!
//! @<Truncate the values of all coordinates that exceed...@>=
//! p:=cur_spec; k:=1; chopped:=0; dmax:=half(max_allowed);
//! repeat procrustes(left_x(p)); procrustes(left_y(p));
//! procrustes(x_coord(p)); procrustes(y_coord(p));
//! procrustes(right_x(p)); procrustes(right_y(p));@/
//! p:=link(p); left_type(p):=k;
//! if k<max_quarterword then incr(k)@+else k:=1;
//! until p=cur_spec;
//! if chopped>0 then
//!   begin print_err("Curve out of range");
//! @.Curve out of range@>
//!   help4("At least one of the coordinates in the path I'm about to")@/
//!     ("digitize was really huge (potentially bigger than 4095).")@/
//!     ("So I've cut it back to the maximum size.")@/
//!     ("The results will probably be pretty wild.");
//!   put_get_error;
//!   end
//!
//! @ We may need to get rid of constant ``dead'' cubics that clutter up
//! the data structure and interfere with autorounding.
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! procedure remove_cubic(@!p:pointer); {removes the cubic following~|p|}
//! var @!q:pointer; {the node that disappears}
//! begin q:=link(p); right_type(p):=right_type(q); link(p):=link(q);@/
//! x_coord(p):=x_coord(q); y_coord(p):=y_coord(q);@/
//! right_x(p):=right_x(q); right_y(p):=right_y(q);@/
//! free_node(q,knot_node_size);
//! end;
//!
//! @ The subdivision process proceeds by first swapping $x\swap-x$, if
//! necessary, to ensure that $x'\G0$; then swapping $y\swap-y$, if necessary,
//! to ensure that $y'\G0$; and finally swapping $x\swap y$, if necessary,
//! to ensure that $x'\G y'$.
//!
//! Recall that the octant codes have been defined in such a way that, for
//! example, |third_octant=first_octant+negate_x+switch_x_and_y|. The program
//! uses the fact that |negate_x<negate_y<switch_x_and_y| to handle ``double
//! negation'': If |c| is an octant code that possibly involves |negate_x|
//! and/or |negate_y|, but not |switch_x_and_y|, then negating~|y| changes~|c|
//! either to |c+negate_y| or |c-negate_y|, depending on whether
//! |c<=negate_y| or |c>negate_y|. Octant codes are always greater than zero.
//!
//! The first step is to subdivide on |x| and |y| only, so that horizontal
//! and vertical autorounding can be done before we compare $x'$ to $y'$.
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! @t\4@>@<Declare the procedure called |split_cubic|@>@;
//! procedure quadrant_subdivide;
//! label continue,exit;
//! var @!p,@!q,@!r,@!s,@!pp,@!qq:pointer; {for traversing the lists}
//! @!first_x,@!first_y:scaled; {unnegated coordinates of node |cur_spec|}
//! @!del1,@!del2,@!del3,@!del,@!dmax:scaled; {proportional to the control
//!   points of a quadratic derived from a cubic}
//! @!t:fraction; {where a quadratic crosses zero}
//! @!dest_x,@!dest_y:scaled; {final values of |x| and |y| in the current cubic}
//! @!constant_x:boolean; {is |x| constant between |p| and |q|?}
//! begin p:=cur_spec; first_x:=x_coord(cur_spec); first_y:=y_coord(cur_spec);
//! repeat continue: q:=link(p);
//! @<Subdivide the cubic between |p| and |q| so that the results travel
//!   toward the right halfplane@>;
//! @<Subdivide all cubics between |p| and |q| so that the results travel
//!   toward the first quadrant; but |return| or |goto continue| if the
//!   cubic from |p| to |q| was dead@>;
//! p:=q;
//! until p=cur_spec;
//! exit:end;
//!
//! @ All three subdivision processes are similar, so it's possible to
//! get the general idea by studying the first one (which is the simplest).
//! The calculation makes use of the fact that the derivatives of
//! Bernshte{\u\i}n polynomials satisfy
//! $B'(z_0,z_1,\ldots,z_n;t)=nB(z_1-z_0,\ldots,z_n-z_{n-1};t)$.
//!
//! When this routine begins, |right_type(p)| is |explicit|; we should
//! set |right_type(p):=first_octant|. However, no assignment is made,
//! because |explicit=first_octant|. The author apologizes for using
//! such trickery here; it is really hard to do redundant computations
//! just for the sake of purity.
//!
//! @<Subdivide the cubic between |p| and |q| so that the results travel
//!   toward the right halfplane...@>=
//! if q=cur_spec then
//!   begin dest_x:=first_x; dest_y:=first_y;
//!   end
//! else  begin dest_x:=x_coord(q); dest_y:=y_coord(q);
//!   end;
//! del1:=right_x(p)-x_coord(p); del2:=left_x(q)-right_x(p);
//! del3:=dest_x-left_x(q);
//! @<Scale up |del1|, |del2|, and |del3| for greater accuracy;
//!   also set |del| to the first nonzero element of |(del1,del2,del3)|@>;
//! if del=0 then constant_x:=true
//! else  begin constant_x:=false;
//!   if del<0 then @<Complement the |x| coordinates of the
//!     cubic between |p| and~|q|@>;
//!   t:=crossing_point(del1,del2,del3);
//!   if t<fraction_one then
//!     @<Subdivide the cubic with respect to $x'$, possibly twice@>;
//!   end
//!
//! @ If |del1=del2=del3=0|, it's impossible to obey the title of this
//! section. We just set |del=0| in that case.
//! @^inner loop@>
//!
//! @<Scale up |del1|, |del2|, and |del3| for greater accuracy...@>=
//! if del1<>0 then del:=del1
//! else if del2<>0 then del:=del2
//! else del:=del3;
//! if del<>0 then
//!   begin dmax:=abs(del1);
//!   if abs(del2)>dmax then dmax:=abs(del2);
//!   if abs(del3)>dmax then dmax:=abs(del3);
//!   while dmax<fraction_half do
//!     begin double(dmax); double(del1); double(del2); double(del3);
//!     end;
//!   end
//!
//! @ During the subdivision phases of |make_spec|, the |x_coord| and |y_coord|
//! fields of node~|q| are not transformed to agree with the octant
//! stated in |right_type(p)|; they remain consistent with |right_type(q)|.
//! But |left_x(q)| and |left_y(q)| are governed by |right_type(p)|.
//!
//! @<Complement the |x| coordinates...@>=
//! begin negate(x_coord(p)); negate(right_x(p));
//! negate(left_x(q));@/
//! negate(del1); negate(del2); negate(del3);@/
//! negate(dest_x);
//! right_type(p):=first_octant+negate_x;
//! end
//!
//! @ When a cubic is split at a |fraction| value |t|, we obtain two cubics
//! whose B\'ezier control points are obtained by a generalization of the
//! bisection process: The formula
//! `$z_k^{(j+1)}={1\over2}(z_k^{(j)}+z\k^{(j)})$' becomes
//! `$z_k^{(j+1)}=t[z_k^{(j)},z\k^{(j)}]$'.
//!
//! It is convenient to define a \.{WEB} macro |t_of_the_way| such that
//! |t_of_the_way(a)(b)| expands to |a-(a-b)*t|, i.e., to |t[a,b]|.
//!
//! If |0<=t<=1|, the quantity |t[a,b]| is always between |a| and~|b|, even in
//! the presence of rounding errors. Our subroutines
//! also obey the identity |t[a,b]+t[b,a]=a+b|.
//!
//! @d t_of_the_way_end(#)==#,t@=)@>
//! @d t_of_the_way(#)==#-take_fraction@=(@>#-t_of_the_way_end
//!
//! @<Declare the procedure called |split_cubic|@>=
//! procedure split_cubic(@!p:pointer;@!t:fraction;
//!   @!xq,@!yq:scaled); {splits the cubic after |p|}
//! var @!v:scaled; {an intermediate value}
//! @!q,@!r:pointer; {for list manipulation}
//! begin q:=link(p); r:=get_node(knot_node_size); link(p):=r; link(r):=q;@/
//! left_type(r):=left_type(q); right_type(r):=right_type(p);@#
//! v:=t_of_the_way(right_x(p))(left_x(q));
//! right_x(p):=t_of_the_way(x_coord(p))(right_x(p));
//! left_x(q):=t_of_the_way(left_x(q))(xq);
//! left_x(r):=t_of_the_way(right_x(p))(v);
//! right_x(r):=t_of_the_way(v)(left_x(q));
//! x_coord(r):=t_of_the_way(left_x(r))(right_x(r));@#
//! v:=t_of_the_way(right_y(p))(left_y(q));
//! right_y(p):=t_of_the_way(y_coord(p))(right_y(p));
//! left_y(q):=t_of_the_way(left_y(q))(yq);
//! left_y(r):=t_of_the_way(right_y(p))(v);
//! right_y(r):=t_of_the_way(v)(left_y(q));
//! y_coord(r):=t_of_the_way(left_y(r))(right_y(r));
//! end;
//!
//! @ Since $x'(t)$ is a quadratic equation, it can cross through zero
//! at~most twice. When it does cross zero, we make doubly sure that the
//! derivative is really zero at the splitting point, in case rounding errors
//! have caused the split cubic to have an apparently nonzero derivative.
//! We also make sure that the split cubic is monotonic.
//!
//! @<Subdivide the cubic with respect to $x'$, possibly twice@>=
//! begin split_cubic(p,t,dest_x,dest_y); r:=link(p);
//! if right_type(r)>negate_x then right_type(r):=first_octant
//! else right_type(r):=first_octant+negate_x;
//! if x_coord(r)<x_coord(p) then x_coord(r):=x_coord(p);
//! left_x(r):=x_coord(r);
//! if right_x(p)>x_coord(r) then right_x(p):=x_coord(r);
//!  {we always have |x_coord(p)<=right_x(p)|}
//! negate(x_coord(r)); right_x(r):=x_coord(r);
//! negate(left_x(q)); negate(dest_x);@/
//! del2:=t_of_the_way(del2)(del3);
//!   {now |0,del2,del3| represent $x'$ on the remaining interval}
//! if del2>0 then del2:=0;
//! t:=crossing_point(0,-del2,-del3);
//! if t<fraction_one then @<Subdivide the cubic a second time
//!   with respect to $x'$@>
//! else begin if x_coord(r)>dest_x then
//!     begin x_coord(r):=dest_x; left_x(r):=-x_coord(r); right_x(r):=x_coord(r);
//!     end;
//!   if left_x(q)>dest_x then left_x(q):=dest_x
//!   else if left_x(q)<x_coord(r) then left_x(q):=x_coord(r);
//!   end;
//! end
//!
//! @ @<Subdivide the cubic a second time with respect to $x'$@>=
//! begin split_cubic(r,t,dest_x,dest_y); s:=link(r);
//! if x_coord(s)<dest_x then x_coord(s):=dest_x;
//! if x_coord(s)<x_coord(r) then x_coord(s):=x_coord(r);
//! right_type(s):=right_type(p);
//! left_x(s):=x_coord(s); {now |x_coord(r)=right_x(r)<=left_x(s)|}
//! if left_x(q)<dest_x then left_x(q):=-dest_x
//! else if left_x(q)>x_coord(s) then left_x(q):=-x_coord(s)
//! else negate(left_x(q));
//! negate(x_coord(s)); right_x(s):=x_coord(s);
//! end
//!
//! @ The process of subdivision with respect to $y'$ is like that with respect
//! to~$x'$, with the slight additional complication that two or three cubics
//! might now appear between |p| and~|q|.
//!
//! @<Subdivide all cubics between |p| and |q| so that the results travel
//!   toward the first quadrant...@>=
//! pp:=p;
//! repeat qq:=link(pp);
//! abnegate(x_coord(qq),y_coord(qq),right_type(qq),right_type(pp));
//! dest_x:=cur_x; dest_y:=cur_y;@/
//! del1:=right_y(pp)-y_coord(pp); del2:=left_y(qq)-right_y(pp);
//! del3:=dest_y-left_y(qq);
//! @<Scale up |del1|, |del2|, and |del3| for greater accuracy;
//!   also set |del| to the first nonzero element of |(del1,del2,del3)|@>;
//! if del<>0 then {they weren't all zero}
//!   begin if del<0 then @<Complement the |y| coordinates of the
//!     cubic between |pp| and~|qq|@>;
//!   t:=crossing_point(del1,del2,del3);
//!   if t<fraction_one then
//!     @<Subdivide the cubic with respect to $y'$, possibly twice@>;
//!   end
//! else @<Do any special actions needed when |y| is constant;
//!   |return| or |goto continue| if a dead cubic from |p| to |q| is removed@>;
//! pp:=qq;
//! until pp=q;
//! if constant_x then @<Correct the octant code in segments with decreasing |y|@>
//!
//! @ @<Complement the |y| coordinates...@>=
//! begin negate(y_coord(pp)); negate(right_y(pp));
//! negate(left_y(qq));@/
//! negate(del1); negate(del2); negate(del3);@/
//! negate(dest_y);
//! right_type(pp):=right_type(pp)+negate_y;
//! end
//!
//! @ @<Subdivide the cubic with respect to $y'$, possibly twice@>=
//! begin split_cubic(pp,t,dest_x,dest_y); r:=link(pp);
//! if right_type(r)>negate_y then right_type(r):=right_type(r)-negate_y
//! else right_type(r):=right_type(r)+negate_y;
//! if y_coord(r)<y_coord(pp) then y_coord(r):=y_coord(pp);
//! left_y(r):=y_coord(r);
//! if right_y(pp)>y_coord(r) then right_y(pp):=y_coord(r);
//!  {we always have |y_coord(pp)<=right_y(pp)|}
//! negate(y_coord(r)); right_y(r):=y_coord(r);
//! negate(left_y(qq)); negate(dest_y);@/
//! if x_coord(r)<x_coord(pp) then x_coord(r):=x_coord(pp)
//! else if x_coord(r)>dest_x then x_coord(r):=dest_x;
//! if left_x(r)>x_coord(r) then
//!   begin left_x(r):=x_coord(r);
//!   if right_x(pp)>x_coord(r) then right_x(pp):=x_coord(r);
//!   end;
//! if right_x(r)<x_coord(r) then
//!   begin right_x(r):=x_coord(r);
//!   if left_x(qq)<x_coord(r) then left_x(qq):=x_coord(r);
//!   end;
//! del2:=t_of_the_way(del2)(del3);
//!   {now |0,del2,del3| represent $y'$ on the remaining interval}
//! if del2>0 then del2:=0;
//! t:=crossing_point(0,-del2,-del3);
//! if t<fraction_one then @<Subdivide the cubic a second time
//!   with respect to $y'$@>
//! else begin if y_coord(r)>dest_y then
//!     begin y_coord(r):=dest_y; left_y(r):=-y_coord(r); right_y(r):=y_coord(r);
//!     end;
//!   if left_y(qq)>dest_y then left_y(qq):=dest_y
//!   else if left_y(qq)<y_coord(r) then left_y(qq):=y_coord(r);
//!   end;
//! end
//!
//! @ @<Subdivide the cubic a second time with respect to $y'$@>=
//! begin split_cubic(r,t,dest_x,dest_y); s:=link(r);@/
//! if y_coord(s)<dest_y then y_coord(s):=dest_y;
//! if y_coord(s)<y_coord(r) then y_coord(s):=y_coord(r);
//! right_type(s):=right_type(pp);
//! left_y(s):=y_coord(s); {now |y_coord(r)=right_y(r)<=left_y(s)|}
//! if left_y(qq)<dest_y then left_y(qq):=-dest_y
//! else if left_y(qq)>y_coord(s) then left_y(qq):=-y_coord(s)
//! else negate(left_y(qq));
//! negate(y_coord(s)); right_y(s):=y_coord(s);
//! if x_coord(s)<x_coord(r) then x_coord(s):=x_coord(r)
//! else if x_coord(s)>dest_x then x_coord(s):=dest_x;
//! if left_x(s)>x_coord(s) then
//!   begin left_x(s):=x_coord(s);
//!   if right_x(r)>x_coord(s) then right_x(r):=x_coord(s);
//!   end;
//! if right_x(s)<x_coord(s) then
//!   begin right_x(s):=x_coord(s);
//!   if left_x(qq)<x_coord(s) then left_x(qq):=x_coord(s);
//!   end;
//! end
//!
//! @ If the cubic is constant in $y$ and increasing in $x$, we have classified
//! it as traveling in the first octant. If the cubic is constant
//! in~$y$ and decreasing in~$x$, it is desirable to classify it as traveling
//! in the fifth octant (not the fourth), because autorounding will be consistent
//! with respect to doublepaths only if the octant number changes by four when
//! the path is reversed. Therefore we negate the $y$~coordinates
//! when they are constant but the curve is decreasing in~$x$; this gives
//! the desired result except in pathological paths.
//!
//! If the cubic is ``dead,'' i.e., constant in both |x| and |y|, we remove
//! it unless it is the only cubic in the entire path. We |goto continue|
//! if it wasn't the final cubic, so that the test |p=cur_spec| does not
//! falsely imply that all cubics have been processed.
//!
//! @<Do any special actions needed when |y| is constant...@>=
//! if constant_x then {|p=pp|, |q=qq|, and the cubic is dead}
//!   begin if q<>p then
//!     begin remove_cubic(p); {remove the dead cycle and recycle node |q|}
//!     if cur_spec<>q then goto continue
//!     else  begin cur_spec:=p; return;
//!       end; {the final cubic was dead and is gone}
//!     end;
//!   end
//! else if not odd(right_type(pp)) then {the $x$ coordinates were negated}
//!   @<Complement the |y| coordinates...@>
//!
//! @ A similar correction to octant codes deserves to be made when |x| is
//! constant and |y| is decreasing.
//!
//! @<Correct the octant code in segments with decreasing |y|@>=
//! begin pp:=p;
//! repeat qq:=link(pp);
//! if right_type(pp)>negate_y then {the $y$ coordinates were negated}
//!   begin right_type(pp):=right_type(pp)+negate_x;
//!   negate(x_coord(pp)); negate(right_x(pp)); negate(left_x(qq));
//!   end;
//! pp:=qq;
//! until pp=q;
//! end
//!
//! @ Finally, the process of subdividing to make $x'\G y'$ is like the other
//! two subdivisions, with a few new twists. We skew the coordinates at this time.
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! procedure octant_subdivide;
//! var @!p,@!q,@!r,@!s:pointer; {for traversing the lists}
//! @!del1,@!del2,@!del3,@!del,@!dmax:scaled; {proportional to the control
//!   points of a quadratic derived from a cubic}
//! @!t:fraction; {where a quadratic crosses zero}
//! @!dest_x,@!dest_y:scaled; {final values of |x| and |y| in the current cubic}
//! begin p:=cur_spec;
//! repeat q:=link(p);@/
//! x_coord(p):=x_coord(p)-y_coord(p);
//! right_x(p):=right_x(p)-right_y(p);
//! left_x(q):=left_x(q)-left_y(q);@/
//! @<Subdivide the cubic between |p| and |q| so that the results travel
//!   toward the first octant@>;
//! p:=q;
//! until p=cur_spec;
//! end;
//!
//! @ @<Subdivide the cubic between |p| and |q| so that the results travel
//!   toward the first octant@>=
//! @<Set up the variables |(del1,del2,del3)| to represent $x'-y'$@>;
//! @<Scale up |del1|, |del2|, and |del3| for greater accuracy;
//!   also set |del| to the first nonzero element of |(del1,del2,del3)|@>;
//! if del<>0 then {they weren't all zero}
//!   begin if del<0 then @<Swap the |x| and |y| coordinates of the
//!     cubic between |p| and~|q|@>;
//!   t:=crossing_point(del1,del2,del3);
//!   if t<fraction_one then
//!     @<Subdivide the cubic with respect to $x'-y'$, possibly twice@>;
//!   end
//!
//! @ @<Set up the variables |(del1,del2,del3)| to represent $x'-y'$@>=
//! if q=cur_spec then
//!   begin unskew(x_coord(q),y_coord(q),right_type(q));
//!   skew(cur_x,cur_y,right_type(p)); dest_x:=cur_x; dest_y:=cur_y;
//!   end
//! else  begin abnegate(x_coord(q),y_coord(q),right_type(q),right_type(p));
//!   dest_x:=cur_x-cur_y; dest_y:=cur_y;
//!   end;
//! del1:=right_x(p)-x_coord(p); del2:=left_x(q)-right_x(p);
//! del3:=dest_x-left_x(q)
//!
//! @ The swapping here doesn't simply interchange |x| and |y| values,
//! because the coordinates are skewed. It turns out that this is easier
//! than ordinary swapping, because it can be done in two assignment statements
//! rather than three.
//!
//! @ @<Swap the |x| and |y| coordinates...@>=
//! begin y_coord(p):=x_coord(p)+y_coord(p); negate(x_coord(p));@/
//! right_y(p):=right_x(p)+right_y(p); negate(right_x(p));@/
//! left_y(q):=left_x(q)+left_y(q); negate(left_x(q));@/
//! negate(del1); negate(del2); negate(del3);@/
//! dest_y:=dest_x+dest_y; negate(dest_x);@/
//! right_type(p):=right_type(p)+switch_x_and_y;
//! end
//!
//! @ A somewhat tedious case analysis is carried out here to make sure that
//! nasty rounding errors don't destroy our assumptions of monotonicity.
//!
//! @<Subdivide the cubic with respect to $x'-y'$, possibly twice@>=
//! begin split_cubic(p,t,dest_x,dest_y); r:=link(p);
//! if right_type(r)>switch_x_and_y then right_type(r):=right_type(r)-switch_x_and_y
//! else right_type(r):=right_type(r)+switch_x_and_y;
//! if y_coord(r)<y_coord(p) then y_coord(r):=y_coord(p)
//! else if y_coord(r)>dest_y then y_coord(r):=dest_y;
//! if x_coord(p)+y_coord(r)>dest_x+dest_y then
//!   y_coord(r):=dest_x+dest_y-x_coord(p);
//! if left_y(r)>y_coord(r) then
//!   begin left_y(r):=y_coord(r);
//!   if right_y(p)>y_coord(r) then right_y(p):=y_coord(r);
//!   end;
//! if right_y(r)<y_coord(r) then
//!   begin right_y(r):=y_coord(r);
//!   if left_y(q)<y_coord(r) then left_y(q):=y_coord(r);
//!   end;
//! if x_coord(r)<x_coord(p) then x_coord(r):=x_coord(p)
//! else if x_coord(r)+y_coord(r)>dest_x+dest_y then
//!   x_coord(r):=dest_x+dest_y-y_coord(r);
//! left_x(r):=x_coord(r);
//! if right_x(p)>x_coord(r) then right_x(p):=x_coord(r);
//!  {we always have |x_coord(p)<=right_x(p)|}
//! y_coord(r):=y_coord(r)+x_coord(r); right_y(r):=right_y(r)+x_coord(r);@/
//! negate(x_coord(r)); right_x(r):=x_coord(r);@/
//! left_y(q):=left_y(q)+left_x(q); negate(left_x(q));@/
//! dest_y:=dest_y+dest_x; negate(dest_x);
//! if right_y(r)<y_coord(r) then
//!   begin right_y(r):=y_coord(r);
//!   if left_y(q)<y_coord(r) then left_y(q):=y_coord(r);
//!   end;
//! del2:=t_of_the_way(del2)(del3);
//!   {now |0,del2,del3| represent $x'-y'$ on the remaining interval}
//! if del2>0 then del2:=0;
//! t:=crossing_point(0,-del2,-del3);
//! if t<fraction_one then
//!   @<Subdivide the cubic a second time with respect to $x'-y'$@>
//! else begin if x_coord(r)>dest_x then
//!     begin x_coord(r):=dest_x; left_x(r):=-x_coord(r); right_x(r):=x_coord(r);
//!     end;
//!   if left_x(q)>dest_x then left_x(q):=dest_x
//!   else if left_x(q)<x_coord(r) then left_x(q):=x_coord(r);
//!   end;
//! end
//!
//! @ @<Subdivide the cubic a second time with respect to $x'-y'$@>=
//! begin split_cubic(r,t,dest_x,dest_y); s:=link(r);@/
//! if y_coord(s)<y_coord(r) then y_coord(s):=y_coord(r)
//! else if y_coord(s)>dest_y then y_coord(s):=dest_y;
//! if x_coord(r)+y_coord(s)>dest_x+dest_y then
//!   y_coord(s):=dest_x+dest_y-x_coord(r);
//! if left_y(s)>y_coord(s) then
//!   begin left_y(s):=y_coord(s);
//!   if right_y(r)>y_coord(s) then right_y(r):=y_coord(s);
//!   end;
//! if right_y(s)<y_coord(s) then
//!   begin right_y(s):=y_coord(s);
//!   if left_y(q)<y_coord(s) then left_y(q):=y_coord(s);
//!   end;
//! if x_coord(s)+y_coord(s)>dest_x+dest_y then x_coord(s):=dest_x+dest_y-y_coord(s)
//! else begin if x_coord(s)<dest_x then x_coord(s):=dest_x;
//!   if x_coord(s)<x_coord(r) then x_coord(s):=x_coord(r);
//!   end;
//! right_type(s):=right_type(p);
//! left_x(s):=x_coord(s); {now |x_coord(r)=right_x(r)<=left_x(s)|}
//! if left_x(q)<dest_x then
//!   begin left_y(q):=left_y(q)+dest_x; left_x(q):=-dest_x;@+end
//! else if left_x(q)>x_coord(s) then
//!   begin left_y(q):=left_y(q)+x_coord(s); left_x(q):=-x_coord(s);@+end
//! else begin left_y(q):=left_y(q)+left_x(q); negate(left_x(q));@+end;
//! y_coord(s):=y_coord(s)+x_coord(s); right_y(s):=right_y(s)+x_coord(s);@/
//! negate(x_coord(s)); right_x(s):=x_coord(s);@/
//! if right_y(s)<y_coord(s) then
//!   begin right_y(s):=y_coord(s);
//!   if left_y(q)<y_coord(s) then left_y(q):=y_coord(s);
//!   end;
//! end
//!
//! @ It's time now to consider ``autorounding,'' which tries to make horizontal,
//! vertical, and diagonal tangents occur at places that will produce appropriate
//! images after the curve is digitized.
//!
//! The first job is to fix things so that |x(t)| plus the horizontal pen offset
//! is an integer multiple of the
//! current ``granularity'' when the derivative $x'(t)$ crosses through zero.
//! The given cyclic path contains regions where $x'(t)\G0$ and regions
//! where $x'(t)\L0$. The |quadrant_subdivide| routine is called into action
//! before any of the path coordinates have been skewed, but some of them
//! may have been negated. In regions where $x'(t)\G0$ we have |right_type=
//! first_octant| or |right_type=eighth_octant|; in regions where $x'(t)\L0$,
//! we have |right_type=fifth_octant| or |right_type=fourth_octant|.
//!
//! Within any such region the transformed $x$ values increase monotonically
//! from, say, $x_0$ to~$x_1$. We want to modify things by applying a linear
//! transformation to all $x$ coordinates in the region, after which
//! the $x$ values will increase monotonically from round$(x_0)$ to round$(x_1)$.
//!
//! This rounding scheme sounds quite simple, and it usually is. But several
//! complications can arise that might make the task more difficult. In the
//! first place, autorounding is inappropriate at cusps where $x'$ jumps
//! discontinuously past zero without ever being zero. In the second place,
//! the current pen might be unsymmetric in such a way that $x$ coordinates
//! should round differently in different parts of the curve.
//! These considerations imply that round$(x_0)$ might be greater
//! than round$(x_1)$, even though $x_0\L x_1$; in such cases we do not want
//! to carry out the linear transformation. Furthermore, it's possible to have
//! round$(x_1)-\hbox{round} (x_0)$ positive but much greater than $x_1-x_0$;
//! then the transformation might distort the curve drastically, and again we
//! want to avoid it. Finally, the rounded points must be consistent between
//! adjacent regions, hence we can't transform one region without knowing
//! about its neighbors.
//!
//! To handle all these complications, we must first look at the whole
//! cycle and choose rounded $x$ values that are ``safe.'' The following
//! procedure does this: Given $m$~values $(b_0,b_1,\ldots,b_{m-1})$ before
//! rounding and $m$~corresponding values $(a_0,a_1,\ldots,a_{m-1})$ that would
//! be desirable after rounding, the |make_safe| routine sets $a$'s to $b$'s
//! if necessary so that $0\L(a\k-a_k)/(b\k-b_k)\L2$ afterwards. It is
//! symmetric under cyclic permutation, reversal, and/or negation of the inputs.
//! (Instead of |a|, |b|, and~|m|, the program uses the names |after|,
//! |before|, and |cur_rounding_ptr|.)
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! procedure make_safe;
//! var @!k:0..max_wiggle; {runs through the list of inputs}
//! @!all_safe:boolean; {does everything look OK so far?}
//! @!next_a:scaled; {|after[k]| before it might have changed}
//! @!delta_a,@!delta_b:scaled; {|after[k+1]-after[k]| and |before[k+1]-before[k]|}
//! begin before[cur_rounding_ptr]:=before[0]; {wrap around}
//! node_to_round[cur_rounding_ptr]:=node_to_round[0];
//! repeat after[cur_rounding_ptr]:=after[0]; all_safe:=true; next_a:=after[0];
//! for k:=0 to cur_rounding_ptr-1 do
//!   begin delta_b:=before[k+1]-before[k];
//!   if delta_b>=0 then delta_a:=after[k+1]-next_a
//!   else delta_a:=next_a-after[k+1];
//!   next_a:=after[k+1];
//!   if (delta_a<0)or(delta_a>abs(delta_b+delta_b)) then
//!     begin all_safe:=false; after[k]:=before[k];
//!     if k=cur_rounding_ptr-1 then after[0]:=before[0]
//!     else after[k+1]:=before[k+1];
//!     end;
//!   end;
//! until all_safe;
//! end;
//!
//! @ The global arrays used by |make_safe| are accompanied by an array of
//! pointers into the current knot list.
//!
//! @<Glob...@>=
//! @!before,@!after:array[0..max_wiggle] of scaled; {data for |make_safe|}
//! @!node_to_round:array[0..max_wiggle] of pointer; {reference back to the path}
//! @!cur_rounding_ptr:0..max_wiggle; {how many are being used}
//! @!max_rounding_ptr:0..max_wiggle; {how many have been used}
//!
//! @ @<Set init...@>=
//! max_rounding_ptr:=0;
//!
//! @ New entries go into the tables via the |before_and_after| routine:
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! procedure before_and_after(@!b,@!a:scaled;@!p:pointer);
//! begin if cur_rounding_ptr=max_rounding_ptr then
//!   if max_rounding_ptr<max_wiggle then incr(max_rounding_ptr)
//!   else overflow("rounding table size",max_wiggle);
//! @:METAFONT capacity exceeded rounding table size}{\quad rounding table size@>
//! after[cur_rounding_ptr]:=a; before[cur_rounding_ptr]:=b;
//! node_to_round[cur_rounding_ptr]:=p; incr(cur_rounding_ptr);
//! end;
//!
//! @ A global variable called |cur_gran| is used instead of |internal[
//! granularity]|, because we want to work with a number that's guaranteed to
//! be positive.
//!
//! @<Glob...@>=
//! @!cur_gran:scaled; {the current granularity (which normally is |unity|)}
//!
//! @ The |good_val| function computes a number |a| that's as close as
//! possible to~|b|, with the property that |a+o| is a multiple of
//! |cur_gran|.
//!
//! If we assume that |cur_gran| is even (since it will in fact be a multiple
//! of |unity| in all reasonable applications), we have the identity
//! |good_val(-b-1,-o)=-good_val(b,o)|.
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! function good_val(@!b,@!o:scaled):scaled;
//! var @!a:scaled; {accumulator}
//! begin a:=b+o;
//! if a>=0 then a:=a-(a mod cur_gran)-o
//! else a:=a+((-(a+1)) mod cur_gran)-cur_gran+1-o;
//! if b-a<a+cur_gran-b then good_val:=a
//! else good_val:=a+cur_gran;
//! end;
//!
//! @ When we're rounding a doublepath, we might need to compromise between
//! two opposing tendencies, if the pen thickness is not a multiple of the
//! granularity. The following ``compromise'' adjustment, suggested by
//! John Hobby, finds the best way out of the dilemma. (Only the value
//! @^Hobby, John Douglas@>
//! modulo |cur_gran| is relevant in our applications, so the result turns
//! out to be essentially symmetric in |u| and~|v|.)
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! function compromise(@!u,@!v:scaled):scaled;
//! begin compromise:=half(good_val(u+u,-u-v));
//! end;
//!
//! @ Here, then, is the procedure that rounds $x$ coordinates as described;
//! it does the same for $y$ coordinates too, independently.
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! procedure xy_round;
//! var @!p,@!q:pointer; {list manipulation registers}
//! @!b,@!a:scaled; {before and after values}
//! @!pen_edge:scaled; {offset that governs rounding}
//! @!alpha:fraction; {coefficient of linear transformation}
//! begin cur_gran:=abs(internal[granularity]);
//! if cur_gran=0 then cur_gran:=unity;
//! p:=cur_spec; cur_rounding_ptr:=0;
//! repeat q:=link(p);
//! @<If node |q| is a transition point for |x| coordinates,
//!   compute and save its before-and-after coordinates@>;
//! p:=q;
//! until p=cur_spec;
//! if cur_rounding_ptr>0 then @<Transform the |x| coordinates@>;
//! p:=cur_spec; cur_rounding_ptr:=0;
//! repeat q:=link(p);
//! @<If node |q| is a transition point for |y| coordinates,
//!   compute and save its before-and-after coordinates@>;
//! p:=q;
//! until p=cur_spec;
//! if cur_rounding_ptr>0 then @<Transform the |y| coordinates@>;
//! end;
//!
//! @ When |x| has been negated, the |octant| codes are even. We allow
//! for an error of up to .01 pixel (i.e., 655 |scaled| units) in the
//! derivative calculations at transition nodes.
//!
//! @<If node |q| is a transition point for |x| coordinates...@>=
//! if odd(right_type(p))<>odd(right_type(q)) then
//!   begin if odd(right_type(q)) then b:=x_coord(q)@+else b:=-x_coord(q);
//!   if (abs(x_coord(q)-right_x(q))<655)or@|
//!     (abs(x_coord(q)+left_x(q))<655) then
//!     @<Compute before-and-after |x| values based on the current pen@>
//!   else a:=b;
//!   if abs(a)>max_allowed then
//!     if a>0 then a:=max_allowed@+else a:=-max_allowed;
//!   before_and_after(b,a,q);
//!   end
//!
//! @ When we study the data representation for pens, we'll learn that the
//! |x|~coordinate of the current pen's west edge is
//! $$\hbox{|y_coord(link(cur_pen+seventh_octant))|},$$
//! and that there are similar ways to address other important offsets.
//!
//! @d north_edge(#)==y_coord(link(#+fourth_octant))
//! @d south_edge(#)==y_coord(link(#+first_octant))
//! @d east_edge(#)==y_coord(link(#+second_octant))
//! @d west_edge(#)==y_coord(link(#+seventh_octant))
//!
//! @<Compute before-and-after |x| values based on the current pen@>=
//! begin if cur_pen=null_pen then pen_edge:=0
//! else if cur_path_type=double_path_code then
//!   pen_edge:=compromise(east_edge(cur_pen),west_edge(cur_pen))
//! else if odd(right_type(q)) then pen_edge:=west_edge(cur_pen)
//! else pen_edge:=east_edge(cur_pen);
//! a:=good_val(b,pen_edge);
//! end
//!
//! @  The monotone transformation computed here with fixed-point arithmetic is
//! guaranteed to take consecutive |before| values $(b,b')$ into consecutive
//! |after| values $(a,a')$, even in the presence of rounding errors,
//! as long as $\vert b-b'\vert<2^{28}$.
//!
//! @<Transform the |x| coordinates@>=
//! begin make_safe;
//! repeat decr(cur_rounding_ptr);
//! if (after[cur_rounding_ptr]<>before[cur_rounding_ptr])or@|
//!  (after[cur_rounding_ptr+1]<>before[cur_rounding_ptr+1]) then
//!   begin p:=node_to_round[cur_rounding_ptr];
//!   if odd(right_type(p)) then
//!     begin b:=before[cur_rounding_ptr]; a:=after[cur_rounding_ptr];
//!     end
//!   else  begin b:=-before[cur_rounding_ptr]; a:=-after[cur_rounding_ptr];
//!     end;
//!   if before[cur_rounding_ptr]=before[cur_rounding_ptr+1] then
//!     alpha:=fraction_one
//!   else alpha:=make_fraction(after[cur_rounding_ptr+1]-after[cur_rounding_ptr],@|
//!     before[cur_rounding_ptr+1]-before[cur_rounding_ptr]);
//!   repeat x_coord(p):=take_fraction(alpha,x_coord(p)-b)+a;
//!   right_x(p):=take_fraction(alpha,right_x(p)-b)+a;
//!   p:=link(p); left_x(p):=take_fraction(alpha,left_x(p)-b)+a;
//!   until p=node_to_round[cur_rounding_ptr+1];
//!   end;
//! until cur_rounding_ptr=0;
//! end
//!
//! @ When |y| has been negated, the |octant| codes are |>negate_y|. Otherwise
//! these routines are essentially identical to the routines for |x| coordinates
//! that we have just seen.
//!
//! @<If node |q| is a transition point for |y| coordinates...@>=
//! if (right_type(p)>negate_y)<>(right_type(q)>negate_y) then
//!   begin if right_type(q)<=negate_y then b:=y_coord(q)@+else b:=-y_coord(q);
//!   if (abs(y_coord(q)-right_y(q))<655)or@|
//!     (abs(y_coord(q)+left_y(q))<655) then
//!     @<Compute before-and-after |y| values based on the current pen@>
//!   else a:=b;
//!   if abs(a)>max_allowed then
//!     if a>0 then a:=max_allowed@+else a:=-max_allowed;
//!   before_and_after(b,a,q);
//!   end
//!
//! @ @<Compute before-and-after |y| values based on the current pen@>=
//! begin if cur_pen=null_pen then pen_edge:=0
//! else if cur_path_type=double_path_code then
//!   pen_edge:=compromise(north_edge(cur_pen),south_edge(cur_pen))
//! else if right_type(q)<=negate_y then pen_edge:=south_edge(cur_pen)
//! else pen_edge:=north_edge(cur_pen);
//! a:=good_val(b,pen_edge);
//! end
//!
//! @ @<Transform the |y| coordinates@>=
//! begin make_safe;
//! repeat decr(cur_rounding_ptr);
//! if (after[cur_rounding_ptr]<>before[cur_rounding_ptr])or@|
//!  (after[cur_rounding_ptr+1]<>before[cur_rounding_ptr+1]) then
//!   begin p:=node_to_round[cur_rounding_ptr];
//!   if right_type(p)<=negate_y then
//!     begin b:=before[cur_rounding_ptr]; a:=after[cur_rounding_ptr];
//!     end
//!   else  begin b:=-before[cur_rounding_ptr]; a:=-after[cur_rounding_ptr];
//!     end;
//!   if before[cur_rounding_ptr]=before[cur_rounding_ptr+1] then
//!     alpha:=fraction_one
//!   else alpha:=make_fraction(after[cur_rounding_ptr+1]-after[cur_rounding_ptr],@|
//!     before[cur_rounding_ptr+1]-before[cur_rounding_ptr]);
//!   repeat y_coord(p):=take_fraction(alpha,y_coord(p)-b)+a;
//!   right_y(p):=take_fraction(alpha,right_y(p)-b)+a;
//!   p:=link(p); left_y(p):=take_fraction(alpha,left_y(p)-b)+a;
//!   until p=node_to_round[cur_rounding_ptr+1];
//!   end;
//! until cur_rounding_ptr=0;
//! end
//!
//! @ Rounding at diagonal tangents takes place after the subdivision into
//! octants is complete, hence after the coordinates have been skewed.
//! The details are somewhat tricky, because we want to round to points
//! whose skewed coordinates are halfway between integer multiples of
//! the granularity. Furthermore, both coordinates change when they are
//! rounded; this means we need a generalization of the |make_safe| routine,
//! ensuring safety in both |x| and |y|.
//!
//! In spite of these extra complications, we can take comfort in the fact
//! that the basic structure of the routine is the same as before.
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! procedure diag_round;
//! var @!p,@!q,@!pp:pointer; {list manipulation registers}
//! @!b,@!a,@!bb,@!aa,@!d,@!c,@!dd,@!cc:scaled; {before and after values}
//! @!pen_edge:scaled; {offset that governs rounding}
//! @!alpha,@!beta:fraction; {coefficients of linear transformation}
//! @!next_a:scaled; {|after[k]| before it might have changed}
//! @!all_safe:boolean; {does everything look OK so far?}
//! @!k:0..max_wiggle; {runs through before-and-after values}
//! @!first_x,@!first_y:scaled; {coordinates before rounding}
//! begin p:=cur_spec; cur_rounding_ptr:=0;
//! repeat q:=link(p);
//! @<If node |q| is a transition point between octants,
//!   compute and save its before-and-after coordinates@>;
//! p:=q;
//! until p=cur_spec;
//! if cur_rounding_ptr>0 then @<Transform the skewed coordinates@>;
//! end;
//!
//! @ We negate the skewed |x| coordinates in the before-and-after table when
//! the octant code is greater than |switch_x_and_y|.
//!
//! @<If node |q| is a transition point between octants...@>=
//! if right_type(p)<>right_type(q) then
//!   begin if right_type(q)>switch_x_and_y then b:=-x_coord(q)
//!   else b:=x_coord(q);
//!   if abs(right_type(q)-right_type(p))=switch_x_and_y then
//!     if (abs(x_coord(q)-right_x(q))<655)or(abs(x_coord(q)+left_x(q))<655) then
//!       @<Compute a good coordinate at a diagonal transition@>
//!     else a:=b
//!   else a:=b;
//!   before_and_after(b,a,q);
//!   end
//!
//! @ In octants whose code number is even, $x$~has been
//! negated; we want to round ambiguous cases downward instead of upward,
//! so that the rounding will be consistent with octants whose code
//! number is odd. This downward bias can be achieved by
//! subtracting~1 from the first argument of |good_val|.
//!
//! @d diag_offset(#)==x_coord(knil(link(cur_pen+#)))
//!
//! @<Compute a good coordinate at a diagonal transition@>=
//! begin if cur_pen=null_pen then pen_edge:=0
//! else if cur_path_type=double_path_code then @<Compute a compromise |pen_edge|@>
//! else if right_type(q)<=switch_x_and_y then pen_edge:=diag_offset(right_type(q))
//! else pen_edge:=-diag_offset(right_type(q));
//! if odd(right_type(q)) then a:=good_val(b,pen_edge+half(cur_gran))
//! else a:=good_val(b-1,pen_edge+half(cur_gran));
//! end
//!
//! @ (It seems a shame to compute these compromise offsets repeatedly. The
//! author would have stored them directly in the pen data structure, if the
//! granularity had been constant.)
//!
//! @<Compute a compromise...@>=
//! case right_type(q) of
//! first_octant,second_octant:pen_edge:=compromise(diag_offset(first_octant),@|
//!     -diag_offset(fifth_octant));
//! fifth_octant,sixth_octant:pen_edge:=-compromise(diag_offset(first_octant),@|
//!     -diag_offset(fifth_octant));
//! third_octant,fourth_octant:pen_edge:=compromise(diag_offset(fourth_octant),@|
//!     -diag_offset(eighth_octant));
//! seventh_octant,eighth_octant:pen_edge:=-compromise(diag_offset(fourth_octant),@|
//!     -diag_offset(eighth_octant));
//! end {there are no other cases}
//!
//! @ @<Transform the skewed coordinates@>=
//! begin p:=node_to_round[0]; first_x:=x_coord(p); first_y:=y_coord(p);
//! @<Make sure that all the diagonal roundings are safe@>;
//! for k:=0 to cur_rounding_ptr-1 do
//!   begin a:=after[k]; b:=before[k];
//!   aa:=after[k+1]; bb:=before[k+1];
//!   if (a<>b)or(aa<>bb) then
//!     begin p:=node_to_round[k]; pp:=node_to_round[k+1];
//!     @<Determine the before-and-after values of both coordinates@>;
//!     if b=bb then alpha:=fraction_one
//!     else alpha:=make_fraction(aa-a,bb-b);
//!     if d=dd then beta:=fraction_one
//!     else beta:=make_fraction(cc-c,dd-d);
//!     repeat x_coord(p):=take_fraction(alpha,x_coord(p)-b)+a;
//!     y_coord(p):=take_fraction(beta,y_coord(p)-d)+c;
//!     right_x(p):=take_fraction(alpha,right_x(p)-b)+a;
//!     right_y(p):=take_fraction(beta,right_y(p)-d)+c;
//!     p:=link(p); left_x(p):=take_fraction(alpha,left_x(p)-b)+a;
//!     left_y(p):=take_fraction(beta,left_y(p)-d)+c;
//!     until p=pp;
//!     end;
//!   end;
//! end
//!
//! @ In node |p|, the coordinates |(b,d)| will be rounded to |(a,c)|;
//! in node |pp|, the coordinates |(bb,dd)| will be rounded to |(aa,cc)|.
//! (We transform the values from node |pp| so that they agree with the
//! conventions of node |p|.)
//!
//! If |aa<>bb|, we know that |abs(right_type(p)-right_type(pp))=switch_x_and_y|.
//!
//! @<Determine the before-and-after values of both coordinates@>=
//! if aa=bb then
//!   begin if pp=node_to_round[0] then
//!     unskew(first_x,first_y,right_type(pp))
//!   else unskew(x_coord(pp),y_coord(pp),right_type(pp));
//!   skew(cur_x,cur_y,right_type(p));
//!   bb:=cur_x; aa:=bb; dd:=cur_y; cc:=dd;
//!   if right_type(p)>switch_x_and_y then
//!     begin b:=-b; a:=-a;
//!     end;
//!   end
//! else  begin if right_type(p)>switch_x_and_y then
//!     begin bb:=-bb; aa:=-aa; b:=-b; a:=-a;
//!     end;
//!   if pp=node_to_round[0] then dd:=first_y-bb@+else dd:=y_coord(pp)-bb;
//!   if odd(aa-bb) then
//!     if right_type(p)>switch_x_and_y then cc:=dd-half(aa-bb+1)
//!     else cc:=dd-half(aa-bb-1)
//!   else cc:=dd-half(aa-bb);
//!   end;
//! d:=y_coord(p);
//! if odd(a-b) then
//!   if right_type(p)>switch_x_and_y then c:=d-half(a-b-1)
//!   else c:=d-half(a-b+1)
//! else c:=d-half(a-b)
//!
//! @ @<Make sure that all the diagonal roundings are safe@>=
//! before[cur_rounding_ptr]:=before[0]; {cf.~|make_safe|}
//! node_to_round[cur_rounding_ptr]:=node_to_round[0];
//! repeat after[cur_rounding_ptr]:=after[0]; all_safe:=true; next_a:=after[0];
//! for k:=0 to cur_rounding_ptr-1 do
//!   begin a:=next_a; b:=before[k]; next_a:=after[k+1];
//!   aa:=next_a; bb:=before[k+1];
//!   if (a<>b)or(aa<>bb) then
//!     begin p:=node_to_round[k]; pp:=node_to_round[k+1];
//!     @<Determine the before-and-after values of both coordinates@>;
//!     if (aa<a)or(cc<c)or(aa-a>2*(bb-b))or(cc-c>2*(dd-d)) then
//!       begin all_safe:=false; after[k]:=before[k];
//!       if k=cur_rounding_ptr-1 then after[0]:=before[0]
//!       else after[k+1]:=before[k+1];
//!       end;
//!     end;
//!   end;
//! until all_safe
//!
//! @ Here we get rid of ``dead'' cubics, i.e., polynomials that don't move at
//! all when |t|~changes, since the subdivision process might have introduced
//! such things.  If the cycle reduces to a single point, however, we are left
//! with a single dead cubic that will not be removed until later.
//!
//! @<Remove dead cubics@>=
//! p:=cur_spec;
//! repeat continue: q:=link(p);
//! if p<>q then
//!   begin if x_coord(p)=right_x(p) then
//!    if y_coord(p)=right_y(p) then
//!     if x_coord(p)=left_x(q) then
//!      if y_coord(p)=left_y(q) then
//!     begin unskew(x_coord(q),y_coord(q),right_type(q));
//!     skew(cur_x,cur_y,right_type(p));
//!     if x_coord(p)=cur_x then if y_coord(p)=cur_y then
//!       begin remove_cubic(p); {remove the cubic following |p|}
//!       if q<>cur_spec then goto continue;
//!       cur_spec:=p; q:=p;
//!       end;
//!     end;
//!   end;
//! p:=q;
//! until p=cur_spec;
//!
//! @ Finally we come to the last steps of |make_spec|, when boundary nodes
//! are inserted between cubics that move in different octants. The main
//! complication remaining arises from consecutive cubics whose octants
//! are not adjacent; we should insert more than one octant boundary
//! at such sharp turns, so that the envelope-forming routine will work.
//!
//! For this purpose, conversion tables between numeric and Gray codes for
//! octants are desirable.
//!
//! @<Glob...@>=
//! @!octant_number:array[first_octant..sixth_octant] of 1..8;
//! @!octant_code:array[1..8] of first_octant..sixth_octant;
//!
//! @ @<Set init...@>=
//! octant_code[1]:=first_octant;
//! octant_code[2]:=second_octant;
//! octant_code[3]:=third_octant;
//! octant_code[4]:=fourth_octant;
//! octant_code[5]:=fifth_octant;
//! octant_code[6]:=sixth_octant;
//! octant_code[7]:=seventh_octant;
//! octant_code[8]:=eighth_octant;
//! for k:=1 to 8 do octant_number[octant_code[k]]:=k;
//!
//! @ The main loop for boundary insertion deals with three consecutive
//! nodes |p,q,r|.
//!
//! @<Insert octant boundaries and compute the turning number@>=
//! turning_number:=0;
//! p:=cur_spec; q:=link(p);
//! repeat r:=link(q);
//! if (right_type(p)<>right_type(q))or(q=r) then
//!   @<Insert one or more octant boundary nodes just before~|q|@>;
//! p:=q; q:=r;
//! until p=cur_spec;
//!
//! @ The |new_boundary| subroutine comes in handy at this point. It inserts
//! a new boundary node just after a given node |p|, using a given octant code
//! to transform the new node's coordinates. The ``transition'' fields are
//! not computed here.
//!
//! @<Declare subroutines needed by |make_spec|@>=
//! procedure new_boundary(@!p:pointer;@!octant:small_number);
//! var @!q,@!r:pointer; {for list manipulation}
//! begin q:=link(p); {we assume that |right_type(q)<>endpoint|}
//! r:=get_node(knot_node_size); link(r):=q; link(p):=r;
//! left_type(r):=left_type(q); {but possibly |left_type(q)=endpoint|}
//! left_x(r):=left_x(q); left_y(r):=left_y(q);
//! right_type(r):=endpoint; left_type(q):=endpoint;
//! right_octant(r):=octant; left_octant(q):=right_type(q);
//! unskew(x_coord(q),y_coord(q),right_type(q));
//! skew(cur_x,cur_y,octant); x_coord(r):=cur_x; y_coord(r):=cur_y;
//! end;
//!
//! @ The case |q=r| occurs if and only if |p=q=r=cur_spec|, when we want to turn
//! $360^\circ$ in eight steps and then remove a solitary dead cubic.
//! The program below happens to work in that case, but the reader isn't
//! expected to understand why.
//!
//! @<Insert one or more octant boundary nodes just before~|q|@>=
//! begin new_boundary(p,right_type(p)); s:=link(p);
//! o1:=octant_number[right_type(p)]; o2:=octant_number[right_type(q)];
//! case o2-o1 of
//! 1,-7,7,-1: goto done;
//! 2,-6: clockwise:=false;
//! 3,-5,4,-4,5,-3: @<Decide whether or not to go clockwise@>;
//! 6,-2: clockwise:=true;
//! 0:clockwise:=rev_turns;
//! end; {there are no other cases}
//! @<Insert additional boundary nodes, then |goto done|@>;
//! done: if q=r then
//!   begin q:=link(q); r:=q; p:=s; link(s):=q; left_octant(q):=right_octant(q);
//!   left_type(q):=endpoint; free_node(cur_spec,knot_node_size); cur_spec:=q;
//!   end;
//! @<Fix up the transition fields and adjust the turning number@>;
//! end
//!
//! @ @<Other local variables for |make_spec|@>=
//! @!o1,@!o2:small_number; {octant numbers}
//! @!clockwise:boolean; {should we turn clockwise?}
//! @!dx1,@!dy1,@!dx2,@!dy2:integer; {directions of travel at a cusp}
//! @!dmax,@!del:integer; {temporary registers}
//!
//! @ A tricky question arises when a path jumps four octants. We want the
//! direction of turning to be counterclockwise if the curve has changed
//! direction by $180^\circ$, or by something so close to $180^\circ$ that
//! the difference is probably due to rounding errors; otherwise we want to
//! turn through an angle of less than $180^\circ$. This decision needs to
//! be made even when a curve seems to have jumped only three octants, since
//! a curve may approach direction $(-1,0)$ from the fourth octant, then
//! it might leave from direction $(+1,0)$ into the first.
//!
//! The following code solves the problem by analyzing the incoming
//! direction |(dx1,dy1)| and the outgoing direction |(dx2,dy2)|.
//!
//! @<Decide whether or not to go clockwise@>=
//! begin @<Compute the incoming and outgoing directions@>;
//! unskew(dx1,dy1,right_type(p)); del:=pyth_add(cur_x,cur_y);@/
//! dx1:=make_fraction(cur_x,del); dy1:=make_fraction(cur_y,del);
//!   {$\cos\theta_1$ and $\sin\theta_1$}
//! unskew(dx2,dy2,right_type(q)); del:=pyth_add(cur_x,cur_y);@/
//! dx2:=make_fraction(cur_x,del); dy2:=make_fraction(cur_y,del);
//!   {$\cos\theta_2$ and $\sin\theta_2$}
//! del:=take_fraction(dx1,dy2)-take_fraction(dx2,dy1); {$\sin(\theta_2-\theta_1)$}
//! if del>4684844 then clockwise:=false
//! else if del<-4684844 then clockwise:=true
//!   {$2^{28}\cdot\sin 1^\circ\approx4684844.68$}
//! else clockwise:=rev_turns;
//! end
//!
//! @ Actually the turnarounds just computed will be clockwise,
//! not counterclockwise, if
//! the global variable |rev_turns| is |true|; it is usually |false|.
//!
//! @<Glob...@>=
//! @!rev_turns:boolean; {should we make U-turns in the English manner?}
//!
//! @ @<Set init...@>=
//! rev_turns:=false;
//!
//! @ @<Compute the incoming and outgoing directions@>=
//! dx1:=x_coord(s)-left_x(s); dy1:=y_coord(s)-left_y(s);
//! if dx1=0 then if dy1=0 then
//!   begin dx1:=x_coord(s)-right_x(p); dy1:=y_coord(s)-right_y(p);
//!   if dx1=0 then if dy1=0 then
//!     begin dx1:=x_coord(s)-x_coord(p); dy1:=y_coord(s)-y_coord(p);
//!     end;  {and they {\sl can't} both be zero}
//!   end;
//! dmax:=abs(dx1);@+if abs(dy1)>dmax then dmax:=abs(dy1);
//! while dmax<fraction_one do
//!   begin double(dmax); double(dx1); double(dy1);
//!   end;
//! dx2:=right_x(q)-x_coord(q); dy2:=right_y(q)-y_coord(q);
//! if dx2=0 then if dy2=0 then
//!   begin dx2:=left_x(r)-x_coord(q); dy2:=left_y(r)-y_coord(q);
//!   if dx2=0 then if dy2=0 then
//!     begin if right_type(r)=endpoint then
//!       begin cur_x:=x_coord(r); cur_y:=y_coord(r);
//!       end
//!     else  begin unskew(x_coord(r),y_coord(r),right_type(r));
//!       skew(cur_x,cur_y,right_type(q));
//!       end;
//!     dx2:=cur_x-x_coord(q); dy2:=cur_y-y_coord(q);
//!     end;  {and they {\sl can't} both be zero}
//!   end;
//! dmax:=abs(dx2);@+if abs(dy2)>dmax then dmax:=abs(dy2);
//! while dmax<fraction_one do
//!   begin double(dmax); double(dx2); double(dy2);
//!   end
//!
//! @ @<Insert additional boundary nodes...@>=
//! loop@+  begin if clockwise then
//!     if o1=1 then o1:=8@+else decr(o1)
//!   else if o1=8 then o1:=1@+else incr(o1);
//!   if o1=o2 then goto done;
//!   new_boundary(s,octant_code[o1]);
//!   s:=link(s); left_octant(s):=right_octant(s);
//!   end
//!
//! @ Now it remains to insert the redundant
//! transition information into the |left_transition|
//! and |right_transition| fields between adjacent octants, in the octant
//! boundary nodes that have just been inserted between |link(p)| and~|q|.
//! The turning number is easily computed from these transitions.
//!
//! @<Fix up the transition fields and adjust the turning number@>=
//! p:=link(p);
//! repeat s:=link(p);
//! o1:=octant_number[right_octant(p)]; o2:=octant_number[left_octant(s)];
//! if abs(o1-o2)=1 then
//!   begin if o2<o1 then o2:=o1;
//!   if odd(o2) then right_transition(p):=axis
//!   else right_transition(p):=diagonal;
//!   end
//! else  begin if o1=8 then incr(turning_number)@+else decr(turning_number);
//!   right_transition(p):=axis;
//!   end;
//! left_transition(s):=right_transition(p);
//! p:=s;
//! until p=q
//!