//! @* \[12] The command codes.
//! Before we can go much further, we need to define symbolic names for the internal
//! code numbers that represent the various commands obeyed by \MF. These codes
//! are somewhat arbitrary, but not completely so. For example,
//! some codes have been made adjacent so that |case| statements in the
//! program need not consider cases that are widely spaced, or so that |case|
//! statements can be replaced by |if| statements. A command can begin an
//! expression if and only if its code lies between |min_primary_command| and
//! |max_primary_command|, inclusive. The first token of a statement that doesn't
//! begin with an expression has a command code between |min_command| and
//! |max_statement_command|, inclusive. The ordering of the highest-numbered
//! commands (|comma<semicolon<end_group<stop|) is crucial for the parsing
//! and error-recovery methods of this program.
//!
//! At any rate, here is the list, for future reference.
//!
//! @d if_test=1 {conditional text (\&{if})}
//! @d fi_or_else=2 {delimiters for conditionals (\&{elseif}, \&{else}, \&{fi})}
//! @d input=3 {input a source file (\&{input}, \&{endinput})}
//! @d iteration=4 {iterate (\&{for}, \&{forsuffixes}, \&{forever}, \&{endfor})}
//! @d repeat_loop=5 {special command substituted for \&{endfor}}
//! @d exit_test=6 {premature exit from a loop (\&{exitif})}
//! @d relax=7 {do nothing (\.{\char`\\})}
//! @d scan_tokens=8 {put a string into the input buffer}
//! @d expand_after=9 {look ahead one token}
//! @d defined_macro=10 {a macro defined by the user}
//! @d min_command=defined_macro+1
//! @d display_command=11 {online graphic output (\&{display})}
//! @d save_command=12 {save a list of tokens (\&{save})}
//! @d interim_command=13 {save an internal quantity (\&{interim})}
//! @d let_command=14 {redefine a symbolic token (\&{let})}
//! @d new_internal=15 {define a new internal quantity (\&{newinternal})}
//! @d macro_def=16 {define a macro (\&{def}, \&{vardef}, etc.)}
//! @d ship_out_command=17 {output a character (\&{shipout})}
//! @d add_to_command=18 {add to edges (\&{addto})}
//! @d cull_command=19 {cull and normalize edges (\&{cull})}
//! @d tfm_command=20 {command for font metric info (\&{ligtable}, etc.)}
//! @d protection_command=21 {set protection flag (\&{outer}, \&{inner})}
//! @d show_command=22 {diagnostic output (\&{show}, \&{showvariable}, etc.)}
//! @d mode_command=23 {set interaction level (\&{batchmode}, etc.)}
//! @d random_seed=24 {initialize random number generator (\&{randomseed})}
//! @d message_command=25 {communicate to user (\&{message}, \&{errmessage})}
//! @d every_job_command=26 {designate a starting token (\&{everyjob})}
//! @d delimiters=27 {define a pair of delimiters (\&{delimiters})}
//! @d open_window=28 {define a window on the screen (\&{openwindow})}
//! @d special_command=29 {output special info (\&{special}, \&{numspecial})}
//! @d type_name=30 {declare a type (\&{numeric}, \&{pair}, etc.)}
//! @d max_statement_command=type_name
//! @d min_primary_command=type_name
//! @d left_delimiter=31 {the left delimiter of a matching pair}
//! @d begin_group=32 {beginning of a group (\&{begingroup})}
//! @d nullary=33 {an operator without arguments (e.g., \&{normaldeviate})}
//! @d unary=34 {an operator with one argument (e.g., \&{sqrt})}
//! @d str_op=35 {convert a suffix to a string (\&{str})}
//! @d cycle=36 {close a cyclic path (\&{cycle})}
//! @d primary_binary=37 {binary operation taking `\&{of}' (e.g., \&{point})}
//! @d capsule_token=38 {a value that has been put into a token list}
//! @d string_token=39 {a string constant (e.g., |"hello"|)}
//! @d internal_quantity=40 {internal numeric parameter (e.g., \&{pausing})}
//! @d min_suffix_token=internal_quantity
//! @d tag_token=41 {a symbolic token without a primitive meaning}
//! @d numeric_token=42 {a numeric constant (e.g., \.{3.14159})}
//! @d max_suffix_token=numeric_token
//! @d plus_or_minus=43 {either `\.+' or `\.-'}
//! @d max_primary_command=plus_or_minus {should also be |numeric_token+1|}
//! @d min_tertiary_command=plus_or_minus
//! @d tertiary_secondary_macro=44 {a macro defined by \&{secondarydef}}
//! @d tertiary_binary=45 {an operator at the tertiary level (e.g., `\.{++}')}
//! @d max_tertiary_command=tertiary_binary
//! @d left_brace=46 {the operator `\.{\char`\{}'}
//! @d min_expression_command=left_brace
//! @d path_join=47 {the operator `\.{..}'}
//! @d ampersand=48 {the operator `\.\&'}
//! @d expression_tertiary_macro=49 {a macro defined by \&{tertiarydef}}
//! @d expression_binary=50 {an operator at the expression level (e.g., `\.<')}
//! @d equals=51 {the operator `\.='}
//! @d max_expression_command=equals
//! @d and_command=52 {the operator `\&{and}'}
//! @d min_secondary_command=and_command
//! @d secondary_primary_macro=53 {a macro defined by \&{primarydef}}
//! @d slash=54 {the operator `\./'}
//! @d secondary_binary=55 {an operator at the binary level (e.g., \&{shifted})}
//! @d max_secondary_command=secondary_binary
//! @d param_type=56 {type of parameter (\&{primary}, \&{expr}, \&{suffix}, etc.)}
//! @d controls=57 {specify control points explicitly (\&{controls})}
//! @d tension=58 {specify tension between knots (\&{tension})}
//! @d at_least=59 {bounded tension value (\&{atleast})}
//! @d curl_command=60 {specify curl at an end knot (\&{curl})}
//! @d macro_special=61 {special macro operators (\&{quote}, \.{\#\AT!}, etc.)}
//! @d right_delimiter=62 {the right delimiter of a matching pair}
//! @d left_bracket=63 {the operator `\.['}
//! @d right_bracket=64 {the operator `\.]'}
//! @d right_brace=65 {the operator `\.{\char`\}}'}
//! @d with_option=66 {option for filling (\&{withpen}, \&{withweight})}
//! @d cull_op=67 {the operator `\&{keeping}' or `\&{dropping}'}
//! @d thing_to_add=68
//!   {variant of \&{addto} (\&{contour}, \&{doublepath}, \&{also})}
//! @d of_token=69 {the operator `\&{of}'}
//! @d from_token=70 {the operator `\&{from}'}
//! @d to_token=71 {the operator `\&{to}'}
//! @d at_token=72 {the operator `\&{at}'}
//! @d in_window=73 {the operator `\&{inwindow}'}
//! @d step_token=74 {the operator `\&{step}'}
//! @d until_token=75 {the operator `\&{until}'}
//! @d lig_kern_token=76
//!   {the operators `\&{kern}' and `\.{=:}' and `\.{=:\char'174}', etc.}
//! @d assignment=77 {the operator `\.{:=}'}
//! @d skip_to=78 {the operation `\&{skipto}'}
//! @d bchar_label=79 {the operator `\.{\char'174\char'174:}'}
//! @d double_colon=80 {the operator `\.{::}'}
//! @d colon=81 {the operator `\.:'}
//! @#
//! @d comma=82 {the operator `\.,', must be |colon+1|}
//! @d end_of_statement==cur_cmd>comma
//! @d semicolon=83 {the operator `\.;', must be |comma+1|}
//! @d end_group=84 {end a group (\&{endgroup}), must be |semicolon+1|}
//! @d stop=85 {end a job (\&{end}, \&{dump}), must be |end_group+1|}
//! @d max_command_code=stop
//! @d outer_tag=max_command_code+1 {protection code added to command code}
//!
//! @<Types...@>=
//! @!command_code=1..max_command_code;
//!
//! @ Variables and capsules in \MF\ have a variety of ``types,''
//! distinguished by the following code numbers:
//!
//! @d undefined=0 {no type has been declared}
//! @d unknown_tag=1 {this constant is added to certain type codes below}
//! @d vacuous=1 {no expression was present}
//! @d boolean_type=2 {\&{boolean} with a known value}
//! @d unknown_boolean=boolean_type+unknown_tag
//! @d string_type=4 {\&{string} with a known value}
//! @d unknown_string=string_type+unknown_tag
//! @d pen_type=6 {\&{pen} with a known value}
//! @d unknown_pen=pen_type+unknown_tag
//! @d future_pen=8 {subexpression that will become a \&{pen} at a higher level}
//! @d path_type=9 {\&{path} with a known value}
//! @d unknown_path=path_type+unknown_tag
//! @d picture_type=11 {\&{picture} with a known value}
//! @d unknown_picture=picture_type+unknown_tag
//! @d transform_type=13 {\&{transform} variable or capsule}
//! @d pair_type=14 {\&{pair} variable or capsule}
//! @d numeric_type=15 {variable that has been declared \&{numeric} but not used}
//! @d known=16 {\&{numeric} with a known value}
//! @d dependent=17 {a linear combination with |fraction| coefficients}
//! @d proto_dependent=18 {a linear combination with |scaled| coefficients}
//! @d independent=19 {\&{numeric} with unknown value}
//! @d token_list=20 {variable name or suffix argument or text argument}
//! @d structured=21 {variable with subscripts and attributes}
//! @d unsuffixed_macro=22 {variable defined with \&{vardef} but no \.{\AT!\#}}
//! @d suffixed_macro=23 {variable defined with \&{vardef} and \.{\AT!\#}}
//! @#
//! @d unknown_types==unknown_boolean,unknown_string,
//!   unknown_pen,unknown_picture,unknown_path
//!
//! @<Basic printing procedures@>=
//! procedure print_type(@!t:small_number);
//! begin case t of
//! vacuous:print("vacuous");
//! boolean_type:print("boolean");
//! unknown_boolean:print("unknown boolean");
//! string_type:print("string");
//! unknown_string:print("unknown string");
//! pen_type:print("pen");
//! unknown_pen:print("unknown pen");
//! future_pen:print("future pen");
//! path_type:print("path");
//! unknown_path:print("unknown path");
//! picture_type:print("picture");
//! unknown_picture:print("unknown picture");
//! transform_type:print("transform");
//! pair_type:print("pair");
//! known:print("known numeric");
//! dependent:print("dependent");
//! proto_dependent:print("proto-dependent");
//! numeric_type:print("numeric");
//! independent:print("independent");
//! token_list:print("token list");
//! structured:print("structured");
//! unsuffixed_macro:print("unsuffixed macro");
//! suffixed_macro:print("suffixed macro");
//! othercases print("undefined")
//! endcases;
//! end;
//!
//! @ Values inside \MF\ are stored in two-word nodes that have a |name_type|
//! as well as a |type|. The possibilities for |name_type| are defined
//! here; they will be explained in more detail later.
//!
//! @d root=0 {|name_type| at the top level of a variable}
//! @d saved_root=1 {same, when the variable has been saved}
//! @d structured_root=2 {|name_type| where a |structured| branch occurs}
//! @d subscr=3 {|name_type| in a subscript node}
//! @d attr=4 {|name_type| in an attribute node}
//! @d x_part_sector=5 {|name_type| in the \&{xpart} of a node}
//! @d y_part_sector=6 {|name_type| in the \&{ypart} of a node}
//! @d xx_part_sector=7 {|name_type| in the \&{xxpart} of a node}
//! @d xy_part_sector=8 {|name_type| in the \&{xypart} of a node}
//! @d yx_part_sector=9 {|name_type| in the \&{yxpart} of a node}
//! @d yy_part_sector=10 {|name_type| in the \&{yypart} of a node}
//! @d capsule=11 {|name_type| in stashed-away subexpressions}
//! @d token=12 {|name_type| in a numeric token or string token}
//!
//! @ Primitive operations that produce values have a secondary identification
//! code in addition to their command code; it's something like genera and species.
//! For example, `\.*' has the command code |primary_binary|, and its
//! secondary identification is |times|. The secondary codes start at 30 so that
//! they don't overlap with the type codes; some type codes (e.g., |string_type|)
//! are used as operators as well as type identifications.
//!
//! @d true_code=30 {operation code for \.{true}}
//! @d false_code=31 {operation code for \.{false}}
//! @d null_picture_code=32 {operation code for \.{nullpicture}}
//! @d null_pen_code=33 {operation code for \.{nullpen}}
//! @d job_name_op=34 {operation code for \.{jobname}}
//! @d read_string_op=35 {operation code for \.{readstring}}
//! @d pen_circle=36 {operation code for \.{pencircle}}
//! @d normal_deviate=37 {operation code for \.{normaldeviate}}
//! @d odd_op=38 {operation code for \.{odd}}
//! @d known_op=39 {operation code for \.{known}}
//! @d unknown_op=40 {operation code for \.{unknown}}
//! @d not_op=41 {operation code for \.{not}}
//! @d decimal=42 {operation code for \.{decimal}}
//! @d reverse=43 {operation code for \.{reverse}}
//! @d make_path_op=44 {operation code for \.{makepath}}
//! @d make_pen_op=45 {operation code for \.{makepen}}
//! @d total_weight_op=46 {operation code for \.{totalweight}}
//! @d oct_op=47 {operation code for \.{oct}}
//! @d hex_op=48 {operation code for \.{hex}}
//! @d ASCII_op=49 {operation code for \.{ASCII}}
//! @d char_op=50 {operation code for \.{char}}
//! @d length_op=51 {operation code for \.{length}}
//! @d turning_op=52 {operation code for \.{turningnumber}}
//! @d x_part=53 {operation code for \.{xpart}}
//! @d y_part=54 {operation code for \.{ypart}}
//! @d xx_part=55 {operation code for \.{xxpart}}
//! @d xy_part=56 {operation code for \.{xypart}}
//! @d yx_part=57 {operation code for \.{yxpart}}
//! @d yy_part=58 {operation code for \.{yypart}}
//! @d sqrt_op=59 {operation code for \.{sqrt}}
//! @d m_exp_op=60 {operation code for \.{mexp}}
//! @d m_log_op=61 {operation code for \.{mlog}}
//! @d sin_d_op=62 {operation code for \.{sind}}
//! @d cos_d_op=63 {operation code for \.{cosd}}
//! @d floor_op=64 {operation code for \.{floor}}
//! @d uniform_deviate=65 {operation code for \.{uniformdeviate}}
//! @d char_exists_op=66 {operation code for \.{charexists}}
//! @d angle_op=67 {operation code for \.{angle}}
//! @d cycle_op=68 {operation code for \.{cycle}}
//! @d plus=69 {operation code for \.+}
//! @d minus=70 {operation code for \.-}
//! @d times=71 {operation code for \.*}
//! @d over=72 {operation code for \./}
//! @d pythag_add=73 {operation code for \.{++}}
//! @d pythag_sub=74 {operation code for \.{+-+}}
//! @d or_op=75 {operation code for \.{or}}
//! @d and_op=76 {operation code for \.{and}}
//! @d less_than=77 {operation code for \.<}
//! @d less_or_equal=78 {operation code for \.{<=}}
//! @d greater_than=79 {operation code for \.>}
//! @d greater_or_equal=80 {operation code for \.{>=}}
//! @d equal_to=81 {operation code for \.=}
//! @d unequal_to=82 {operation code for \.{<>}}
//! @d concatenate=83 {operation code for \.\&}
//! @d rotated_by=84 {operation code for \.{rotated}}
//! @d slanted_by=85 {operation code for \.{slanted}}
//! @d scaled_by=86 {operation code for \.{scaled}}
//! @d shifted_by=87 {operation code for \.{shifted}}
//! @d transformed_by=88 {operation code for \.{transformed}}
//! @d x_scaled=89 {operation code for \.{xscaled}}
//! @d y_scaled=90 {operation code for \.{yscaled}}
//! @d z_scaled=91 {operation code for \.{zscaled}}
//! @d intersect=92 {operation code for \.{intersectiontimes}}
//! @d double_dot=93 {operation code for improper \.{..}}
//! @d substring_of=94 {operation code for \.{substring}}
//! @d min_of=substring_of
//! @d subpath_of=95 {operation code for \.{subpath}}
//! @d direction_time_of=96 {operation code for \.{directiontime}}
//! @d point_of=97 {operation code for \.{point}}
//! @d precontrol_of=98 {operation code for \.{precontrol}}
//! @d postcontrol_of=99 {operation code for \.{postcontrol}}
//! @d pen_offset_of=100 {operation code for \.{penoffset}}
//!
//! @p procedure print_op(@!c:quarterword);
//! begin if c<=numeric_type then print_type(c)
//! else case c of
//! true_code:print("true");
//! false_code:print("false");
//! null_picture_code:print("nullpicture");
//! null_pen_code:print("nullpen");
//! job_name_op:print("jobname");
//! read_string_op:print("readstring");
//! pen_circle:print("pencircle");
//! normal_deviate:print("normaldeviate");
//! odd_op:print("odd");
//! known_op:print("known");
//! unknown_op:print("unknown");
//! not_op:print("not");
//! decimal:print("decimal");
//! reverse:print("reverse");
//! make_path_op:print("makepath");
//! make_pen_op:print("makepen");
//! total_weight_op:print("totalweight");
//! oct_op:print("oct");
//! hex_op:print("hex");
//! ASCII_op:print("ASCII");
//! char_op:print("char");
//! length_op:print("length");
//! turning_op:print("turningnumber");
//! x_part:print("xpart");
//! y_part:print("ypart");
//! xx_part:print("xxpart");
//! xy_part:print("xypart");
//! yx_part:print("yxpart");
//! yy_part:print("yypart");
//! sqrt_op:print("sqrt");
//! m_exp_op:print("mexp");
//! m_log_op:print("mlog");
//! sin_d_op:print("sind");
//! cos_d_op:print("cosd");
//! floor_op:print("floor");
//! uniform_deviate:print("uniformdeviate");
//! char_exists_op:print("charexists");
//! angle_op:print("angle");
//! cycle_op:print("cycle");
//! plus:print_char("+");
//! minus:print_char("-");
//! times:print_char("*");
//! over:print_char("/");
//! pythag_add:print("++");
//! pythag_sub:print("+-+");
//! or_op:print("or");
//! and_op:print("and");
//! less_than:print_char("<");
//! less_or_equal:print("<=");
//! greater_than:print_char(">");
//! greater_or_equal:print(">=");
//! equal_to:print_char("=");
//! unequal_to:print("<>");
//! concatenate:print("&");
//! rotated_by:print("rotated");
//! slanted_by:print("slanted");
//! scaled_by:print("scaled");
//! shifted_by:print("shifted");
//! transformed_by:print("transformed");
//! x_scaled:print("xscaled");
//! y_scaled:print("yscaled");
//! z_scaled:print("zscaled");
//! intersect:print("intersectiontimes");
//! substring_of:print("substring");
//! subpath_of:print("subpath");
//! direction_time_of:print("directiontime");
//! point_of:print("point");
//! precontrol_of:print("precontrol");
//! postcontrol_of:print("postcontrol");
//! pen_offset_of:print("penoffset");
//! othercases print("..")
//! endcases;
//! end;
//!
//! @ \MF\ also has a bunch of internal parameters that a user might want to
//! fuss with. Every such parameter has an identifying code number, defined here.
//!
//! @d tracing_titles=1 {show titles online when they appear}
//! @d tracing_equations=2 {show each variable when it becomes known}
//! @d tracing_capsules=3 {show capsules too}
//! @d tracing_choices=4 {show the control points chosen for paths}
//! @d tracing_specs=5 {show subdivision of paths into octants before digitizing}
//! @d tracing_pens=6 {show details of pens that are made}
//! @d tracing_commands=7 {show commands and operations before they are performed}
//! @d tracing_restores=8 {show when a variable or internal is restored}
//! @d tracing_macros=9 {show macros before they are expanded}
//! @d tracing_edges=10 {show digitized edges as they are computed}
//! @d tracing_output=11 {show digitized edges as they are output}
//! @d tracing_stats=12 {show memory usage at end of job}
//! @d tracing_online=13 {show long diagnostics on terminal and in the log file}
//! @d year=14 {the current year (e.g., 1984)}
//! @d month=15 {the current month (e.g., 3 $\equiv$ March)}
//! @d day=16 {the current day of the month}
//! @d time=17 {the number of minutes past midnight when this job started}
//! @d char_code=18 {the number of the next character to be output}
//! @d char_ext=19 {the extension code of the next character to be output}
//! @d char_wd=20 {the width of the next character to be output}
//! @d char_ht=21 {the height of the next character to be output}
//! @d char_dp=22 {the depth of the next character to be output}
//! @d char_ic=23 {the italic correction of the next character to be output}
//! @d char_dx=24 {the device's $x$ movement for the next character, in pixels}
//! @d char_dy=25 {the device's $y$ movement for the next character, in pixels}
//! @d design_size=26 {the unit of measure used for |char_wd..char_ic|, in points}
//! @d hppp=27 {the number of horizontal pixels per point}
//! @d vppp=28 {the number of vertical pixels per point}
//! @d x_offset=29 {horizontal displacement of shipped-out characters}
//! @d y_offset=30 {vertical displacement of shipped-out characters}
//! @d pausing=31 {positive to display lines on the terminal before they are read}
//! @d showstopping=32 {positive to stop after each \&{show} command}
//! @d fontmaking=33 {positive if font metric output is to be produced}
//! @d proofing=34 {positive for proof mode, negative to suppress output}
//! @d smoothing=35 {positive if moves are to be ``smoothed''}
//! @d autorounding=36 {controls path modification to ``good'' points}
//! @d granularity=37 {autorounding uses this pixel size}
//! @d fillin=38 {extra darkness of diagonal lines}
//! @d turning_check=39 {controls reorientation of clockwise paths}
//! @d warning_check=40 {controls error message when variable value is large}
//! @d boundary_char=41 {the boundary character for ligatures}
//! @d max_given_internal=41
//!
//! @<Glob...@>=
//! @!internal:array[1..max_internal] of scaled;
//!   {the values of internal quantities}
//! @!int_name:array[1..max_internal] of str_number;
//!   {their names}
//! @!int_ptr:max_given_internal..max_internal;
//!   {the maximum internal quantity defined so far}
//!
//! @ @<Set init...@>=
//! for k:=1 to max_given_internal do internal[k]:=0;
//! int_ptr:=max_given_internal;
//!
//! @ The symbolic names for internal quantities are put into \MF's hash table
//! by using a routine called |primitive|, which will be defined later. Let us
//! enter them now, so that we don't have to list all those names again
//! anywhere else.
//!
//! @<Put each of \MF's primitives into the hash table@>=
//! primitive("tracingtitles",internal_quantity,tracing_titles);@/
//! @!@:tracingtitles_}{\&{tracingtitles} primitive@>
//! primitive("tracingequations",internal_quantity,tracing_equations);@/
//! @!@:tracing_equations_}{\&{tracingequations} primitive@>
//! primitive("tracingcapsules",internal_quantity,tracing_capsules);@/
//! @!@:tracing_capsules_}{\&{tracingcapsules} primitive@>
//! primitive("tracingchoices",internal_quantity,tracing_choices);@/
//! @!@:tracing_choices_}{\&{tracingchoices} primitive@>
//! primitive("tracingspecs",internal_quantity,tracing_specs);@/
//! @!@:tracing_specs_}{\&{tracingspecs} primitive@>
//! primitive("tracingpens",internal_quantity,tracing_pens);@/
//! @!@:tracing_pens_}{\&{tracingpens} primitive@>
//! primitive("tracingcommands",internal_quantity,tracing_commands);@/
//! @!@:tracing_commands_}{\&{tracingcommands} primitive@>
//! primitive("tracingrestores",internal_quantity,tracing_restores);@/
//! @!@:tracing_restores_}{\&{tracingrestores} primitive@>
//! primitive("tracingmacros",internal_quantity,tracing_macros);@/
//! @!@:tracing_macros_}{\&{tracingmacros} primitive@>
//! primitive("tracingedges",internal_quantity,tracing_edges);@/
//! @!@:tracing_edges_}{\&{tracingedges} primitive@>
//! primitive("tracingoutput",internal_quantity,tracing_output);@/
//! @!@:tracing_output_}{\&{tracingoutput} primitive@>
//! primitive("tracingstats",internal_quantity,tracing_stats);@/
//! @!@:tracing_stats_}{\&{tracingstats} primitive@>
//! primitive("tracingonline",internal_quantity,tracing_online);@/
//! @!@:tracing_online_}{\&{tracingonline} primitive@>
//! primitive("year",internal_quantity,year);@/
//! @!@:year_}{\&{year} primitive@>
//! primitive("month",internal_quantity,month);@/
//! @!@:month_}{\&{month} primitive@>
//! primitive("day",internal_quantity,day);@/
//! @!@:day_}{\&{day} primitive@>
//! primitive("time",internal_quantity,time);@/
//! @!@:time_}{\&{time} primitive@>
//! primitive("charcode",internal_quantity,char_code);@/
//! @!@:char_code_}{\&{charcode} primitive@>
//! primitive("charext",internal_quantity,char_ext);@/
//! @!@:char_ext_}{\&{charext} primitive@>
//! primitive("charwd",internal_quantity,char_wd);@/
//! @!@:char_wd_}{\&{charwd} primitive@>
//! primitive("charht",internal_quantity,char_ht);@/
//! @!@:char_ht_}{\&{charht} primitive@>
//! primitive("chardp",internal_quantity,char_dp);@/
//! @!@:char_dp_}{\&{chardp} primitive@>
//! primitive("charic",internal_quantity,char_ic);@/
//! @!@:char_ic_}{\&{charic} primitive@>
//! primitive("chardx",internal_quantity,char_dx);@/
//! @!@:char_dx_}{\&{chardx} primitive@>
//! primitive("chardy",internal_quantity,char_dy);@/
//! @!@:char_dy_}{\&{chardy} primitive@>
//! primitive("designsize",internal_quantity,design_size);@/
//! @!@:design_size_}{\&{designsize} primitive@>
//! primitive("hppp",internal_quantity,hppp);@/
//! @!@:hppp_}{\&{hppp} primitive@>
//! primitive("vppp",internal_quantity,vppp);@/
//! @!@:vppp_}{\&{vppp} primitive@>
//! primitive("xoffset",internal_quantity,x_offset);@/
//! @!@:x_offset_}{\&{xoffset} primitive@>
//! primitive("yoffset",internal_quantity,y_offset);@/
//! @!@:y_offset_}{\&{yoffset} primitive@>
//! primitive("pausing",internal_quantity,pausing);@/
//! @!@:pausing_}{\&{pausing} primitive@>
//! primitive("showstopping",internal_quantity,showstopping);@/
//! @!@:showstopping_}{\&{showstopping} primitive@>
//! primitive("fontmaking",internal_quantity,fontmaking);@/
//! @!@:fontmaking_}{\&{fontmaking} primitive@>
//! primitive("proofing",internal_quantity,proofing);@/
//! @!@:proofing_}{\&{proofing} primitive@>
//! primitive("smoothing",internal_quantity,smoothing);@/
//! @!@:smoothing_}{\&{smoothing} primitive@>
//! primitive("autorounding",internal_quantity,autorounding);@/
//! @!@:autorounding_}{\&{autorounding} primitive@>
//! primitive("granularity",internal_quantity,granularity);@/
//! @!@:granularity_}{\&{granularity} primitive@>
//! primitive("fillin",internal_quantity,fillin);@/
//! @!@:fillin_}{\&{fillin} primitive@>
//! primitive("turningcheck",internal_quantity,turning_check);@/
//! @!@:turning_check_}{\&{turningcheck} primitive@>
//! primitive("warningcheck",internal_quantity,warning_check);@/
//! @!@:warning_check_}{\&{warningcheck} primitive@>
//! primitive("boundarychar",internal_quantity,boundary_char);@/
//! @!@:boundary_char_}{\&{boundarychar} primitive@>
//!
//! @ Well, we do have to list the names one more time, for use in symbolic
//! printouts.
//!
//! @<Initialize table...@>=
//! int_name[tracing_titles]:="tracingtitles";
//! int_name[tracing_equations]:="tracingequations";
//! int_name[tracing_capsules]:="tracingcapsules";
//! int_name[tracing_choices]:="tracingchoices";
//! int_name[tracing_specs]:="tracingspecs";
//! int_name[tracing_pens]:="tracingpens";
//! int_name[tracing_commands]:="tracingcommands";
//! int_name[tracing_restores]:="tracingrestores";
//! int_name[tracing_macros]:="tracingmacros";
//! int_name[tracing_edges]:="tracingedges";
//! int_name[tracing_output]:="tracingoutput";
//! int_name[tracing_stats]:="tracingstats";
//! int_name[tracing_online]:="tracingonline";
//! int_name[year]:="year";
//! int_name[month]:="month";
//! int_name[day]:="day";
//! int_name[time]:="time";
//! int_name[char_code]:="charcode";
//! int_name[char_ext]:="charext";
//! int_name[char_wd]:="charwd";
//! int_name[char_ht]:="charht";
//! int_name[char_dp]:="chardp";
//! int_name[char_ic]:="charic";
//! int_name[char_dx]:="chardx";
//! int_name[char_dy]:="chardy";
//! int_name[design_size]:="designsize";
//! int_name[hppp]:="hppp";
//! int_name[vppp]:="vppp";
//! int_name[x_offset]:="xoffset";
//! int_name[y_offset]:="yoffset";
//! int_name[pausing]:="pausing";
//! int_name[showstopping]:="showstopping";
//! int_name[fontmaking]:="fontmaking";
//! int_name[proofing]:="proofing";
//! int_name[smoothing]:="smoothing";
//! int_name[autorounding]:="autorounding";
//! int_name[granularity]:="granularity";
//! int_name[fillin]:="fillin";
//! int_name[turning_check]:="turningcheck";
//! int_name[warning_check]:="warningcheck";
//! int_name[boundary_char]:="boundarychar";
//!
