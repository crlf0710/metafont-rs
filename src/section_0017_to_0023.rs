//! @* \[2] The character set.
//! In order to make \MF\ readily portable to a wide variety of
//! computers, all of its input text is converted to an internal eight-bit
//! code that includes standard ASCII, the ``American Standard Code for
//! Information Interchange.''  This conversion is done immediately when each
//! character is read in. Conversely, characters are converted from ASCII to
//! the user's external representation just before they are output to a
//! text file.
//! @^ASCII code@>
//!
//! Such an internal code is relevant to users of \MF\ only with respect to
//! the \&{char} and \&{ASCII} operations, and the comparison of strings.
//!
//! @ Characters of text that have been converted to \MF's internal form
//! are said to be of type |ASCII_code|, which is a subrange of the integers.
//!
//! @<Types...@>=
//! @!ASCII_code=0..255; {eight-bit numbers}
//!
//! @ The original \PASCAL\ compiler was designed in the late 60s, when six-bit
//! character sets were common, so it did not make provision for lowercase
//! letters. Nowadays, of course, we need to deal with both capital and small
//! letters in a convenient way, especially in a program for font design;
//! so the present specification of \MF\ has been written under the assumption
//! that the \PASCAL\ compiler and run-time system permit the use of text files
//! with more than 64 distinguishable characters. More precisely, we assume that
//! the character set contains at least the letters and symbols associated
//! with ASCII codes @'40 through @'176; all of these characters are now
//! available on most computer terminals.
//!
//! Since we are dealing with more characters than were present in the first
//! \PASCAL\ compilers, we have to decide what to call the associated data
//! type. Some \PASCAL s use the original name |char| for the
//! characters in text files, even though there now are more than 64 such
//! characters, while other \PASCAL s consider |char| to be a 64-element
//! subrange of a larger data type that has some other name.
//!
//! In order to accommodate this difference, we shall use the name |text_char|
//! to stand for the data type of the characters that are converted to and
//! from |ASCII_code| when they are input and output. We shall also assume
//! that |text_char| consists of the elements |chr(first_text_char)| through
//! |chr(last_text_char)|, inclusive. The following definitions should be
//! adjusted if necessary.
//! @^system dependencies@>
//!
//! @d text_char == char {the data type of characters in text files}
//! @d first_text_char=0 {ordinal number of the smallest element of |text_char|}
//! @d last_text_char=255 {ordinal number of the largest element of |text_char|}
//!
//! @<Local variables for init...@>=
//! @!i:integer;
//!
//! @ The \MF\ processor converts between ASCII code and
//! the user's external character set by means of arrays |xord| and |xchr|
//! that are analogous to \PASCAL's |ord| and |chr| functions.
//!
//! @<Glob...@>=
//! @!xord: array [text_char] of ASCII_code;
//!   {specifies conversion of input characters}
//! @!xchr: array [ASCII_code] of text_char;
//!   {specifies conversion of output characters}
//!
//! @ Since we are assuming that our \PASCAL\ system is able to read and
//! write the visible characters of standard ASCII (although not
//! necessarily using the ASCII codes to represent them), the following
//! assignment statements initialize the standard part of the |xchr| array
//! properly, without needing any system-dependent changes. On the other
//! hand, it is possible to implement \MF\ with less complete character
//! sets, and in such cases it will be necessary to change something here.
//! @^system dependencies@>
//!
//! @<Set init...@>=
//! xchr[@'40]:=' ';
//! xchr[@'41]:='!';
//! xchr[@'42]:='"';
//! xchr[@'43]:='#';
//! xchr[@'44]:='$';
//! xchr[@'45]:='%';
//! xchr[@'46]:='&';
//! xchr[@'47]:='''';@/
//! xchr[@'50]:='(';
//! xchr[@'51]:=')';
//! xchr[@'52]:='*';
//! xchr[@'53]:='+';
//! xchr[@'54]:=',';
//! xchr[@'55]:='-';
//! xchr[@'56]:='.';
//! xchr[@'57]:='/';@/
//! xchr[@'60]:='0';
//! xchr[@'61]:='1';
//! xchr[@'62]:='2';
//! xchr[@'63]:='3';
//! xchr[@'64]:='4';
//! xchr[@'65]:='5';
//! xchr[@'66]:='6';
//! xchr[@'67]:='7';@/
//! xchr[@'70]:='8';
//! xchr[@'71]:='9';
//! xchr[@'72]:=':';
//! xchr[@'73]:=';';
//! xchr[@'74]:='<';
//! xchr[@'75]:='=';
//! xchr[@'76]:='>';
//! xchr[@'77]:='?';@/
//! xchr[@'100]:='@@';
//! xchr[@'101]:='A';
//! xchr[@'102]:='B';
//! xchr[@'103]:='C';
//! xchr[@'104]:='D';
//! xchr[@'105]:='E';
//! xchr[@'106]:='F';
//! xchr[@'107]:='G';@/
//! xchr[@'110]:='H';
//! xchr[@'111]:='I';
//! xchr[@'112]:='J';
//! xchr[@'113]:='K';
//! xchr[@'114]:='L';
//! xchr[@'115]:='M';
//! xchr[@'116]:='N';
//! xchr[@'117]:='O';@/
//! xchr[@'120]:='P';
//! xchr[@'121]:='Q';
//! xchr[@'122]:='R';
//! xchr[@'123]:='S';
//! xchr[@'124]:='T';
//! xchr[@'125]:='U';
//! xchr[@'126]:='V';
//! xchr[@'127]:='W';@/
//! xchr[@'130]:='X';
//! xchr[@'131]:='Y';
//! xchr[@'132]:='Z';
//! xchr[@'133]:='[';
//! xchr[@'134]:='\';
//! xchr[@'135]:=']';
//! xchr[@'136]:='^';
//! xchr[@'137]:='_';@/
//! xchr[@'140]:='`';
//! xchr[@'141]:='a';
//! xchr[@'142]:='b';
//! xchr[@'143]:='c';
//! xchr[@'144]:='d';
//! xchr[@'145]:='e';
//! xchr[@'146]:='f';
//! xchr[@'147]:='g';@/
//! xchr[@'150]:='h';
//! xchr[@'151]:='i';
//! xchr[@'152]:='j';
//! xchr[@'153]:='k';
//! xchr[@'154]:='l';
//! xchr[@'155]:='m';
//! xchr[@'156]:='n';
//! xchr[@'157]:='o';@/
//! xchr[@'160]:='p';
//! xchr[@'161]:='q';
//! xchr[@'162]:='r';
//! xchr[@'163]:='s';
//! xchr[@'164]:='t';
//! xchr[@'165]:='u';
//! xchr[@'166]:='v';
//! xchr[@'167]:='w';@/
//! xchr[@'170]:='x';
//! xchr[@'171]:='y';
//! xchr[@'172]:='z';
//! xchr[@'173]:='{';
//! xchr[@'174]:='|';
//! xchr[@'175]:='}';
//! xchr[@'176]:='~';@/
//!
//! @ The ASCII code is ``standard'' only to a certain extent, since many
//! computer installations have found it advantageous to have ready access
//! to more than 94 printing characters.  If \MF\ is being used
//! on a garden-variety \PASCAL\ for which only standard ASCII
//! codes will appear in the input and output files, it doesn't really matter
//! what codes are specified in |xchr[0..@'37]|, but the safest policy is to
//! blank everything out by using the code shown below.
//!
//! However, other settings of |xchr| will make \MF\ more friendly on
//! computers that have an extended character set, so that users can type things
//! like `\.^^Z' instead of `\.{<>}'.
//! People with extended character sets can
//! assign codes arbitrarily, giving an |xchr| equivalent to whatever
//! characters the users of \MF\ are allowed to have in their input files.
//! Appropriate changes to \MF's |char_class| table should then be made.
//! (Unlike \TeX, each installation of \MF\ has a fixed assignment of category
//! codes, called the |char_class|.) Such changes make portability of programs
//! more difficult, so they should be introduced cautiously if at all.
//! @^character set dependencies@>
//! @^system dependencies@>
//!
//! @<Set init...@>=
//! for i:=0 to @'37 do xchr[i]:=' ';
//! for i:=@'177 to @'377 do xchr[i]:=' ';
//!
//! @ The following system-independent code makes the |xord| array contain a
//! suitable inverse to the information in |xchr|. Note that if |xchr[i]=xchr[j]|
//! where |i<j<@'177|, the value of |xord[xchr[i]]| will turn out to be
//! |j| or more; hence, standard ASCII code numbers will be used instead of
//! codes below @'40 in case there is a coincidence.
//!
//! @<Set init...@>=
//! for i:=first_text_char to last_text_char do xord[chr(i)]:=@'177;
//! for i:=@'200 to @'377 do xord[xchr[i]]:=i;
//! for i:=0 to @'176 do xord[xchr[i]]:=i;
//!
