Strings
=======

Syntax
++++++

We mostly adopt Python's string syntax::

     "two \n lines"
    r"one \n line with a backslash"
    """triple quotes"""
    r'''or triple ticks'''
    """multi-line
       strings ok"""

Unicode escapes are currently parsed but not interpreted; I'd like to have a
better story for these before committing to anything more concrete.
The above literals all have type ``Text``. There are also byte-array literals,
which have the same escape syntax, but extended with hex escapes::

    b"the\x20space\x20between"    // b"the space between"
    b"""ab
    cd"""                         // b"abcd" ; newline not included

Byte array literals have type ``Array Int8``. We could make them be ``Bytes``,
but the downside is that we then have to teach the compiler about another
hard-coded type. The main advantages are that we encourage higher-level programming,
and also we can go from ``ByteFragment`` to a byte array without allocating, but
it seems... trickier... to guarantee that ``bytesOfRawArray b"lah"`` will statically
allocate the ``Bytes`` wrapper in addition to the bytes thsem

For text literals, code generation will emit a static array and a call to the
implictly-inserted function ``TextFragment`` with an automatically-computed length.
Currently this means that each "dynamic execution" of a text literal results in a
heap allocated pair, although the ``TextFragment`` constructor could certainly be
statically allocated in the future.

Byte arrays are statically allocated.

Strings vs Bytes
++++++++++++++++

Essentially, how seriously are we going to take Unicode
(which is to say, issues of internationalization)?

An incomplete list of the issues that are harder to deal with "properly" in Unicode:

* Characters vs columns vs graphemes vs grapheme clusters...
* Normalization (NFC vs NFKD vs ...)
  * And interaction with external systems (FSes) that have their own opinions...
* Comparison/equivalence
* Sorting/collation
* Case conversion,
* Splitting and decomposition
* Regex matching
* Substring searching
* Numerical formatting
* Equivalence testing (compatibility vs canonical)
  * Locale-based...
* Unicode properties (Lowercase vs Lower/Alphabetic/Letter/Lu/Ll vs Lowercase_Letter)
  * ``\s`` vs ``[\h\v]``
  * ``\r?\n`` vs ``\R``

Meaty Links
~~~~~~~~~~~

http://eli.thegreenplace.net/2012/01/30/the-bytesstr-dichotomy-in-python-3
http://www.diveintopython3.net/strings.html
http://www.tbray.org/ongoing/When/200x/2003/04/06/Unicode
https://stackoverflow.com/questions/6162484/why-does-modern-perl-avoid-utf-8-by-default

http://search.cpan.org/~nezumi/Unicode-LineBreak-2014.06/lib/Unicode/LineBreak.pod
http://search.cpan.org/~nezumi/Unicode-LineBreak-2014.06/lib/Unicode/GCString.pod

Misc Links
~~~~~~~~~~
http://stackoverflow.com/questions/8841290/do-latin-capital-letter-i-u0049-and-roman-numeral-one-u2160-have-unicode-c
http://icu-project.org/apiref/icu4j/com/ibm/icu/text/SpoofChecker.html
http://en.wikibooks.org/wiki/Perl_Programming/Unicode_UTF-8

http://search.cpan.org/~cfaerber/Unicode-Stringprep-1.105/lib/Unicode/Stringprep.pm
http://stackoverflow.com/questions/4304928/unicode-equivalents-for-w-and-b-in-java-regular-expressions/4307261#4307261
http://stackoverflow.com/questions/4246077/matching-numbers-with-regular-expressions-only-digits-and-commas/4247184#4247184
http://stackoverflow.com/questions/5697171/regex-what-is-incombiningdiacriticalmarks/5697575#5697575

http://www.joelonsoftware.com/articles/Unicode.html

Efficient Representations
+++++++++++++++++++++++++

libc++ implements strings like so::

         { [ size_cap  ][ size_size ][  ptr_data ] } (long)
   union { [chrsz][ data                         ] } (short)
         { [    words                            ] } (raw)

A string is either long or short; the (raw) variant is used only for
efficient initialization and so on. A bit stolen from ``short.chr_size``
determines whether the string is long or short.

On a 64-bit platform, strings of up to (3 * 8) - 2 = 22 bytes
do not require allocation.

The downside, of course, is that strings are not pointer-sized and thus
cannot be used directly in polymorphic code. Strings are often (usually?)
passed by reference anyhow; it's unclear to me what the performance tradeoff
is between such double-indirection in the (long) case and reduced allocation
in the (short) case.

What we might like for Foster::

    type
    case String
      of $StringFragment UTF8Array Int32      // UTF-8 encoded chars, cached length
      of $StringConcat   String  String Int32 // substrings, total length

    //of $StringSlice    String  Int32# Int32#  // base, offset, length
    //of $StringInlinedC Int32 (ByteArrayC# 40) // statically known capacity
    //of $StringInlined   ByteArray#            // not-statically-known length

    stringConcat :: String -> String -> String
    stringLength :: String -> Word#
    stringPrintStdout :: String -> ()
    stringPrintStderr :: String -> ()

    primPrintBytesStdout :: (Array Int8) -> Int32 -> ()
    primPrintBytesStderr :: (Array Int8) -> Int32 -> ()

    type ByteArray = opaque

    newByteArray :: Word# -> ByteArray


    type MutableByteArray = opaque

    mutableByteArrayNew :: Word# -> MutableByteArray
    mbaAppendByte  :: Byte#            -> MutableByteArray -> ()
    mbaAppendBytes :: MutableByteArray -> MutableByteArray -> ()
    mbaPutByte :: Word# -> Byte# -> MutableByteArray -> ()
    mbaGetByte :: Word# -> MutableByteArray -> Byte#


