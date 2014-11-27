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

Efficient Representations
+++++++++++++++++++++++++

libc++ implements strings like so::

         { [ size_cap  ][ size_size ][  ptr_data ] } (long)
   union { [chrsz][ data                         ] } (short)
         { [    words                            ] } (raw)

   A string is either long or short; the (raw) variant is used only for
   efficient initialization and so on. A bit stolen from short.chr_size
   determines whether the string is long or short.

   On a 64-bit platform, strings of up to (3 * 8) - 2 = 22 bytes
   do not require allocation.

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


