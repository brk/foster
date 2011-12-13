Strings
=======

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
    mbaAppendByte :: Byte# -> MutableByteArray -> ()
    mbaPutByte :: Word# -> Byte# -> MutableByteArray -> ()
    mbaGetByte :: Word# -> MutableByteArray -> Byte#


