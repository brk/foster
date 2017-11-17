Symlink these two files from $PINROOT/source/tools/Memory

You can then do (from the Memory directory)
  make obj-intel64/memfootprint.so

and then run a program like
  $PINROOT/pin -t $PINROOT/source/tools/Memory/obj-intel64/memfootprint.so -- PROG

