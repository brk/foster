Runtime
=======

Dependencies
------------

The scheduling timer uses:

* ``base/threading/simple_thread.h``
* ``obj/runtime.h`` and ``'objc/objc-runtime.h`` on Mac OS.

Parsing runtime options from JSON syntax currently involves:

* ``base/json/json_reader.h``
* ``strncmp``, ``strlen``, ``sstream``

Coroutines currently use (well, ``#ifdef``'ed out):

* ``base/synchronization/lock.h``

``foster__assert`` uses:

* ``fprintf``, ``fflush``, ``exit``

``libfoster_posix.cpp`` uses:

* ``fread``, ``feof``, ``read``, ``write``, ``errno``, ``strncpy``, ``close``, ``ioctl``,
  ``memset``, ``strncpy``, ``close``, ``ioctl``, ``ifreq``

``libfoster.cpp`` uses:

* ``base::PlatformThread::Sleep``, ``base::SimpleThread::Join``, ``AtomicBool``
* ``fprintf``, ``memcpy``
* On Mac OS: ``objc_msgSend``, ``sel_registerName``, ``objc_getClass``, ``class_createInstance``
* ``__foster_getticks`` (from ``third_party/fftw/cycle_wrapper.c``)

``foster_gc.cpp`` uses:

* ``malloc``, ``free``, ``new``, ``fprintf``, ``fflush``, ``std::map``
* ``offsetof``,  ``getrlimit``, ``backtrace``, ``memset``
* ``base/time.h``, ``base/metrics/histogram.h``, ``base/metrics/statistics_recorder.h``
