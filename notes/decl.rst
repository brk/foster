Give nicer names for C symbols (part of module interface),
along with the symbol's type::

        declare plusInt "mp_int_plus" :: int -> int -> int

Say that a given symbol corresponds to a primitive (non-C) operation::

        bit-and-i32 :: { i32 -> i32 -> i32 } = primitive


