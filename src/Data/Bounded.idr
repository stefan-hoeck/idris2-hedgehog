module Data.Bounded

%default total

public export
interface Ord b => MinBound b where
  ||| The lower bound for the type
  minBound : b

public export
interface Ord b => MaxBound b where
  ||| The upper bound for the type
  maxBound : b

public export %inline
MinBound Bits8 where
  minBound = 0x0

public export %inline
MaxBound Bits8 where
  maxBound = 0xff

public export %inline
MinBound Bits16 where
  minBound = 0x0

public export %inline
MaxBound Bits16 where
  maxBound = 0xffff

public export %inline
MinBound Bits32 where
  minBound = 0x0

public export %inline
MaxBound Bits32 where
  maxBound = 0xffffffff

public export %inline
MinBound Bits64 where
  minBound = 0x0

public export %inline
MaxBound Bits64 where
  maxBound = 0xffffffffffffffff

public export %inline
MinBound Int8 where
  minBound = (- 0x80)

public export %inline
MaxBound Int8 where
  maxBound = 0x7f

public export %inline
MinBound Int16 where
  minBound = (- 0x8000)

public export %inline
MaxBound Int16 where
  maxBound = 0x7fff

public export %inline
MinBound Int32 where
  minBound = (- 0x80000000)

public export %inline
MaxBound Int32 where
  maxBound = 0x7fffffff

public export %inline
MinBound Int64 where
  minBound = (- 0x8000000000000000)

public export %inline
MaxBound Int64 where
  maxBound = 0x7fffffffffffffff

public export %inline
MinBound Int where
  minBound = (- 0x8000000000000000)

public export %inline
MaxBound Int where
  maxBound = 0x7fffffffffffffff
