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
MinBound Int where
  minBound = (- 0xffffffffffffffff)

public export %inline
MaxBound Int where
  maxBound = 0xffffffffffffffff
