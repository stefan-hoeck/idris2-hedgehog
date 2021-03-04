||| This module will be removed once #1033 is added to base.
module Data.Bits

import public Data.Bounded

infixl 8 `shiftL`, `shiftR`
infixl 7 .&.
infixl 6 `xor`
infixl 5 .|.

--------------------------------------------------------------------------------
--          Interface Bits
--------------------------------------------------------------------------------

||| The 'Bits' interface defines bitwise operations over integral types.
public export
interface Bits a where
  ||| Bitwise "and"
  (.&.) : a -> a -> a

  ||| Bitwise "or"
  (.|.) : a -> a -> a

  ||| Shift the argument left by the specified number of bits.
  shiftL : a -> a -> a

  ||| Shift the argument right by the specified number of bits.
  shiftR : a -> a -> a

  ||| Sets the `i`-th bit.
  bit : (i : a) -> a

  ||| The value with all bits unset.
  zeroBits : a

  ||| Tests, whether the i-th bit is set in the given value.
  testBit : a -> a -> Bool

  ||| Sets the i-th bit of a value.
  setBit : a -> (i : a) -> a
  setBit x i = x .|. bit i

  ||| Bitwise "xor".
  xor : a -> a -> a

  ||| Complements the i-th bit of a value
  complementBit : a -> (i : a) -> a
  complementBit x i = x `xor` bit i

export
popCount : Eq a => Num a => Bits a => a -> Nat
popCount x = if x == 0 then 0
                       else let pc = popCount $ x `shiftR` 1
                             in if testBit x 0 then S pc else pc

public export %inline
Bits Bits8 where
  (.&.)       = prim__and_Bits8
  (.|.)       = prim__or_Bits8
  shiftR      = prim__shr_Bits8
  shiftL      = prim__shl_Bits8
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = setBit x i == x
  xor         = prim__xor_Bits8

public export %inline
Bits Bits16 where
  (.&.)       = prim__and_Bits16
  (.|.)       = prim__or_Bits16
  shiftR      = prim__shr_Bits16
  shiftL      = prim__shl_Bits16
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = setBit x i == x
  xor         = prim__xor_Bits16

public export %inline
Bits Bits32 where
  (.&.)       = prim__and_Bits32
  (.|.)       = prim__or_Bits32
  shiftR      = prim__shr_Bits32
  shiftL      = prim__shl_Bits32
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = setBit x i == x
  xor         = prim__xor_Bits32

public export %inline
Bits Bits64 where
  (.&.)       = prim__and_Bits64
  (.|.)       = prim__or_Bits64
  shiftR      = prim__shr_Bits64
  shiftL      = prim__shl_Bits64
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = setBit x i == x
  xor         = prim__xor_Bits64

public export %inline
Bits Int where
  (.&.)       = prim__and_Int
  (.|.)       = prim__or_Int
  shiftR      = prim__shr_Int
  shiftL      = prim__shl_Int
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = setBit x i == x
  xor         = prim__xor_Int

public export %inline
Bits Integer where
  (.&.)       = prim__and_Integer
  (.|.)       = prim__or_Integer
  shiftR      = prim__shr_Integer
  shiftL      = prim__shl_Integer
  bit         = (1 `shiftL`)
  zeroBits    = 0
  testBit x i = setBit x i == x
  xor         = believe_me prim__xor_Integer

--------------------------------------------------------------------------------
--          XorBits
--------------------------------------------------------------------------------

public export
interface Bits t => FiniteBits t where
  bits : t

  ||| Returns the bitwise complement of a value.
  complement : t -> t

  ||| Clears (unsets) the i-th bit of a value
  clearBit : t -> (i : t) -> t
  clearBit x i = x .&. complement (bit i)

public export %inline
FiniteBits Bits8 where
  complement  = xor maxBound
  bits = 8

public export %inline
FiniteBits Bits16 where
  complement  = xor maxBound
  bits = 16

public export %inline
FiniteBits Bits32 where
  complement  = xor maxBound
  bits = 32

public export %inline
FiniteBits Bits64 where
  complement  = xor maxBound
  bits = 64
