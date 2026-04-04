import LeanBitsyntax.Internal
import LeanBitsyntax.Core

namespace LeanBitsyntax.Build

inductive Endianness where
  | big
  | little
deriving DecidableEq, Repr

class SegmentValue (α : Type u) where
  toUnsignedBitVec : (width : Nat) → α → BitVec width
  toSignedBitVec : (width : Nat) → α → BitVec width

instance : SegmentValue Nat where
  toUnsignedBitVec width value := BitVec.ofNat width value
  toSignedBitVec width value := BitVec.ofInt width value

instance : SegmentValue Int where
  toUnsignedBitVec width value := BitVec.ofInt width value
  toSignedBitVec width value := BitVec.ofInt width value

instance {n : Nat} : SegmentValue (BitVec n) where
  toUnsignedBitVec width value := BitVec.zeroExtend width value
  toSignedBitVec width value := BitVec.signExtend width value

instance : SegmentValue LeanBitsyntax.Internal.SizedBits where
  toUnsignedBitVec width value := BitVec.zeroExtend width value.bits
  toSignedBitVec width value := BitVec.signExtend width value.bits

def empty : BitVec 0 :=
  BitVec.nil

def nat (width value : Nat) : BitVec width :=
  BitVec.ofNat width value

def int (width : Nat) (value : Int) : BitVec width :=
  BitVec.ofInt width value

def segment {α : Type u} [SegmentValue α] (width : Nat) (value : α) : BitVec width :=
  SegmentValue.toUnsignedBitVec width value

def signedSegment {α : Type u} [SegmentValue α] (width : Nat) (value : α) : BitVec width :=
  SegmentValue.toSignedBitVec width value

def concat {m n : Nat} (lhs : BitVec m) (rhs : BitVec n) : BitVec (m + n) :=
  LeanBitsyntax.concat lhs rhs

private def reverseBytesAux : (bytes : Nat) → BitVec (LeanBitsyntax.ByteWidth bytes) → BitVec (LeanBitsyntax.ByteWidth bytes)
  | 0, bits => bits
  | bytes + 1, bits => by
      have h : 8 ≤ LeanBitsyntax.ByteWidth (bytes + 1) := by
        simp [LeanBitsyntax.ByteWidth]
      let head : BitVec 8 := LeanBitsyntax.takeMsb bits h
      let tail : BitVec (LeanBitsyntax.ByteWidth bytes) := LeanBitsyntax.dropMsb bits h
      simpa [LeanBitsyntax.ByteWidth, Nat.left_distrib, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        LeanBitsyntax.concat (reverseBytesAux bytes tail) head

def littleEndian {bytes : Nat} (value : BitVec (LeanBitsyntax.ByteWidth bytes)) : BitVec (LeanBitsyntax.ByteWidth bytes) :=
  reverseBytesAux bytes value

def littleEndianNat (bytes value : Nat) : BitVec (LeanBitsyntax.ByteWidth bytes) :=
  littleEndian (nat (LeanBitsyntax.ByteWidth bytes) value)

def littleEndianSegment {α : Type u} [SegmentValue α] (bytes : Nat) (value : α) : BitVec (LeanBitsyntax.ByteWidth bytes) :=
  littleEndian (segment (LeanBitsyntax.ByteWidth bytes) value)

def signedLittleEndianSegment {α : Type u} [SegmentValue α] (bytes : Nat) (value : α) : BitVec (LeanBitsyntax.ByteWidth bytes) :=
  littleEndian (signedSegment (LeanBitsyntax.ByteWidth bytes) value)

example : littleEndianNat 2 0x1234 = (0x3412#16) := by
  decide

end LeanBitsyntax.Build
