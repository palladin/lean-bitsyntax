import LeanBitsyntax.Syntax

namespace LeanBitsyntax.Test

def sourceWord : Nat :=
  0x1234

def signedValue : Int :=
  -1

def signedLittleValue : Int :=
  -2

def bareByte : BitVec 8 :=
  <<42>>

def sizedNat : BitVec 16 :=
  <<42:16>>

def littleNat : BitVec 16 :=
  <<0x1234:16 / little>>

def explicitBigNat : BitVec 16 :=
  <<0x1234:16 / big>>

def identLittle : BitVec 16 :=
  <<sourceWord : 16 / little>>

def explicitBigIdent : BitVec 16 :=
  <<sourceWord : 16 / big>>

def widenedBitVec : BitVec 16 :=
  <<(0xAB#8) : 16>>

def explicitBigTerm : BitVec 16 :=
  <<(0xAB#8) : 16 / big>>

def signedInt : BitVec 8 :=
  <<signedValue : 8 / signed>>

def explicitSignedBigIdent : BitVec 8 :=
  <<signedValue : 8 / signed-big>>

def signExtendedNibble : BitVec 8 :=
  <<(0xF#4) : 8 / signed>>

def explicitSignedBigTerm : BitVec 8 :=
  <<(0xF#4) : 8 / signed-big>>

def signedLittleWord : BitVec 16 :=
  <<signedLittleValue : 16 / signed-little>>

example : bareByte = (0x2A#8) := by
  decide

example : sizedNat = (0x002A#16) := by
  decide

example : littleNat = (0x3412#16) := by
  native_decide

example : explicitBigNat = (0x1234#16) := by
  native_decide

example : identLittle = (0x3412#16) := by
  native_decide

example : explicitBigIdent = (0x1234#16) := by
  native_decide

example : widenedBitVec = (0x00AB#16) := by
  native_decide

example : explicitBigTerm = (0x00AB#16) := by
  native_decide

example : signedInt = (0xFF#8) := by
  decide

example : explicitSignedBigIdent = (0xFF#8) := by
  decide

example : signExtendedNibble = (0xFF#8) := by
  native_decide

example : explicitSignedBigTerm = (0xFF#8) := by
  native_decide

example : signedLittleWord = (0xFEFF#16) := by
  native_decide

end LeanBitsyntax.Test
