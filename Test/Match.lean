import LeanBitsyntax.Match

namespace LeanBitsyntax.Test

def packet : BitVec 32 :=
  <<1, 17, 42:16>>

def marker : BitVec 8 :=
  0xAB#8

def expectedLengthPrefixedPayload : BitVec 24 :=
  0xAABBCC#24

def markedPacket : BitVec 32 :=
  <<(marker), 1, 2, 3>>

def littleWord : BitVec 16 :=
  <<0x1234:16 / little>>

def signedBigWord : BitVec 16 :=
  <<(-2) : 16 / signed>>

def signedNibble : BitVec 8 :=
  <<(0xF#4) : 8 / signed>>

def signedLittleWord : BitVec 16 :=
  <<(-2) : 16 / signed-little>>

def lengthPrefixedPacket : BitVec 32 :=
  <<3, 0xAABBCC:24>>

def signedLengthPrefixedPacket : BitVec 24 :=
  <<2, (-2) : 16 / signed>>

def littleLengthPrefixedPacket : BitVec 32 :=
  <<3, 0xAABBCC:24 / little>>

def signedLittleLengthPrefixedPacket : BitVec 24 :=
  <<2, (-2) : 16 / signed-little>>

def boundedDependentWidthPacket : BitVec 32 :=
  <<3:2, 5:3, 0:27>>

def boundedDependentByteWidthPacket : BitVec 32 :=
  <<2:2, 0xAABB:16 / little, 0:14>>

def decodedPayload : Nat :=
  bitmatch packet with
  | <<1, kind : 8, payload : 16>> => payload.toNat + kind.toNat
  | _ => 0

def fallbackOnLiteralMismatch : Nat :=
  bitmatch packet with
  | <<7, _ : 8, _ : 16>> => 1
  | _ => 2

def secondBranchWins : Nat :=
  bitmatch packet with
  | <<7, _ : 8, _ : 16>> => 1
  | <<1, _ : 8, payload : 16>> => payload.toNat
  | _ => 2

def thirdBranchWins : Nat :=
  bitmatch packet with
  | <<7, _ : 8, _ : 16>> => 1
  | <<8, _ : 8, _ : 16>> => 2
  | <<1, kind : 8, _ : 16>> => kind.toNat
  | _ => 3

def termPatternWins : Nat :=
  bitmatch markedPacket with
  | <<(marker) : 8, second : 8, _ : 16>> => second.toNat
  | _ => 0

def littleLiteralPatternWins : Nat :=
  bitmatch littleWord with
  | <<0x1234 : 16 / little>> => 1
  | _ => 0

def explicitBigLiteralPatternWins : Nat :=
  bitmatch packet with
  | <<1 : 8 / big, 17 : 8 / big, payload : 16 / big>> => payload.toNat
  | _ => 0

def explicitBigTermPatternWins : Nat :=
  bitmatch packet with
  | <<(1) : 8 / big, kind : 8 / big, (0x002A#16) : 16 / big>> => kind.toNat
  | _ => 0

def signedPatternWins : Nat :=
  bitmatch signedNibble with
  | <<(0xF#4) : 8 / signed>> => 1
  | _ => 0

def explicitSignedBigPatternWins : Int :=
  bitmatch signedBigWord with
  | <<word : 16 / signed-big>> => word.toInt

def explicitSignedBigTermPatternWins : Nat :=
  bitmatch signedBigWord with
  | <<(-2) : 16 / signed-big>> => 1
  | _ => 0

def signedLittlePatternWins : Nat :=
  bitmatch signedLittleWord with
  | <<(-2) : 16 / signed-little>> => 1
  | _ => 0

def omittedFallbackBranchWins : BitVec 16 :=
  bitmatch littleWord with
  | <<word : 16>> => word

def omittedFallbackLittleCaptureWins : BitVec 16 :=
  bitmatch littleWord with
  | <<word : 16 / little>> => word

def omittedFallbackSignedBigCaptureWins : Int :=
  bitmatch signedBigWord with
  | <<word : 16 / signed-big>> => word.toInt

def omittedFallbackSignedLittleCaptureWins : Int :=
  bitmatch signedLittleWord with
  | <<word : 16 / signed-little>> => word.toInt

def explicitFallbackReturnsInput : BitVec 16 :=
  bitmatch littleWord with
  | <<0xFFFF : 16>> => (0x0000#16)
  | _ => littleWord

def littleCaptureWins : Nat :=
  bitmatch littleWord with
  | <<word : 16 / little>> => word.toNat

def signedLittleCaptureWins : Int :=
  bitmatch signedLittleWord with
  | <<word : 16 / signed-little>> => word.toInt

def fixedWidthPayloadWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, payload : 24>> =>
      if len.toNat = 3 then payload.toNat else 0

def fixedWidthIgnoreWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, _ : 24>> =>
      if len.toNat = 3 then len.toNat else 0

def fixedWidthLiteralWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, 0xAABBCC : 24>> =>
      if len.toNat = 3 then len.toNat else 0
  | _ => 0

def fixedWidthLiteralMismatchWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, 0xAABBCA : 24>> =>
      if len.toNat = 3 then 1 else 0
  | _ => 0

def fixedWidthTermWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, (expectedLengthPrefixedPayload) : 24>> =>
      if len.toNat = 3 then len.toNat else 0
  | _ => 0

def fixedWidthBigLiteralWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, 0xAABBCC : 24 / big>> =>
      if len.toNat = 3 then len.toNat else 0
  | _ => 0

def fixedWidthBigTermWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, (expectedLengthPrefixedPayload) : 24 / big>> =>
      if len.toNat = 3 then len.toNat else 0
  | _ => 0

def fixedWidthSignedTermWins : Nat :=
  bitmatch signedLengthPrefixedPacket with
  | <<len : 8, (-2) : 16 / signed>> =>
      if len.toNat = 2 then len.toNat else 0
  | _ => 0

def fixedWidthSignedBigTermWins : Nat :=
  bitmatch signedLengthPrefixedPacket with
  | <<len : 8, (-2) : 16 / signed-big>> =>
      if len.toNat = 2 then len.toNat else 0
  | _ => 0

def dependentWidthCaptureWins : Nat :=
  bitmatch boundedDependentWidthPacket with
  | <<len : 2, payload : (len.toNat), _ : (30 - len.toNat)>> => payload.toNat
  --| _ => 0

#print dependentWidthCaptureWins

def fixedByteWidthLittleLiteralWins : Nat :=
  bitmatch littleLengthPrefixedPacket with
  | <<len : 8, 0xAABBCC : bytes(3) / little>> =>
      if len.toNat = 3 then len.toNat else 0
  | _ => 0

def fixedByteWidthLittleCaptureWins : Nat :=
  bitmatch littleLengthPrefixedPacket with
  | <<len : 8, payload : bytes(3) / little>> =>
      if len.toNat = 3 then payload.toNat else 0

def fixedByteWidthLittleIgnoreWins : Nat :=
  bitmatch littleLengthPrefixedPacket with
  | <<len : 8, _ : bytes(3) / little>> =>
      if len.toNat = 3 then len.toNat else 0

def fixedByteWidthSignedLittleTermWins : Nat :=
  bitmatch signedLittleLengthPrefixedPacket with
  | <<len : 8, (-2) : bytes(2) / signed-little>> =>
      if len.toNat = 2 then len.toNat else 0
  | _ => 0

def dependentByteWidthLittleCaptureWins : Nat :=
  bitmatch boundedDependentByteWidthPacket with
  | <<len : 2, payload : bytes(len.toNat) / little, _ : (30 - (8 * len.toNat))>> => payload.toNat

def fixedByteWidthLittleMismatchWins : Nat :=
  bitmatch littleLengthPrefixedPacket with
  | <<len : 8, 0xAABBCA : bytes(3) / little>> =>
      if len.toNat = 3 then 1 else 0
  | _ => 0

example : decodedPayload = 59 := by
  native_decide

example : fallbackOnLiteralMismatch = 2 := by
  native_decide

example : secondBranchWins = 42 := by
  native_decide

example : thirdBranchWins = 17 := by
  native_decide

example : termPatternWins = 1 := by
  native_decide

example : littleLiteralPatternWins = 1 := by
  native_decide

example : explicitBigLiteralPatternWins = 42 := by
  native_decide

example : explicitBigTermPatternWins = 17 := by
  native_decide

example : signedPatternWins = 1 := by
  native_decide

example : explicitSignedBigPatternWins = -2 := by
  native_decide

example : explicitSignedBigTermPatternWins = 1 := by
  native_decide

example : signedLittlePatternWins = 1 := by
  native_decide

example : omittedFallbackBranchWins = littleWord := by
  native_decide

example : omittedFallbackLittleCaptureWins = (0x1234#16) := by
  native_decide

example : omittedFallbackSignedBigCaptureWins = -2 := by
  native_decide

example : omittedFallbackSignedLittleCaptureWins = -2 := by
  native_decide

example : explicitFallbackReturnsInput = littleWord := by
  native_decide

example : littleCaptureWins = 0x1234 := by
  native_decide

example : signedLittleCaptureWins = -2 := by
  native_decide

example : fixedWidthPayloadWins = 0xAABBCC := by
  native_decide

example : fixedWidthIgnoreWins = 3 := by
  native_decide

example : fixedWidthLiteralWins = 3 := by
  native_decide

example : fixedWidthLiteralMismatchWins = 0 := by
  native_decide

example : fixedWidthTermWins = 3 := by
  native_decide

example : fixedWidthBigLiteralWins = 3 := by
  native_decide

example : fixedWidthBigTermWins = 3 := by
  native_decide

example : fixedWidthSignedTermWins = 2 := by
  native_decide

example : fixedWidthSignedBigTermWins = 2 := by
  native_decide

example : dependentWidthCaptureWins = 5 := by
  native_decide

example : fixedByteWidthLittleLiteralWins = 3 := by
  native_decide

example : fixedByteWidthLittleCaptureWins = 0xAABBCC := by
  native_decide

example : fixedByteWidthLittleIgnoreWins = 3 := by
  native_decide

example : fixedByteWidthSignedLittleTermWins = 2 := by
  native_decide

example : fixedByteWidthLittleMismatchWins = 0 := by
  native_decide

example : dependentByteWidthLittleCaptureWins = 0xAABB := by
  native_decide

end LeanBitsyntax.Test
