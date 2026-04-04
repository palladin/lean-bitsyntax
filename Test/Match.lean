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

def decodedPayload : Nat :=
  bitmatch packet with
  | <<1, kind : 8, payload : 16>> => payload.toNat + kind.toNat
  | _ => 0

def fallbackOnLiteralMismatch : Nat :=
  bitmatch packet with
  | <<7, _ : 8, _ : 16>> => 1
  | _ => 2

def fallbackOnWidthMismatch : Nat :=
  bitmatch packet with
  | <<1 : 16, _ : 8>> => 1
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
  | _ => 0

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

def omittedFallbackReturnsInput : BitVec 16 :=
  bitmatch littleWord with
  | <<0xFFFF : 16>> => (0x0000#16)

def littleCaptureWins : Nat :=
  bitmatch littleWord with
  | <<word : 16 / little>> => word.toNat
  | _ => 0

def signedLittleCaptureWins : Int :=
  bitmatch signedLittleWord with
  | <<word : 16 / signed-little>> => word.toInt
  | _ => 0

def dependentWidthPayloadWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, payload : (8 * len.toNat)>> => payload.toNat
  | _ => 0

def dependentWidthIgnoreWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, _ : (8 * len.toNat)>> => len.toNat
  | _ => 0

def dependentWidthFallbackWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, _ : (8 * (len.toNat + 1))>> => 1
  | _ => 0

def dependentWidthLiteralWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, 0xAABBCC : (8 * len.toNat)>> => len.toNat
  | _ => 0

def dependentWidthLiteralMismatchWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, 0xAABBCA : (8 * len.toNat)>> => 1
  | _ => 0

def dependentWidthTermWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, (expectedLengthPrefixedPayload) : (8 * len.toNat)>> => len.toNat
  | _ => 0

def dependentWidthBigLiteralWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, 0xAABBCC : (8 * len.toNat) / big>> => len.toNat
  | _ => 0

def dependentWidthBigTermWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, (expectedLengthPrefixedPayload) : (8 * len.toNat) / big>> => len.toNat
  | _ => 0

def dependentWidthSignedTermWins : Nat :=
  bitmatch signedLengthPrefixedPacket with
  | <<len : 8, (-2) : (8 * len.toNat) / signed>> => len.toNat
  | _ => 0

def dependentWidthSignedBigTermWins : Nat :=
  bitmatch signedLengthPrefixedPacket with
  | <<len : 8, (-2) : (8 * len.toNat) / signed-big>> => len.toNat
  | _ => 0

def dependentByteWidthLittleLiteralWins : Nat :=
  bitmatch littleLengthPrefixedPacket with
  | <<len : 8, 0xAABBCC : bytes(len.toNat) / little>> => len.toNat
  | _ => 0

def dependentByteWidthLittleCaptureWins : Nat :=
  bitmatch littleLengthPrefixedPacket with
  | <<len : 8, payload : bytes(len.toNat) / little>> => payload.toNat
  | _ => 0

def dependentByteWidthLittleIgnoreWins : Nat :=
  bitmatch littleLengthPrefixedPacket with
  | <<len : 8, _ : bytes(len.toNat) / little>> => len.toNat
  | _ => 0

def dependentByteWidthSignedLittleTermWins : Nat :=
  bitmatch signedLittleLengthPrefixedPacket with
  | <<len : 8, (-2) : bytes(len.toNat) / signed-little>> => len.toNat
  | _ => 0

def dependentByteWidthLittleMismatchWins : Nat :=
  bitmatch littleLengthPrefixedPacket with
  | <<len : 8, 0xAABBCA : bytes(len.toNat) / little>> => 1
  | _ => 0

example : decodedPayload = 59 := by
  native_decide

example : fallbackOnLiteralMismatch = 2 := by
  native_decide

example : fallbackOnWidthMismatch = 2 := by
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

example : omittedFallbackReturnsInput = littleWord := by
  native_decide

example : littleCaptureWins = 0x1234 := by
  native_decide

example : signedLittleCaptureWins = -2 := by
  native_decide

example : dependentWidthPayloadWins = 0xAABBCC := by
  native_decide

example : dependentWidthIgnoreWins = 3 := by
  native_decide

example : dependentWidthFallbackWins = 0 := by
  native_decide

example : dependentWidthLiteralWins = 3 := by
  native_decide

example : dependentWidthLiteralMismatchWins = 0 := by
  native_decide

example : dependentWidthTermWins = 3 := by
  native_decide

example : dependentWidthBigLiteralWins = 3 := by
  native_decide

example : dependentWidthBigTermWins = 3 := by
  native_decide

example : dependentWidthSignedTermWins = 2 := by
  native_decide

example : dependentWidthSignedBigTermWins = 2 := by
  native_decide

example : dependentByteWidthLittleLiteralWins = 3 := by
  native_decide

example : dependentByteWidthLittleCaptureWins = 0xAABBCC := by
  native_decide

example : dependentByteWidthLittleIgnoreWins = 3 := by
  native_decide

example : dependentByteWidthSignedLittleTermWins = 2 := by
  native_decide

example : dependentByteWidthLittleMismatchWins = 0 := by
  native_decide

end LeanBitsyntax.Test
