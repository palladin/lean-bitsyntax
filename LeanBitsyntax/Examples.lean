import LeanBitsyntax.Match

namespace LeanBitsyntax

def demoPacket : BitVec 32 :=
  <<1, 17, 42:16>>

def mixedPacket : BitVec 32 :=
  <<(0xAB#8), 1, 2, 3>>

def widenedLiteral : BitVec 16 :=
  <<(0xAB#8) : 16>>

def sourceWord : Nat :=
  0x1234

def littleEndianWord : BitVec 16 :=
  <<sourceWord : 16 / little>>

def signedByteValue : Int :=
  -1

def signedByte : BitVec 8 :=
  <<signedByteValue : 8 / signed>>

def signExtendedNibble : BitVec 8 :=
  <<(0xF#4) : 8 / signed>>

def signedLittleWord : BitVec 16 :=
  <<(-2) : 16 / signed-little>>

def headerMarker : BitVec 8 :=
  0xAB#8

def expectedLengthPrefixedPayload : BitVec 24 :=
  0xAABBCC#24

def lengthPrefixedPacket : BitVec 32 :=
  <<3, 0xAABBCC:24>>

def signedLengthPrefixedPacket : BitVec 24 :=
  <<2, (-2) : 16 / signed>>

def littleLengthPrefixedPacket : BitVec 32 :=
  <<3, 0xAABBCC:24 / little>>

def signedLittleLengthPrefixedPacket : BitVec 24 :=
  <<2, (-2) : 16 / signed-little>>

def parsedPayload : Nat :=
  bitmatch demoPacket with
  | <<1, _ : 8, payload : 16>> => payload.toNat
  | _ => 0

def rejectedPacketFallback : Nat :=
  bitmatch demoPacket with
  | <<2, _ : 8, _ : 16>> => 99
  | _ => 0

def parsedPayloadFromSecondBranch : Nat :=
  bitmatch demoPacket with
  | <<2, _ : 8, _ : 16>> => 99
  | <<1, _ : 8, payload : 16>> => payload.toNat
  | _ => 0

def parsedKindFromThirdBranch : Nat :=
  bitmatch demoPacket with
  | <<2, _ : 8, _ : 16>> => 99
  | <<3, _ : 8, _ : 16>> => 100
  | <<1, kind : 8, _ : 16>> => kind.toNat
  | _ => 0

def parsedSecondByteFromTermPattern : Nat :=
  bitmatch mixedPacket with
  | <<(headerMarker) : 8, second : 8, _ : 16>> => second.toNat
  | _ => 0

def littleEndianLiteralPatternMatched : Nat :=
  bitmatch littleEndianWord with
  | <<0x1234 : 16 / little>> => 1
  | _ => 0

def signedPatternMatched : Nat :=
  bitmatch signExtendedNibble with
  | <<(0xF#4) : 8 / signed>> => 1
  | _ => 0

def signedLittlePatternMatched : Nat :=
  bitmatch signedLittleWord with
  | <<(-2) : 16 / signed-little>> => 1
  | _ => 0

def capturedLittleWord : Nat :=
  bitmatch littleEndianWord with
  | <<word : 16 / little>> => word.toNat
  | _ => 0

def capturedSignedLittleWord : Int :=
  bitmatch signedLittleWord with
  | <<word : 16 / signed-little>> => word.toInt
  | _ => 0

def dependentWidthPayload : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, payload : (8 * len.toNat)>> => payload.toNat
  | _ => 0

def dependentWidthIgnored : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, _ : (8 * len.toNat)>> => len.toNat
  | _ => 0

def dependentWidthFallback : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, _ : (8 * (len.toNat + 1))>> => 1
  | _ => 0

def dependentWidthLiteralMatched : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, 0xAABBCC : (8 * len.toNat)>> => len.toNat
  | _ => 0

def dependentWidthLiteralMismatch : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, 0xAABBCA : (8 * len.toNat)>> => 1
  | _ => 0

def dependentWidthTermMatched : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, (expectedLengthPrefixedPayload) : (8 * len.toNat)>> => len.toNat
  | _ => 0

def dependentWidthSignedTermMatched : Nat :=
  bitmatch signedLengthPrefixedPacket with
  | <<len : 8, (-2) : (8 * len.toNat) / signed>> => len.toNat
  | _ => 0

def dependentByteWidthLittleLiteralMatched : Nat :=
  bitmatch littleLengthPrefixedPacket with
  | <<len : 8, 0xAABBCC : bytes(len.toNat) / little>> => len.toNat
  | _ => 0

def dependentByteWidthLittleCapture : Nat :=
  bitmatch littleLengthPrefixedPacket with
  | <<len : 8, payload : bytes(len.toNat) / little>> => payload.toNat
  | _ => 0

def dependentByteWidthLittleIgnore : Nat :=
  bitmatch littleLengthPrefixedPacket with
  | <<len : 8, _ : bytes(len.toNat) / little>> => len.toNat
  | _ => 0

def dependentByteWidthSignedLittleTermMatched : Nat :=
  bitmatch signedLittleLengthPrefixedPacket with
  | <<len : 8, (-2) : bytes(len.toNat) / signed-little>> => len.toNat
  | _ => 0

def dependentByteWidthLittleMismatch : Nat :=
  bitmatch littleLengthPrefixedPacket with
  | <<len : 8, 0xAABBCA : bytes(len.toNat) / little>> => 1
  | _ => 0

example : demoPacket = (0x0111002A#32) := by
  decide

example : mixedPacket = (0xAB010203#32) := by
  decide

example : widenedLiteral = (0x00AB#16) := by
  native_decide

example : littleEndianWord = (0x3412#16) := by
  native_decide

example : signedByte = (0xFF#8) := by
  decide

example : signExtendedNibble = (0xFF#8) := by
  native_decide

example : parsedPayload = 42 := by
  native_decide

example : rejectedPacketFallback = 0 := by
  native_decide

example : parsedPayloadFromSecondBranch = 42 := by
  native_decide

example : parsedKindFromThirdBranch = 17 := by
  native_decide

example : parsedSecondByteFromTermPattern = 1 := by
  native_decide

example : littleEndianLiteralPatternMatched = 1 := by
  native_decide

example : signedPatternMatched = 1 := by
  native_decide

example : signedLittlePatternMatched = 1 := by
  native_decide

example : capturedLittleWord = 0x1234 := by
  native_decide

example : capturedSignedLittleWord = -2 := by
  native_decide

example : dependentWidthPayload = 0xAABBCC := by
  native_decide

example : dependentWidthIgnored = 3 := by
  native_decide

example : dependentWidthFallback = 0 := by
  native_decide

example : dependentWidthLiteralMatched = 3 := by
  native_decide

example : dependentWidthLiteralMismatch = 0 := by
  native_decide

example : dependentWidthTermMatched = 3 := by
  native_decide

example : dependentWidthSignedTermMatched = 2 := by
  native_decide

example : dependentByteWidthLittleLiteralMatched = 3 := by
  native_decide

example : dependentByteWidthLittleCapture = 0xAABBCC := by
  native_decide

example : dependentByteWidthLittleIgnore = 3 := by
  native_decide

example : dependentByteWidthSignedLittleTermMatched = 2 := by
  native_decide

example : dependentByteWidthLittleMismatch = 0 := by
  native_decide

end LeanBitsyntax
