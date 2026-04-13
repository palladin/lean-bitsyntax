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

def capturedSignedLittleWord : Int :=
  bitmatch signedLittleWord with
  | <<word : 16 / signed-little>> => word.toInt

def staticallySizedPayload : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, payload : 24>> =>
      if len.toNat = 3 then payload.toNat else 0

def staticallySizedIgnored : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, _ : 24>> =>
      if len.toNat = 3 then len.toNat else 0

def staticallySizedLiteralMatched : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, 0xAABBCC : 24>> =>
      if len.toNat = 3 then len.toNat else 0
  | _ => 0

def staticallySizedTermMatched : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, (expectedLengthPrefixedPayload) : 24>> =>
      if len.toNat = 3 then len.toNat else 0
  | _ => 0

def staticallySizedSignedTermMatched : Nat :=
  bitmatch signedLengthPrefixedPacket with
  | <<len : 8, (-2) : 16 / signed>> =>
      if len.toNat = 2 then len.toNat else 0
  | _ => 0

def staticallySizedLittleLiteralMatched : Nat :=
  bitmatch littleLengthPrefixedPacket with
  | <<len : 8, 0xAABBCC : bytes(3) / little>> =>
      if len.toNat = 3 then len.toNat else 0
  | _ => 0

def staticallySizedLittleCapture : Nat :=
  bitmatch littleLengthPrefixedPacket with
  | <<len : 8, payload : bytes(3) / little>> =>
      if len.toNat = 3 then payload.toNat else 0

def staticallySizedLittleIgnore : Nat :=
  bitmatch littleLengthPrefixedPacket with
  | <<len : 8, _ : bytes(3) / little>> =>
      if len.toNat = 3 then len.toNat else 0

def staticallySizedSignedLittleTermMatched : Nat :=
  bitmatch signedLittleLengthPrefixedPacket with
  | <<len : 8, (-2) : bytes(2) / signed-little>> =>
      if len.toNat = 2 then len.toNat else 0
  | _ => 0

/-
Captured-dependent widths such as `(8 * len.toNat)` or `bytes(len.toNat)` are
accepted when the generated arithmetic obligations can be proved from the
surrounding facts. This aggregate examples file sticks to fixed-width cases;
see `Test/Match.lean` for accepted dependent-width examples and
`Test/MatchErrors.lean` for guarded rejected cases.
-/

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

example : staticallySizedPayload = 0xAABBCC := by
  native_decide

example : staticallySizedIgnored = 3 := by
  native_decide

example : staticallySizedLiteralMatched = 3 := by
  native_decide

example : staticallySizedTermMatched = 3 := by
  native_decide

example : staticallySizedSignedTermMatched = 2 := by
  native_decide

example : staticallySizedLittleLiteralMatched = 3 := by
  native_decide

example : staticallySizedLittleCapture = 0xAABBCC := by
  native_decide

example : staticallySizedLittleIgnore = 3 := by
  native_decide

example : staticallySizedSignedLittleTermMatched = 2 := by
  native_decide

end LeanBitsyntax
