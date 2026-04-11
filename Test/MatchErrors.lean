import LeanBitsyntax.Match

namespace LeanBitsyntax.Test

def packet : BitVec 32 :=
  <<1, 17, 42:16>>

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

/--
error: unsolved goals
-/
#guard_msgs (error, substring := true) in
def fallbackOnWidthMismatch : Nat :=
  bitmatch packet with
  | <<1 : 16, _ : 8>> => 1
  | _ => 2

/--
error: unsolved goals
-/
#guard_msgs (error, substring := true) in
def fixedWidthFallbackWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, _ : 32>> =>
      if len.toNat = 3 then 1 else 0
  | _ => 0

/--
error: pattern widths must be statically determined
-/
#guard_msgs (error, substring := true) in
def dependentWidthPayloadWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, payload : (8 * len.toNat)>> => payload.toNat
  | _ => 0

/--
error: pattern widths must be statically determined
-/
#guard_msgs (error, substring := true) in
def dependentWidthIgnoreWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, _ : (8 * len.toNat)>> => len.toNat
  | _ => 0

/--
error: pattern widths must be statically determined
-/
#guard_msgs (error, substring := true) in
def dependentWidthFallbackWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, _ : (8 * (len.toNat + 1))>> => 1
  | _ => 0

/--
error: pattern widths must be statically determined
-/
#guard_msgs (error, substring := true) in
def dependentWidthLiteralWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, 0xAABBCC : (8 * len.toNat)>> => len.toNat
  | _ => 0

/--
error: pattern widths must be statically determined
-/
#guard_msgs (error, substring := true) in
def dependentWidthLiteralMismatchWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, 0xAABBCA : (8 * len.toNat)>> => 1
  | _ => 0

/--
error: pattern widths must be statically determined
-/
#guard_msgs (error, substring := true) in
def dependentWidthTermWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, (expectedLengthPrefixedPayload) : (8 * len.toNat)>> => len.toNat
  | _ => 0

/--
error: pattern widths must be statically determined
-/
#guard_msgs (error, substring := true) in
def dependentWidthBigLiteralWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, 0xAABBCC : (8 * len.toNat) / big>> => len.toNat
  | _ => 0

/--
error: pattern widths must be statically determined
-/
#guard_msgs (error, substring := true) in
def dependentWidthBigTermWins : Nat :=
  bitmatch lengthPrefixedPacket with
  | <<len : 8, (expectedLengthPrefixedPayload) : (8 * len.toNat) / big>> => len.toNat
  | _ => 0

/--
error: pattern widths must be statically determined
-/
#guard_msgs (error, substring := true) in
def dependentWidthSignedTermWins : Nat :=
  bitmatch signedLengthPrefixedPacket with
  | <<len : 8, (-2) : (8 * len.toNat) / signed>> => len.toNat
  | _ => 0

/--
error: pattern widths must be statically determined
-/
#guard_msgs (error, substring := true) in
def dependentWidthSignedBigTermWins : Nat :=
  bitmatch signedLengthPrefixedPacket with
  | <<len : 8, (-2) : (8 * len.toNat) / signed-big>> => len.toNat
  | _ => 0

/--
error: pattern widths must be statically determined
-/
#guard_msgs (error, substring := true) in
def dependentByteWidthLittleLiteralWins : Nat :=
  bitmatch littleLengthPrefixedPacket with
  | <<len : 8, 0xAABBCC : bytes(len.toNat) / little>> => len.toNat
  | _ => 0

/--
error: pattern widths must be statically determined
-/
#guard_msgs (error, substring := true) in
def dependentByteWidthLittleCaptureWins : Nat :=
  bitmatch littleLengthPrefixedPacket with
  | <<len : 8, payload : bytes(len.toNat) / little>> => payload.toNat
  | _ => 0

/--
error: pattern widths must be statically determined
-/
#guard_msgs (error, substring := true) in
def dependentByteWidthLittleIgnoreWins : Nat :=
  bitmatch littleLengthPrefixedPacket with
  | <<len : 8, _ : bytes(len.toNat) / little>> => len.toNat
  | _ => 0

/--
error: pattern widths must be statically determined
-/
#guard_msgs (error, substring := true) in
def dependentByteWidthSignedLittleTermWins : Nat :=
  bitmatch signedLittleLengthPrefixedPacket with
  | <<len : 8, (-2) : bytes(len.toNat) / signed-little>> => len.toNat
  | _ => 0

/--
error: pattern widths must be statically determined
-/
#guard_msgs (error, substring := true) in
def dependentByteWidthLittleMismatchWins : Nat :=
  bitmatch littleLengthPrefixedPacket with
  | <<len : 8, 0xAABBCA : bytes(len.toNat) / little>> => 1
  | _ => 0

end LeanBitsyntax.Test
