import LeanBitsyntax.Match

namespace LeanBitsyntax

/--
IPv4 header checksum example inspired by Program 3 in
"Programming Efficiently with Binaries and Bit Strings".

This file models the front-consuming recursive versions naturally supported by
the current bitsyntax subset:

- a straightforward 16-bit recursive checksum
- an unrolled variant that consumes eight 16-bit words at a time

The offset-based iterator variants from the paper are less natural in the
current DSL because they rely on indexed prefix skipping.
-/

def int16Max : Nat :=
  0xFFFF

def foldCarryOnce (csum : Nat) : Nat :=
  (csum % (int16Max + 1)) + (csum / (int16Max + 1))

def doTrunc (csum : Nat) : Nat :=
  if 0x6ffffff < csum ∧ csum < 0x7ffffff then
    foldCarryOnce csum
  else
    csum

def finishChecksum (csum : Nat) : Nat :=
  let csum := foldCarryOnce csum
  let csum := foldCarryOnce csum
  int16Max - csum

def ipv4ChecksumAcc {byteCount : Nat} (bits : BitVec (8 * byteCount)) (csum : Nat) : Nat :=
  if _h2 : 2 ≤ byteCount then
    bitmatch bits with
    | <<word : 16, rest : (8 * (byteCount - 2))>> =>
        ipv4ChecksumAcc (byteCount := byteCount - 2) rest (doTrunc (csum + word.toNat))
    | _ => 0
  else if _h1 : 1 ≤ byteCount then
    bitmatch bits with
    | <<last : 8>> =>
        ipv4ChecksumAcc (byteCount := 0) <<>> (doTrunc (csum + 256 * last.toNat))
    | _ => 0
  else
    finishChecksum csum
termination_by byteCount
decreasing_by
  all_goals omega

def ipv4ChecksumAccUnrolled {byteCount : Nat} (bits : BitVec (8 * byteCount)) (csum : Nat) : Nat :=
  if _h16 : 16 ≤ byteCount then
    bitmatch bits with
    | <<w1 : 16, w2 : 16, w3 : 16, w4 : 16,
        w5 : 16, w6 : 16, w7 : 16, w8 : 16,
        rest : (8 * (byteCount - 16))>> =>
        ipv4ChecksumAccUnrolled (byteCount := byteCount - 16) rest
          (doTrunc (csum + w1.toNat + w2.toNat + w3.toNat + w4.toNat +
            w5.toNat + w6.toNat + w7.toNat + w8.toNat))
    | _ => 0
  else if _h2 : 2 ≤ byteCount then
    bitmatch bits with
    | <<word : 16, rest : (8 * (byteCount - 2))>> =>
        ipv4ChecksumAccUnrolled (byteCount := byteCount - 2) rest (doTrunc (csum + word.toNat))
    | _ => 0
  else if _h1 : 1 ≤ byteCount then
    bitmatch bits with
    | <<last : 8>> =>
        ipv4ChecksumAccUnrolled (byteCount := 0) <<>> (doTrunc (csum + 256 * last.toNat))
    | _ => 0
  else
    finishChecksum csum
termination_by byteCount
decreasing_by
  all_goals omega

def ipv4Checksum {byteCount : Nat} (bits : BitVec (8 * byteCount)) : Nat :=
  ipv4ChecksumAcc (byteCount := byteCount) bits 0

def ipv4ChecksumUnrolled {byteCount : Nat} (bits : BitVec (8 * byteCount)) : Nat :=
  ipv4ChecksumAccUnrolled (byteCount := byteCount) bits 0

def ipv4SourceAddress : BitVec 32 :=
  0xC0A8010A#32

def ipv4DestinationAddress : BitVec 32 :=
  0x08080808#32

def ipv4HeaderWithoutChecksum : BitVec 160 :=
  <<4:4, 5:4, 0:6, 0:2, 24:16, 0x1234:16, 2:3, 0:13, 64, 17, 0:16,
    (ipv4SourceAddress), (ipv4DestinationAddress)>>

def ipv4HeaderChecksumValue : Nat :=
  ipv4Checksum (byteCount := 20) ipv4HeaderWithoutChecksum

def ipv4HeaderChecksumBits : BitVec 16 :=
  BitVec.ofNat 16 ipv4HeaderChecksumValue

def ipv4HeaderWithChecksum : BitVec 160 :=
  <<4:4, 5:4, 0:6, 0:2, 24:16, 0x1234:16, 2:3, 0:13, 64, 17,
    (ipv4HeaderChecksumBits), (ipv4SourceAddress), (ipv4DestinationAddress)>>

example : ipv4HeaderChecksumValue = 0x56DF := by
  native_decide

example : ipv4ChecksumUnrolled (byteCount := 20) ipv4HeaderWithoutChecksum = ipv4HeaderChecksumValue := by
  native_decide

example : ipv4Checksum (byteCount := 20) ipv4HeaderWithChecksum = 0 := by
  native_decide

example : ipv4ChecksumUnrolled (byteCount := 20) ipv4HeaderWithChecksum = 0 := by
  native_decide

end LeanBitsyntax
