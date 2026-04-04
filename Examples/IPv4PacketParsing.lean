import LeanBitsyntax.Match

namespace LeanBitsyntax

/--
Protocol-oriented IPv4 example.

The example separates header parsing from full-packet parsing and exposes a few
derived protocol properties such as header length, whether options are present,
whether the packet is fragmented, and whether the payload should be treated as
UDP.
-/
structure IPv4Header where
  ihlWords : Nat
  dscp : Nat
  ecn : Nat
  totalLengthBytes : Nat
  identification : Nat
  flags : Nat
  fragmentOffset : Nat
  ttl : Nat
  protocol : Nat
  headerChecksum : Nat
  source : BitVec 32
  destination : BitVec 32
deriving Repr, DecidableEq

def IPv4Header.headerBytes (header : IPv4Header) : Nat :=
  4 * header.ihlWords

def IPv4Header.payloadBytes (header : IPv4Header) : Nat :=
  header.totalLengthBytes - header.headerBytes

def IPv4Header.hasOptions (header : IPv4Header) : Bool :=
  decide (header.ihlWords > 5)

def IPv4Header.moreFragments (header : IPv4Header) : Bool :=
  header.flags % 2 = 1

def IPv4Header.isFragmented (header : IPv4Header) : Bool :=
  header.moreFragments || decide (header.fragmentOffset ≠ 0)

def IPv4Header.isUDP (header : IPv4Header) : Bool :=
  header.protocol = 17

structure IPv4Packet where
  header : IPv4Header
  optionsBits : Nat
  options : BitVec optionsBits
  payloadBits : Nat
  payload : BitVec payloadBits
deriving Repr, DecidableEq

def ipv4SourceAddress : BitVec 32 :=
  0xC0A8010A#32

def ipv4DestinationAddress : BitVec 32 :=
  0x08080808#32

def ipv4Options : BitVec 0 :=
  <<>>

def ipv4Payload : BitVec 32 :=
  0xDEADBEEF#32

def ipv4Packet : BitVec 192 :=
  <<4:4, 5:4, 0:6, 0:2, 24:16, 0x1234:16, 2:3, 0:13, 64, 17, 0:16,
    (ipv4SourceAddress), (ipv4DestinationAddress), (ipv4Options), (ipv4Payload)>>

def ipv4PacketBadLength : BitVec 192 :=
  <<4:4, 5:4, 0:6, 0:2, 28:16, 0x1234:16, 2:3, 0:13, 64, 17, 0:16,
    (ipv4SourceAddress), (ipv4DestinationAddress), (ipv4Options), (ipv4Payload)>>

def parseIPv4Header {bits : Nat} (packet : BitVec bits) : Option IPv4Header :=
  bitmatch packet with
  | <<4:4, ihlWords : 4, dscp : 6, ecn : 2, totalLength : 16,
      identification : 16, flags : 3, fragmentOffset : 13,
      ttl : 8, protocol : 8, headerChecksum : 16,
      source : 32, destination : 32,
      _ : (32 * ihlWords.toNat - 160),
      _ : (8 * totalLength.toNat - 32 * ihlWords.toNat)>> =>
      let header : IPv4Header := {
        ihlWords := ihlWords.toNat
        dscp := dscp.toNat
        ecn := ecn.toNat
        totalLengthBytes := totalLength.toNat
        identification := identification.toNat
        flags := flags.toNat
        fragmentOffset := fragmentOffset.toNat
        ttl := ttl.toNat
        protocol := protocol.toNat
        headerChecksum := headerChecksum.toNat
        source := source
        destination := destination
      }
      if header.ihlWords < 5 then
        none
      else if header.totalLengthBytes < header.headerBytes then
        none
      else
        some header
  | _ => none

def parseIPv4Packet {bits : Nat} (packet : BitVec bits) : Option IPv4Packet :=
  bitmatch packet with
  | <<4:4, ihlWords : 4, dscp : 6, ecn : 2, totalLength : 16,
      identification : 16, flags : 3, fragmentOffset : 13,
      ttl : 8, protocol : 8, headerChecksum : 16,
      source : 32, destination : 32,
      options : (32 * ihlWords.toNat - 160),
      payload : (8 * totalLength.toNat - 32 * ihlWords.toNat)>> =>
      let header : IPv4Header := {
        ihlWords := ihlWords.toNat
        dscp := dscp.toNat
        ecn := ecn.toNat
        totalLengthBytes := totalLength.toNat
        identification := identification.toNat
        flags := flags.toNat
        fragmentOffset := fragmentOffset.toNat
        ttl := ttl.toNat
        protocol := protocol.toNat
        headerChecksum := headerChecksum.toNat
        source := source
        destination := destination
      }
      if header.ihlWords < 5 then
        none
      else if header.totalLengthBytes < header.headerBytes then
        none
      else
        some {
          header := header
          optionsBits := 32 * header.ihlWords - 160
          options := options
          payloadBits := 8 * header.totalLengthBytes - 32 * header.ihlWords
          payload := payload
        }
  | _ => none

def parsedIPv4Header : Option IPv4Header :=
  parseIPv4Header ipv4Packet

def parsedIPv4Packet : Option IPv4Packet :=
  parseIPv4Packet ipv4Packet

example : parsedIPv4Header = some {
    ihlWords := 5
    dscp := 0
    ecn := 0
    totalLengthBytes := 24
    identification := 0x1234
    flags := 2
    fragmentOffset := 0
    ttl := 64
    protocol := 17
    headerChecksum := 0
    source := ipv4SourceAddress
    destination := ipv4DestinationAddress
  } := by
  native_decide

example : parsedIPv4Packet = some {
    header := {
      ihlWords := 5
      dscp := 0
      ecn := 0
      totalLengthBytes := 24
      identification := 0x1234
      flags := 2
      fragmentOffset := 0
      ttl := 64
      protocol := 17
      headerChecksum := 0
      source := ipv4SourceAddress
      destination := ipv4DestinationAddress
    }
    optionsBits := 0
    options := ipv4Options
    payloadBits := 32
    payload := ipv4Payload
  } := by
  native_decide

example : parsedIPv4Header.map IPv4Header.headerBytes = some 20 := by
  native_decide

example : parsedIPv4Header.map IPv4Header.payloadBytes = some 4 := by
  native_decide

example : parsedIPv4Header.map IPv4Header.hasOptions = some false := by
  native_decide

example : parsedIPv4Header.map IPv4Header.isFragmented = some false := by
  native_decide

example : parsedIPv4Header.map IPv4Header.isUDP = some true := by
  native_decide

example : parseIPv4Packet ipv4PacketBadLength = none := by
  native_decide

end LeanBitsyntax
