import LeanBitsyntax.Match

namespace LeanBitsyntax

/--
Protocol-oriented IPv6 example.

The example separates the fixed 40-byte base header from the payload and adds a
few semantic helpers such as header length and UDP detection.
-/
structure IPv6Header where
  trafficClass : Nat
  flowLabel : Nat
  payloadLengthBytes : Nat
  nextHeader : Nat
  hopLimit : Nat
  source : BitVec 128
  destination : BitVec 128
deriving Repr, DecidableEq

def IPv6Header.headerBytes (_header : IPv6Header) : Nat :=
  40

def IPv6Header.payloadBytes (header : IPv6Header) : Nat :=
  header.payloadLengthBytes

def IPv6Header.isUDP (header : IPv6Header) : Bool :=
  header.nextHeader = 17

structure IPv6Packet where
  header : IPv6Header
  payloadBits : Nat
  payload : BitVec payloadBits
deriving Repr, DecidableEq

def ipv6SourceAddress : BitVec 128 :=
  0x20010DB8000000000000000000000001#128

def ipv6DestinationAddress : BitVec 128 :=
  0x20010DB8000000000000000000000002#128

def ipv6Payload : BitVec 32 :=
  0xDEADBEEF#32

def ipv6Packet : BitVec 352 :=
  <<6:4, 0xAB:8, 0x54321:20, 4:16, 17, 64,
    (ipv6SourceAddress), (ipv6DestinationAddress), (ipv6Payload)>>

def ipv6PacketBadLength : BitVec 352 :=
  <<6:4, 0xAB:8, 0x54321:20, 5:16, 17, 64,
    (ipv6SourceAddress), (ipv6DestinationAddress), (ipv6Payload)>>

def parseIPv6Header {bits : Nat} (packet : BitVec bits) : Option IPv6Header :=
  bitmatch packet with
  | <<6:4, trafficClass : 8, flowLabel : 20, payloadLength : 16,
      nextHeader : 8, hopLimit : 8,
      source : 128, destination : 128,
      _ : (8 * payloadLength.toNat)>> =>
      some {
        trafficClass := trafficClass.toNat
        flowLabel := flowLabel.toNat
        payloadLengthBytes := payloadLength.toNat
        nextHeader := nextHeader.toNat
        hopLimit := hopLimit.toNat
        source := source
        destination := destination
      }
  | _ => none

def parseIPv6Packet {bits : Nat} (packet : BitVec bits) : Option IPv6Packet :=
  bitmatch packet with
  | <<6:4, trafficClass : 8, flowLabel : 20, payloadLength : 16,
      nextHeader : 8, hopLimit : 8,
      source : 128, destination : 128,
      payload : (8 * payloadLength.toNat)>> =>
      let header : IPv6Header := {
        trafficClass := trafficClass.toNat
        flowLabel := flowLabel.toNat
        payloadLengthBytes := payloadLength.toNat
        nextHeader := nextHeader.toNat
        hopLimit := hopLimit.toNat
        source := source
        destination := destination
      }
      some {
        header := header
        payloadBits := 8 * header.payloadLengthBytes
        payload := payload
      }
  | _ => none

def parsedIPv6Header : Option IPv6Header :=
  parseIPv6Header ipv6Packet

def parsedIPv6Packet : Option IPv6Packet :=
  parseIPv6Packet ipv6Packet

example : parsedIPv6Header = some {
    trafficClass := 0xAB
    flowLabel := 0x54321
    payloadLengthBytes := 4
    nextHeader := 17
    hopLimit := 64
    source := ipv6SourceAddress
    destination := ipv6DestinationAddress
  } := by
  native_decide

example : parsedIPv6Packet = some {
    header := {
      trafficClass := 0xAB
      flowLabel := 0x54321
      payloadLengthBytes := 4
      nextHeader := 17
      hopLimit := 64
      source := ipv6SourceAddress
      destination := ipv6DestinationAddress
    }
    payloadBits := 32
    payload := ipv6Payload
  } := by
  native_decide

example : parsedIPv6Header.map IPv6Header.headerBytes = some 40 := by
  native_decide

example : parsedIPv6Header.map IPv6Header.payloadBytes = some 4 := by
  native_decide

example : parsedIPv6Header.map IPv6Header.isUDP = some true := by
  native_decide

example : parseIPv6Packet ipv6PacketBadLength = none := by
  native_decide

end LeanBitsyntax
