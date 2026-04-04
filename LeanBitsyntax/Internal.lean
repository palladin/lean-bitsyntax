import Lean

namespace LeanBitsyntax.Internal

/--
Internal width-carrying representation used when a width is only known after
construction or decoding. Public APIs should prefer `BitVec n`.
-/
structure SizedBits where
  width : Nat
  bits : BitVec width

namespace SizedBits

def empty : SizedBits :=
  ⟨0, BitVec.nil⟩

instance : EmptyCollection SizedBits where
  emptyCollection := empty

instance : Repr SizedBits where
  reprPrec value _ :=
    s!"SizedBits(width := {value.width}, hex := 0x{value.bits.toHex})"

def ofBitVec {n : Nat} (bits : BitVec n) : SizedBits :=
  ⟨n, bits⟩

def ofNat (width value : Nat) : SizedBits :=
  ofBitVec (BitVec.ofNat width value)

def ofInt (width : Nat) (value : Int) : SizedBits :=
  ofBitVec (BitVec.ofInt width value)

def append (lhs rhs : SizedBits) : SizedBits :=
  ⟨lhs.width + rhs.width, BitVec.append lhs.bits rhs.bits⟩

instance : Append SizedBits where
  append := append

def toNat (value : SizedBits) : Nat :=
  value.bits.toNat

def toInt (value : SizedBits) : Int :=
  value.bits.toInt

def zeroExtend (newWidth : Nat) (value : SizedBits) : SizedBits :=
  ⟨newWidth, BitVec.zeroExtend newWidth value.bits⟩

def signExtend (newWidth : Nat) (value : SizedBits) : SizedBits :=
  ⟨newWidth, BitVec.signExtend newWidth value.bits⟩

def extractLsb? (start len : Nat) (value : SizedBits) : Option (BitVec len) :=
  if _h : start + len ≤ value.width then
    some (BitVec.extractLsb' start len value.bits)
  else
    none

def takeLsb? (len : Nat) (value : SizedBits) : Option (BitVec len) :=
  extractLsb? 0 len value

def dropLsb? (len : Nat) (value : SizedBits) : Option SizedBits :=
  if _h : len ≤ value.width then
    let remainingWidth := value.width - len
    some ⟨remainingWidth, BitVec.extractLsb' len remainingWidth value.bits⟩
  else
    none

def takeMsb? (len : Nat) (value : SizedBits) : Option (BitVec len) :=
  if _h : len ≤ value.width then
    let start := value.width - len
    some (BitVec.extractLsb' start len value.bits)
  else
    none

def dropMsb? (len : Nat) (value : SizedBits) : Option SizedBits :=
  if _h : len ≤ value.width then
    let remainingWidth := value.width - len
    some ⟨remainingWidth, BitVec.extractLsb' 0 remainingWidth value.bits⟩
  else
    none

def splitMsb? (len : Nat) (value : SizedBits) : Option (BitVec len × SizedBits) := do
  let head ← takeMsb? len value
  let tail ← dropMsb? len value
  pure (head, tail)

def splitLsb? (len : Nat) (value : SizedBits) : Option (BitVec len × SizedBits) := do
  let tail ← takeLsb? len value
  let rest ← dropLsb? len value
  pure (tail, rest)

@[simp]
theorem width_ofBitVec {n : Nat} (bits : BitVec n) : (ofBitVec bits).width = n := rfl

@[simp]
theorem bits_ofBitVec {n : Nat} (bits : BitVec n) : (ofBitVec bits).bits = bits := rfl

@[simp]
theorem width_empty : empty.width = 0 := rfl

@[simp]
theorem bits_empty : empty.bits = BitVec.nil := rfl

@[simp]
theorem width_append (lhs rhs : SizedBits) : (lhs ++ rhs).width = lhs.width + rhs.width := rfl

@[simp]
theorem bits_append (lhs rhs : SizedBits) : (lhs ++ rhs).bits = BitVec.append lhs.bits rhs.bits := rfl

end SizedBits

end LeanBitsyntax.Internal
