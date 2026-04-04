import LeanBitsyntax.Width

namespace LeanBitsyntax

def concat {m n : Nat} (lhs : BitVec m) (rhs : BitVec n) : BitVec (m + n) :=
  BitVec.append lhs rhs

def takeMsb {n len : Nat} (bits : BitVec n) (_h : len ≤ n) : BitVec len :=
  BitVec.extractLsb' (n - len) len bits

def dropMsb {n len : Nat} (bits : BitVec n) (_h : len ≤ n) : BitVec (n - len) :=
  BitVec.extractLsb' 0 (n - len) bits

def splitMsb {n len : Nat} (bits : BitVec n) (h : len ≤ n) : BitVec len × BitVec (n - len) :=
  (takeMsb bits h, dropMsb bits h)

def takeLsb {n len : Nat} (bits : BitVec n) (_h : len ≤ n) : BitVec len :=
  BitVec.extractLsb' 0 len bits

def dropLsb {n len : Nat} (bits : BitVec n) (_h : len ≤ n) : BitVec (n - len) :=
  BitVec.extractLsb' len (n - len) bits

def splitLsb {n len : Nat} (bits : BitVec n) (h : len ≤ n) : BitVec len × BitVec (n - len) :=
  (takeLsb bits h, dropLsb bits h)

end LeanBitsyntax
