namespace LeanBitsyntax

/-- The number of bits in `n` bytes. -/
abbrev ByteWidth (n : Nat) : Nat := 8 * n

@[simp]
theorem byteWidth_zero : ByteWidth 0 = 0 := rfl

@[simp]
theorem byteWidth_one : ByteWidth 1 = 8 := rfl

@[simp]
theorem byteWidth_add (m n : Nat) : ByteWidth (m + n) = ByteWidth m + ByteWidth n := by
  simp [ByteWidth, Nat.left_distrib]

@[simp]
theorem byteWidth_succ (n : Nat) : ByteWidth (n + 1) = ByteWidth n + 8 := by
  simp [byteWidth_add]

end LeanBitsyntax
