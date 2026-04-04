import LeanBitsyntax.Match

namespace LeanBitsyntax

/--
LeanBitsyntax form of Example 5.1 from
"Programming Efficiently with Binaries and Bit Strings":

`reverse_32bit(<<X:32,Rest/bits>>) -> <<(reverse_32bit(Rest))/bits,X:32>>;`
`reverse_32bit(<<>>) -> <<>>.`

The important constraint is kept in the type: a `BitVec (32 * chunks)` is
reversed into another `BitVec (32 * chunks)`, so the tail is captured as
`rest : (32 * chunks)`.
-/
def reverse_32bit : {chunks : Nat} → BitVec (32 * chunks) → BitVec (32 * chunks)
  | 0, _ => <<>>
  | chunks + 1, bits =>
      bitmatch bits with
      | <<x : 32, rest : (32 * chunks)>> => <<(reverse_32bit rest), x : 32>>

def example51Input : BitVec 96 :=
  <<0x11111111:32, 0x22222222:32, 0x33333333:32>>

def example51Expected : BitVec 96 :=
  <<0x33333333:32, 0x22222222:32, 0x11111111:32>>

def example51Reversed : BitVec 96 :=
  reverse_32bit (chunks := 3) example51Input

example : example51Reversed = example51Expected := by
  rfl

end LeanBitsyntax
