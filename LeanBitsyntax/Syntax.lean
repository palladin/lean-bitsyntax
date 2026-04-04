import Lean
import LeanBitsyntax.Build

open Lean

namespace LeanBitsyntax

/-- A construction-only segment parser for the first implementation slice. -/
declare_syntax_cat bitsSeg
syntax num : bitsSeg
syntax num " : " num : bitsSeg
syntax num " : " num " / " "big" : bitsSeg
syntax num " : " num " / " "little" : bitsSeg
syntax ident " : " num : bitsSeg
syntax ident " : " num " / " "big" : bitsSeg
syntax ident " : " num " / " "signed" : bitsSeg
syntax ident " : " num " / " "little" : bitsSeg
syntax ident " : " num " / " "signed" "-" "big" : bitsSeg
syntax ident " : " num " / " "signed" "-" "little" : bitsSeg
syntax "(" term ")" " : " num : bitsSeg
syntax "(" term ")" " : " num " / " "big" : bitsSeg
syntax "(" term ")" " : " num " / " "signed" : bitsSeg
syntax "(" term ")" " : " num " / " "little" : bitsSeg
syntax "(" term ")" " : " num " / " "signed" "-" "big" : bitsSeg
syntax "(" term ")" " : " num " / " "signed" "-" "little" : bitsSeg
syntax "(" term ")" : bitsSeg

/--
Exact bitsyntax surface form for the initial construction subset.

Currently supported segments:
- bare numeric literals, defaulting to 8 bits
- sized numeric literals `n : w`
- width-explicit identifiers `value : w`
- parenthesized existing `BitVec` terms `(expr)`
- width-explicit parenthesized terms `(expr) : w`
- `big`, `little`, and `signed` for width-explicit term segments
-/
syntax (name := bitsLiteral) "<<" bitsSeg,* ">>" : term

private def mkNatTerm (value : Nat) : TSyntax `term :=
  ⟨Syntax.mkNumLit (toString value)⟩

private def mkIdentTerm (name : TSyntax `ident) : TSyntax `term :=
  ⟨name.raw⟩

private def byteCountFor (width : TSyntax `num) : MacroM (TSyntax `term) := do
  let widthNat := width.getNat
  if widthNat % 8 != 0 then
    Macro.throwErrorAt width s!"little-endian segments currently require byte-aligned widths, got {widthNat}"
  pure (mkNatTerm (widthNat / 8))

private def expandBitsSeg : TSyntax `bitsSeg → MacroM (TSyntax `term)
  | `(bitsSeg| $n:num) => `(LeanBitsyntax.Build.nat 8 $n)
  | `(bitsSeg| $n:num : $w:num) => `(LeanBitsyntax.Build.nat $w $n)
  | `(bitsSeg| $n:num : $w:num / big) => `(LeanBitsyntax.Build.nat $w $n)
  | `(bitsSeg| $n:num : $w:num / little) => do
      let bytes ← byteCountFor w
      `(LeanBitsyntax.Build.littleEndianNat $bytes $n)
  | `(bitsSeg| $t:ident : $w:num) => `(LeanBitsyntax.Build.segment $w $(mkIdentTerm t))
  | `(bitsSeg| $t:ident : $w:num / big) => `(LeanBitsyntax.Build.segment $w $(mkIdentTerm t))
  | `(bitsSeg| $t:ident : $w:num / signed) => `(LeanBitsyntax.Build.signedSegment $w $(mkIdentTerm t))
  | `(bitsSeg| $t:ident : $w:num / signed-big) => `(LeanBitsyntax.Build.signedSegment $w $(mkIdentTerm t))
  | `(bitsSeg| $t:ident : $w:num / little) => do
      let bytes ← byteCountFor w
      `(LeanBitsyntax.Build.littleEndianSegment $bytes $(mkIdentTerm t))
  | `(bitsSeg| $t:ident : $w:num / signed-little) => do
      let bytes ← byteCountFor w
      `(LeanBitsyntax.Build.signedLittleEndianSegment $bytes $(mkIdentTerm t))
  | `(bitsSeg| ($t:term)) => pure t
  | `(bitsSeg| ($t:term) : $w:num) => `(LeanBitsyntax.Build.segment $w $t)
  | `(bitsSeg| ($t:term) : $w:num / big) => `(LeanBitsyntax.Build.segment $w $t)
  | `(bitsSeg| ($t:term) : $w:num / signed) => `(LeanBitsyntax.Build.signedSegment $w $t)
  | `(bitsSeg| ($t:term) : $w:num / signed-big) => `(LeanBitsyntax.Build.signedSegment $w $t)
  | `(bitsSeg| ($t:term) : $w:num / little) => do
      let bytes ← byteCountFor w
      `(LeanBitsyntax.Build.littleEndianSegment $bytes $t)
  | `(bitsSeg| ($t:term) : $w:num / signed-little) => do
      let bytes ← byteCountFor w
      `(LeanBitsyntax.Build.signedLittleEndianSegment $bytes $t)
  | _ => Macro.throwUnsupported

private def expandBitsSegs : List (TSyntax `bitsSeg) → MacroM (TSyntax `term)
  | [] => `(LeanBitsyntax.Build.empty)
  | [segment] => expandBitsSeg segment
  | segment :: rest => do
      let head ← expandBitsSeg segment
      let tail ← expandBitsSegs rest
      `(LeanBitsyntax.Build.concat $head $tail)

macro_rules
  | `(<< $segments:bitsSeg,* >>) =>
      expandBitsSegs segments.getElems.toList

end LeanBitsyntax
