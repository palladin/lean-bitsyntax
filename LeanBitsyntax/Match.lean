import Lean
import LeanBitsyntax.Internal
import LeanBitsyntax.Syntax

open Lean

namespace LeanBitsyntax.Match

class MatchInput (α : Type u) where
  toSizedBits : α → LeanBitsyntax.Internal.SizedBits

instance {n : Nat} : MatchInput (BitVec n) where
  toSizedBits bits := LeanBitsyntax.Internal.SizedBits.ofBitVec bits

instance : MatchInput LeanBitsyntax.Internal.SizedBits where
  toSizedBits bits := bits

def bindSegment (width : Nat) (value : LeanBitsyntax.Internal.SizedBits) : Option (BitVec width × LeanBitsyntax.Internal.SizedBits) :=
  value.splitMsb? width

def requireEq {n : Nat} (actual expected : BitVec n) : Option Unit :=
  if actual = expected then some () else none

def requireEmpty (value : LeanBitsyntax.Internal.SizedBits) : Option Unit :=
  if value.width = 0 then some () else none

end LeanBitsyntax.Match

namespace LeanBitsyntax

declare_syntax_cat bitsPatByteCount
syntax "bytes" "(" term ")" : bitsPatByteCount

declare_syntax_cat bitsPatSeg
syntax num : bitsPatSeg
syntax num " : " num : bitsPatSeg
syntax num " : " num " / " "big" : bitsPatSeg
syntax num " : " num " / " "little" : bitsPatSeg
syntax num " : " "(" term ")" : bitsPatSeg
syntax num " : " "(" term ")" " / " "big" : bitsPatSeg
syntax num " : " bitsPatByteCount " / " "little" : bitsPatSeg
syntax ident " : " num " / " "big" : bitsPatSeg
syntax ident " : " num " / " "signed" : bitsPatSeg
syntax ident " : " num " / " "little" : bitsPatSeg
syntax ident " : " num " / " "signed" "-" "big" : bitsPatSeg
syntax ident " : " num " / " "signed" "-" "little" : bitsPatSeg
syntax ident " : " num : bitsPatSeg
syntax ident " : " "(" term ")" : bitsPatSeg
syntax ident " : " bitsPatByteCount " / " "little" : bitsPatSeg
syntax ident " : " bitsPatByteCount " / " "signed" "-" "little" : bitsPatSeg
syntax "_" " : " num : bitsPatSeg
syntax "_" " : " "(" term ")" : bitsPatSeg
syntax "_" " : " bitsPatByteCount " / " "little" : bitsPatSeg
syntax "_" " : " bitsPatByteCount " / " "signed" "-" "little" : bitsPatSeg
syntax "(" term ")" " : " num : bitsPatSeg
syntax "(" term ")" " : " num " / " "big" : bitsPatSeg
syntax "(" term ")" " : " num " / " "signed" : bitsPatSeg
syntax "(" term ")" " : " num " / " "little" : bitsPatSeg
syntax "(" term ")" " : " num " / " "signed" "-" "big" : bitsPatSeg
syntax "(" term ")" " : " num " / " "signed" "-" "little" : bitsPatSeg
syntax "(" term ")" " : " "(" term ")" : bitsPatSeg
syntax "(" term ")" " : " "(" term ")" " / " "big" : bitsPatSeg
syntax "(" term ")" " : " "(" term ")" " / " "signed" : bitsPatSeg
syntax "(" term ")" " : " "(" term ")" " / " "signed" "-" "big" : bitsPatSeg
syntax "(" term ")" " : " bitsPatByteCount " / " "little" : bitsPatSeg
syntax "(" term ")" " : " bitsPatByteCount " / " "signed" "-" "little" : bitsPatSeg

declare_syntax_cat bitsPattern
syntax "<<" bitsPatSeg,* ">>" : bitsPattern
declare_syntax_cat bitsMatchRest
syntax "|" bitsPattern " => " term bitsMatchRest : bitsMatchRest
syntax "|" bitsPattern " => " term : bitsMatchRest
syntax "|" "_" " => " term : bitsMatchRest

declare_syntax_cat bitsMatchArms
syntax "|" bitsPattern " => " term bitsMatchRest : bitsMatchArms
syntax "|" bitsPattern " => " term : bitsMatchArms

/--
Fixed-width matching subset for the first matcher increment.

Currently supported pattern segments:
- bare numeric literals, defaulting to 8 bits
- sized numeric literals `n : w`
- modified numeric literals such as `n : w / little`
- width-explicit comparison terms `(expr) : w`
- captures `name : w` and modified captures such as `name : w / little`
- dependent-width literal and comparison segments such as `0xAABBCC : (8 * len.toNat)`
- dependent-width captures `name : (expr)` where `expr : Nat` can mention earlier captures
- byte-aligned dependent-width little-endian forms such as `word : bytes(len.toNat) / little`
- ignored segments `_ : w` and `_ : (expr)`

Each pattern must consume the full input.

An explicit final fallback branch is optional. When omitted, `bitmatch` falls back
to the original scrutinee unchanged, so the omitted-fallback form is most useful
for bit-preserving rewrites where the result type matches the scrutinee type.
-/
syntax (name := bitmatchTerm)
  "bitmatch " term " with " bitsMatchArms : term

private def mkNatTerm (value : Nat) : TSyntax `term :=
  ⟨Syntax.mkNumLit (toString value)⟩

private def byteCountFor (width : TSyntax `num) : MacroM (TSyntax `term) := do
  let widthNat := width.getNat
  if widthNat % 8 != 0 then
    Macro.throwErrorAt width s!"little-endian pattern segments currently require byte-aligned widths, got {widthNat}"
  pure (mkNatTerm (widthNat / 8))

private def expandByteCount (byteCount : TSyntax `bitsPatByteCount) : MacroM (TSyntax `term) := do
  match byteCount with
  | `(bitsPatByteCount| bytes($count:term)) =>
      pure count
  | _ => Macro.throwUnsupported

private def expandPatSeg (bits : TSyntax `term) (segment : TSyntax `bitsPatSeg)
    (restId : TSyntax `ident) (tail : TSyntax `term) : MacroM (TSyntax `term) := do
  match segment with
  | `(bitsPatSeg| $n:num) => do
      let headId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $(mkNatTerm 8) $bits with
        | some ($headId, $restId) =>
            match LeanBitsyntax.Match.requireEq $headId (LeanBitsyntax.Build.nat 8 $n) with
            | some () => $tail
            | none => none
        | none => none)
  | `(bitsPatSeg| $n:num : $w:num) => do
      let headId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
        | some ($headId, $restId) =>
            match LeanBitsyntax.Match.requireEq $headId (LeanBitsyntax.Build.nat $w $n) with
            | some () => $tail
            | none => none
        | none => none)
  | `(bitsPatSeg| $n:num : $w:num / big) => do
      let headId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
        | some ($headId, $restId) =>
            match LeanBitsyntax.Match.requireEq $headId (LeanBitsyntax.Build.nat $w $n) with
            | some () => $tail
            | none => none
        | none => none)
  | `(bitsPatSeg| $n:num : $w:num / little) => do
      let byteCount ← byteCountFor w
      let headId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
        | some ($headId, $restId) =>
        match LeanBitsyntax.Match.requireEq $headId (LeanBitsyntax.Build.littleEndianNat $byteCount $n) with
            | some () => $tail
            | none => none
        | none => none)
  | `(bitsPatSeg| $n:num : $byteCount:bitsPatByteCount / little) => do
      let byteCountTerm ← expandByteCount byteCount
      let width ← `(LeanBitsyntax.ByteWidth $byteCountTerm)
      let headId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $width $bits with
        | some ($headId, $restId) =>
        match LeanBitsyntax.Match.requireEq $headId (LeanBitsyntax.Build.littleEndianNat $byteCountTerm $n) with
            | some () => $tail
            | none => none
        | none => none)
    | `(bitsPatSeg| $n:num : ($w:term)) => do
      let headId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
      | some ($headId, $restId) =>
        match LeanBitsyntax.Match.requireEq $headId (LeanBitsyntax.Build.nat $w $n) with
        | some () => $tail
        | none => none
      | none => none)
    | `(bitsPatSeg| $n:num : ($w:term) / big) => do
      let headId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
      | some ($headId, $restId) =>
        match LeanBitsyntax.Match.requireEq $headId (LeanBitsyntax.Build.nat $w $n) with
        | some () => $tail
        | none => none
      | none => none)
  | `(bitsPatSeg| ($t:term) : $w:num) => do
      let headId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
        | some ($headId, $restId) =>
            match LeanBitsyntax.Match.requireEq $headId (LeanBitsyntax.Build.segment $w $t) with
            | some () => $tail
            | none => none
        | none => none)
  | `(bitsPatSeg| ($t:term) : $w:num / big) => do
      let headId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
        | some ($headId, $restId) =>
            match LeanBitsyntax.Match.requireEq $headId (LeanBitsyntax.Build.segment $w $t) with
            | some () => $tail
            | none => none
        | none => none)
  | `(bitsPatSeg| ($t:term) : $w:num / signed) => do
      let headId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
        | some ($headId, $restId) =>
            match LeanBitsyntax.Match.requireEq $headId (LeanBitsyntax.Build.signedSegment $w $t) with
            | some () => $tail
            | none => none
        | none => none)
  | `(bitsPatSeg| ($t:term) : $w:num / signed-big) => do
      let headId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
        | some ($headId, $restId) =>
            match LeanBitsyntax.Match.requireEq $headId (LeanBitsyntax.Build.signedSegment $w $t) with
            | some () => $tail
            | none => none
        | none => none)
  | `(bitsPatSeg| ($t:term) : $w:num / little) => do
      let byteCount ← byteCountFor w
      let headId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
        | some ($headId, $restId) =>
        match LeanBitsyntax.Match.requireEq $headId (LeanBitsyntax.Build.littleEndianSegment $byteCount $t) with
            | some () => $tail
            | none => none
        | none => none)
  | `(bitsPatSeg| ($t:term) : $w:num / signed-little) => do
      let byteCount ← byteCountFor w
      let headId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
        | some ($headId, $restId) =>
        match LeanBitsyntax.Match.requireEq $headId (LeanBitsyntax.Build.signedLittleEndianSegment $byteCount $t) with
            | some () => $tail
            | none => none
        | none => none)
    | `(bitsPatSeg| ($t:term) : $byteCount:bitsPatByteCount / little) => do
      let byteCountTerm ← expandByteCount byteCount
      let width ← `(LeanBitsyntax.ByteWidth $byteCountTerm)
      let headId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $width $bits with
      | some ($headId, $restId) =>
        match LeanBitsyntax.Match.requireEq $headId (LeanBitsyntax.Build.littleEndianSegment $byteCountTerm $t) with
        | some () => $tail
        | none => none
      | none => none)
    | `(bitsPatSeg| ($t:term) : $byteCount:bitsPatByteCount / signed-little) => do
      let byteCountTerm ← expandByteCount byteCount
      let width ← `(LeanBitsyntax.ByteWidth $byteCountTerm)
      let headId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $width $bits with
      | some ($headId, $restId) =>
        match LeanBitsyntax.Match.requireEq $headId (LeanBitsyntax.Build.signedLittleEndianSegment $byteCountTerm $t) with
        | some () => $tail
        | none => none
      | none => none)
    | `(bitsPatSeg| ($t:term) : ($w:term)) => do
      let headId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
      | some ($headId, $restId) =>
        match LeanBitsyntax.Match.requireEq $headId (LeanBitsyntax.Build.segment $w $t) with
        | some () => $tail
        | none => none
      | none => none)
    | `(bitsPatSeg| ($t:term) : ($w:term) / big) => do
      let headId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
      | some ($headId, $restId) =>
        match LeanBitsyntax.Match.requireEq $headId (LeanBitsyntax.Build.segment $w $t) with
        | some () => $tail
        | none => none
      | none => none)
    | `(bitsPatSeg| ($t:term) : ($w:term) / signed) => do
      let headId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
      | some ($headId, $restId) =>
        match LeanBitsyntax.Match.requireEq $headId (LeanBitsyntax.Build.signedSegment $w $t) with
        | some () => $tail
        | none => none
      | none => none)
    | `(bitsPatSeg| ($t:term) : ($w:term) / signed-big) => do
      let headId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
      | some ($headId, $restId) =>
        match LeanBitsyntax.Match.requireEq $headId (LeanBitsyntax.Build.signedSegment $w $t) with
        | some () => $tail
        | none => none
      | none => none)
    | `(bitsPatSeg| $name:ident : $w:num / big) => do
      let rawId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
      | some ($rawId, $restId) =>
        let $name := LeanBitsyntax.Build.segment $w $rawId
        $tail
      | none => none)
    | `(bitsPatSeg| $name:ident : $w:num / signed) => do
      let rawId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
      | some ($rawId, $restId) =>
        let $name := LeanBitsyntax.Build.signedSegment $w $rawId
        $tail
      | none => none)
    | `(bitsPatSeg| $name:ident : $w:num / little) => do
      let byteCount ← byteCountFor w
      let rawId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
      | some ($rawId, $restId) =>
        let $name := LeanBitsyntax.Build.littleEndianSegment $byteCount $rawId
        $tail
      | none => none)
    | `(bitsPatSeg| $name:ident : $w:num / signed-big) => do
      let rawId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
      | some ($rawId, $restId) =>
        let $name := LeanBitsyntax.Build.signedSegment $w $rawId
        $tail
      | none => none)
    | `(bitsPatSeg| $name:ident : $w:num / signed-little) => do
      let byteCount ← byteCountFor w
      let rawId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
      | some ($rawId, $restId) =>
        let $name := LeanBitsyntax.Build.signedLittleEndianSegment $byteCount $rawId
        $tail
      | none => none)
  | `(bitsPatSeg| $name:ident : $w:num) =>
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
        | some ($name, $restId) => $tail
        | none => none)
  | `(bitsPatSeg| $name:ident : ($w:term)) =>
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
        | some ($name, $restId) => $tail
        | none => none)
  | `(bitsPatSeg| $name:ident : $byteCount:bitsPatByteCount / little) => do
      let byteCountTerm ← expandByteCount byteCount
      let width ← `(LeanBitsyntax.ByteWidth $byteCountTerm)
      let rawId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $width $bits with
        | some ($rawId, $restId) =>
            let $name := LeanBitsyntax.Build.littleEndianSegment $byteCountTerm $rawId;
            $tail
        | none => none)
  | `(bitsPatSeg| $name:ident : $byteCount:bitsPatByteCount / signed-little) => do
      let byteCountTerm ← expandByteCount byteCount
      let width ← `(LeanBitsyntax.ByteWidth $byteCountTerm)
      let rawId := mkIdent `__segment
      `(match LeanBitsyntax.Match.bindSegment $width $bits with
        | some ($rawId, $restId) =>
            let $name := LeanBitsyntax.Build.signedLittleEndianSegment $byteCountTerm $rawId;
            $tail
        | none => none)
  | `(bitsPatSeg| _ : $w:num) => do
      let ignoredId := mkIdent `__ignored
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
        | some ($ignoredId, $restId) => $tail
        | none => none)
  | `(bitsPatSeg| _ : ($w:term)) => do
      let ignoredId := mkIdent `__ignored
      `(match LeanBitsyntax.Match.bindSegment $w $bits with
        | some ($ignoredId, $restId) => $tail
        | none => none)
  | `(bitsPatSeg| _ : $byteCount:bitsPatByteCount / little) => do
      let byteCountTerm ← expandByteCount byteCount
      let width ← `(LeanBitsyntax.ByteWidth $byteCountTerm)
      let ignoredId := mkIdent `__ignored
      `(match LeanBitsyntax.Match.bindSegment $width $bits with
        | some ($ignoredId, $restId) => $tail
        | none => none)
  | `(bitsPatSeg| _ : $byteCount:bitsPatByteCount / signed-little) => do
      let byteCountTerm ← expandByteCount byteCount
      let width ← `(LeanBitsyntax.ByteWidth $byteCountTerm)
      let ignoredId := mkIdent `__ignored
      `(match LeanBitsyntax.Match.bindSegment $width $bits with
        | some ($ignoredId, $restId) => $tail
        | none => none)
  | _ => Macro.throwUnsupported

private def expandPatSegs (bits : TSyntax `term) (segments : List (TSyntax `bitsPatSeg)) (body : TSyntax `term) : MacroM (TSyntax `term) := do
  match segments with
  | [] =>
      `(match LeanBitsyntax.Match.requireEmpty $bits with
        | some () => some $body
        | none => none)
  | segment :: rest =>
      let restId := mkIdent `__rest
      let restTerm : TSyntax `term := ⟨restId.raw⟩
      let tail ← expandPatSegs restTerm rest body
      expandPatSeg bits segment restId tail

private def expandBitsPattern (bits : TSyntax `term) (pattern : TSyntax `bitsPattern) (body : TSyntax `term) : MacroM (TSyntax `term) := do
  match pattern with
  | `(bitsPattern| << $segments:bitsPatSeg,* >>) =>
      expandPatSegs bits segments.getElems.toList body
  | _ => Macro.throwUnsupported

private partial def expandMatchRest (bits defaultFallback : TSyntax `term) : TSyntax `bitsMatchRest → MacroM (TSyntax `term)
  | `(bitsMatchRest| | _ => $fallback) =>
      pure fallback
  | `(bitsMatchRest| | $pattern:bitsPattern => $body) => do
      let resultId := mkIdent `__result
      let branch ← expandBitsPattern bits pattern body
      `(match ($branch) with
        | some $resultId => $resultId
        | none => $defaultFallback)
  | `(bitsMatchRest| | $pattern:bitsPattern => $body $rest:bitsMatchRest) => do
      let resultId := mkIdent `__result
      let branch ← expandBitsPattern bits pattern body
      let next ← expandMatchRest bits defaultFallback rest
      `(match ($branch) with
        | some $resultId => $resultId
        | none => $next)
  | _ => Macro.throwUnsupported

private def expandMatchArms (bits defaultFallback : TSyntax `term) : TSyntax `bitsMatchArms → MacroM (TSyntax `term)
  | `(bitsMatchArms| | $pattern:bitsPattern => $body) => do
      let resultId := mkIdent `__result
      let branch ← expandBitsPattern bits pattern body
      `(match ($branch) with
        | some $resultId => $resultId
        | none => $defaultFallback)
  | `(bitsMatchArms| | $pattern:bitsPattern => $body $rest:bitsMatchRest) => do
      let resultId := mkIdent `__result
      let branch ← expandBitsPattern bits pattern body
      let next ← expandMatchRest bits defaultFallback rest
      `(match ($branch) with
        | some $resultId => $resultId
        | none => $next)
  | _ => Macro.throwUnsupported

macro_rules
  | `(bitmatchTerm| bitmatch $scrutinee:term with $arms:bitsMatchArms) => do
        let scrutineeId := mkIdent `__scrutinee
        let inputId := mkIdent `__input
        let scrutineeTerm : TSyntax `term := ⟨scrutineeId.raw⟩
        let expanded ← expandMatchArms inputId scrutineeTerm arms
        `(let $scrutineeId := $scrutinee;
          let $inputId := LeanBitsyntax.Match.MatchInput.toSizedBits $scrutineeId;
          $expanded)

end LeanBitsyntax
