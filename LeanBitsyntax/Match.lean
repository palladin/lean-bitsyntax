import Lean
import LeanBitsyntax.Syntax

open Lean

namespace LeanBitsyntax.Match

def splitExact (headWidth tailWidth : Nat) {n : Nat} (bits : BitVec n)
    (_h : n = headWidth + tailWidth) : BitVec headWidth × BitVec tailWidth := by
  subst n
  have hle : headWidth ≤ headWidth + tailWidth := by
    omega
  exact (LeanBitsyntax.takeMsb bits hle, by simpa using LeanBitsyntax.dropMsb bits hle)

def exactWidth (width : Nat) {n : Nat} (bits : BitVec n) (_h : n = width) : BitVec width := by
  subst n
  exact bits

def continueIfFits (width : Nat) {n : Nat} {α : Sort u} (bits : BitVec n) (fallback : α)
    (k : BitVec width → BitVec (n - width) → α) : α :=
  if h : width ≤ n then
    k (LeanBitsyntax.takeMsb bits h) (LeanBitsyntax.dropMsb bits h)
  else
    fallback

def continueIfExact (width : Nat) {n : Nat} {α : Sort u} (bits : BitVec n) (fallback : α)
    (k : BitVec width → α) : α :=
  if h : n = width then
    k (exactWidth width bits h)
  else
    fallback

end LeanBitsyntax.Match

namespace LeanBitsyntax

private inductive CaptureMode where
  | raw
  | unsigned
  | signed
  | little (byteCount : TSyntax `term)
  | signedLittle (byteCount : TSyntax `term)

private inductive TotalPatSeg where
  | capture (name : TSyntax `ident) (width : TSyntax `term) (mode : CaptureMode)
  | ignore (width : TSyntax `term)

private inductive TypedBranchSeg where
  | guard (width : TSyntax `term) (expected : TSyntax `term)
  | capture (name : TSyntax `ident) (width : TSyntax `term) (mode : CaptureMode)
  | ignore (width : TSyntax `term)

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

An explicit final fallback branch is required for ordinary partial matches.
Omitting the fallback is currently accepted only for a single structurally total
capture/ignore rewrite branch, which lowers directly to typed `BitVec` splitting.
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

private partial def syntaxMentionsAny (names : List Name) : Syntax → Bool
  | Syntax.ident _ _ val _ =>
    (names.map Name.eraseMacroScopes).contains val.eraseMacroScopes
  | Syntax.node _ _ args =>
    args.toList.any (syntaxMentionsAny names)
  | _ =>
    false

private def widthSafeAgainst (captured : List Name) (width : TSyntax `term) : Bool :=
  !syntaxMentionsAny captured width.raw

private def expandCaptureValue (mode : CaptureMode) (width raw : TSyntax `term) : MacroM (TSyntax `term) := do
  match mode with
  | .raw =>
    pure raw
  | .unsigned =>
    `(LeanBitsyntax.Build.segment $width $raw)
  | .signed =>
    `(LeanBitsyntax.Build.signedSegment $width $raw)
  | .little byteCount =>
    `(LeanBitsyntax.Build.littleEndianSegment $byteCount $raw)
  | .signedLittle byteCount =>
    `(LeanBitsyntax.Build.signedLittleEndianSegment $byteCount $raw)

private def totalPatSegWidth : TotalPatSeg → TSyntax `term
  | .capture _ width _ => width
  | .ignore width => width

private def asTotalPatSeg (captured : List Name) (segment : TSyntax `bitsPatSeg) : MacroM (TotalPatSeg × List Name) := do
  let captureIfSafe (name : TSyntax `ident) (width : TSyntax `term) (mode : CaptureMode) : MacroM (TotalPatSeg × List Name) := do
    if widthSafeAgainst captured width then
      pure (.capture name width mode, captured.concat name.getId)
    else
      Macro.throwUnsupported
  let ignoreIfSafe (width : TSyntax `term) : MacroM (TotalPatSeg × List Name) := do
    if widthSafeAgainst captured width then
      pure (.ignore width, captured)
    else
      Macro.throwUnsupported
  match segment with
  | `(bitsPatSeg| $name:ident : $w:num) =>
      captureIfSafe name (mkNatTerm w.getNat) .raw
  | `(bitsPatSeg| $name:ident : ($w:term)) =>
      captureIfSafe name w .raw
  | `(bitsPatSeg| $name:ident : $w:num / big) =>
      captureIfSafe name (mkNatTerm w.getNat) .unsigned
  | `(bitsPatSeg| $name:ident : $w:num / signed) =>
      captureIfSafe name (mkNatTerm w.getNat) .signed
  | `(bitsPatSeg| $name:ident : $w:num / signed-big) =>
      captureIfSafe name (mkNatTerm w.getNat) .signed
  | `(bitsPatSeg| $name:ident : $w:num / little) => do
      let byteCount ← byteCountFor w
      captureIfSafe name (mkNatTerm w.getNat) (.little byteCount)
  | `(bitsPatSeg| $name:ident : $w:num / signed-little) => do
      let byteCount ← byteCountFor w
      captureIfSafe name (mkNatTerm w.getNat) (.signedLittle byteCount)
  | `(bitsPatSeg| $name:ident : $byteCount:bitsPatByteCount / little) => do
      let byteCountTerm ← expandByteCount byteCount
      let width ← `(LeanBitsyntax.ByteWidth $byteCountTerm)
      captureIfSafe name width (.little byteCountTerm)
  | `(bitsPatSeg| $name:ident : $byteCount:bitsPatByteCount / signed-little) => do
      let byteCountTerm ← expandByteCount byteCount
      let width ← `(LeanBitsyntax.ByteWidth $byteCountTerm)
      captureIfSafe name width (.signedLittle byteCountTerm)
  | `(bitsPatSeg| _ : $w:num) =>
      ignoreIfSafe (mkNatTerm w.getNat)
  | `(bitsPatSeg| _ : ($w:term)) =>
      ignoreIfSafe w
  | `(bitsPatSeg| _ : $byteCount:bitsPatByteCount / little) => do
      let byteCountTerm ← expandByteCount byteCount
      let width ← `(LeanBitsyntax.ByteWidth $byteCountTerm)
      ignoreIfSafe width
  | `(bitsPatSeg| _ : $byteCount:bitsPatByteCount / signed-little) => do
      let byteCountTerm ← expandByteCount byteCount
      let width ← `(LeanBitsyntax.ByteWidth $byteCountTerm)
      ignoreIfSafe width
  | _ =>
      Macro.throwUnsupported

private def asTypedBranchSeg (captured : List Name) (segment : TSyntax `bitsPatSeg) : MacroM (TypedBranchSeg × List Name) := do
  let captureSeg (name : TSyntax `ident) (width : TSyntax `term) (mode : CaptureMode) :=
    (.capture name width mode, captured.concat name.getId)
  let ignoreSeg (width : TSyntax `term) :=
    (.ignore width, captured)
  let guardSeg (width expected : TSyntax `term) :=
    (.guard width expected, captured)
  match segment with
  | `(bitsPatSeg| $n:num) =>
    let width := mkNatTerm 8
    pure (guardSeg width (← `(LeanBitsyntax.Build.nat 8 $n)))
  | `(bitsPatSeg| $n:num : $w:num) =>
    let width := mkNatTerm w.getNat
    pure (guardSeg width (← `(LeanBitsyntax.Build.nat $width $n)))
  | `(bitsPatSeg| $n:num : $w:num / big) =>
    let width := mkNatTerm w.getNat
    pure (guardSeg width (← `(LeanBitsyntax.Build.nat $width $n)))
  | `(bitsPatSeg| $n:num : $w:num / little) => do
    let byteCount ← byteCountFor w
    let width := mkNatTerm w.getNat
    pure (guardSeg width (← `(LeanBitsyntax.Build.littleEndianNat $byteCount $n)))
  | `(bitsPatSeg| $n:num : $byteCount:bitsPatByteCount / little) => do
    let byteCountTerm ← expandByteCount byteCount
    let width ← `(LeanBitsyntax.ByteWidth $byteCountTerm)
    pure (guardSeg width (← `(LeanBitsyntax.Build.littleEndianNat $byteCountTerm $n)))
  | `(bitsPatSeg| $n:num : ($w:term)) =>
    pure (guardSeg w (← `(LeanBitsyntax.Build.nat $w $n)))
  | `(bitsPatSeg| $n:num : ($w:term) / big) =>
    pure (guardSeg w (← `(LeanBitsyntax.Build.nat $w $n)))
  | `(bitsPatSeg| ($t:term) : $w:num) => do
    let width := mkNatTerm w.getNat
    pure (guardSeg width (← `(LeanBitsyntax.Build.segment $width $t)))
  | `(bitsPatSeg| ($t:term) : $w:num / big) => do
    let width := mkNatTerm w.getNat
    pure (guardSeg width (← `(LeanBitsyntax.Build.segment $width $t)))
  | `(bitsPatSeg| ($t:term) : $w:num / signed) => do
    let width := mkNatTerm w.getNat
    pure (guardSeg width (← `(LeanBitsyntax.Build.signedSegment $width $t)))
  | `(bitsPatSeg| ($t:term) : $w:num / signed-big) => do
    let width := mkNatTerm w.getNat
    pure (guardSeg width (← `(LeanBitsyntax.Build.signedSegment $width $t)))
  | `(bitsPatSeg| ($t:term) : $w:num / little) => do
    let byteCount ← byteCountFor w
    let width := mkNatTerm w.getNat
    pure (guardSeg width (← `(LeanBitsyntax.Build.littleEndianSegment $byteCount $t)))
  | `(bitsPatSeg| ($t:term) : $w:num / signed-little) => do
    let byteCount ← byteCountFor w
    let width := mkNatTerm w.getNat
    pure (guardSeg width (← `(LeanBitsyntax.Build.signedLittleEndianSegment $byteCount $t)))
  | `(bitsPatSeg| ($t:term) : $byteCount:bitsPatByteCount / little) => do
    let byteCountTerm ← expandByteCount byteCount
    let width ← `(LeanBitsyntax.ByteWidth $byteCountTerm)
    pure (guardSeg width (← `(LeanBitsyntax.Build.littleEndianSegment $byteCountTerm $t)))
  | `(bitsPatSeg| ($t:term) : $byteCount:bitsPatByteCount / signed-little) => do
    let byteCountTerm ← expandByteCount byteCount
    let width ← `(LeanBitsyntax.ByteWidth $byteCountTerm)
    pure (guardSeg width (← `(LeanBitsyntax.Build.signedLittleEndianSegment $byteCountTerm $t)))
  | `(bitsPatSeg| ($t:term) : ($w:term)) =>
    pure (guardSeg w (← `(LeanBitsyntax.Build.segment $w $t)))
  | `(bitsPatSeg| ($t:term) : ($w:term) / big) =>
    pure (guardSeg w (← `(LeanBitsyntax.Build.segment $w $t)))
  | `(bitsPatSeg| ($t:term) : ($w:term) / signed) =>
    pure (guardSeg w (← `(LeanBitsyntax.Build.signedSegment $w $t)))
  | `(bitsPatSeg| ($t:term) : ($w:term) / signed-big) =>
    pure (guardSeg w (← `(LeanBitsyntax.Build.signedSegment $w $t)))
  | `(bitsPatSeg| $name:ident : $w:num / big) =>
    pure (captureSeg name (mkNatTerm w.getNat) .unsigned)
  | `(bitsPatSeg| $name:ident : $w:num / signed) =>
    pure (captureSeg name (mkNatTerm w.getNat) .signed)
  | `(bitsPatSeg| $name:ident : $w:num / little) => do
    let byteCount ← byteCountFor w
    pure (captureSeg name (mkNatTerm w.getNat) (.little byteCount))
  | `(bitsPatSeg| $name:ident : $w:num / signed-big) =>
    pure (captureSeg name (mkNatTerm w.getNat) .signed)
  | `(bitsPatSeg| $name:ident : $w:num / signed-little) => do
    let byteCount ← byteCountFor w
    pure (captureSeg name (mkNatTerm w.getNat) (.signedLittle byteCount))
  | `(bitsPatSeg| $name:ident : $w:num) =>
    pure (captureSeg name (mkNatTerm w.getNat) .raw)
  | `(bitsPatSeg| $name:ident : ($w:term)) =>
    pure (captureSeg name w .raw)
  | `(bitsPatSeg| $name:ident : $byteCount:bitsPatByteCount / little) => do
    let byteCountTerm ← expandByteCount byteCount
    let width ← `(LeanBitsyntax.ByteWidth $byteCountTerm)
    pure (captureSeg name width (.little byteCountTerm))
  | `(bitsPatSeg| $name:ident : $byteCount:bitsPatByteCount / signed-little) => do
    let byteCountTerm ← expandByteCount byteCount
    let width ← `(LeanBitsyntax.ByteWidth $byteCountTerm)
    pure (captureSeg name width (.signedLittle byteCountTerm))
  | `(bitsPatSeg| _ : $w:num) =>
    pure (ignoreSeg (mkNatTerm w.getNat))
  | `(bitsPatSeg| _ : ($w:term)) =>
    pure (ignoreSeg w)
  | `(bitsPatSeg| _ : $byteCount:bitsPatByteCount / little) => do
    let byteCountTerm ← expandByteCount byteCount
    let width ← `(LeanBitsyntax.ByteWidth $byteCountTerm)
    pure (ignoreSeg width)
  | `(bitsPatSeg| _ : $byteCount:bitsPatByteCount / signed-little) => do
    let byteCountTerm ← expandByteCount byteCount
    let width ← `(LeanBitsyntax.ByteWidth $byteCountTerm)
    pure (ignoreSeg width)
  | _ =>
    Macro.throwUnsupported

private def sumWidthTerms : List (TSyntax `term) → MacroM (TSyntax `term)
  | [] =>
      pure (mkNatTerm 0)
  | [width] =>
      pure width
  | width :: rest => do
      let tail ← sumWidthTerms rest
      `($width + $tail)

private def totalPatSegsAux (captured : List Name) : List (TSyntax `bitsPatSeg) → MacroM (List TotalPatSeg)
  | [] =>
    pure []
  | segment :: rest => do
    let (current, captured') ← asTotalPatSeg captured segment
    let tail ← totalPatSegsAux captured' rest
    pure (current :: tail)

private def totalPatSegs (pattern : TSyntax `bitsPattern) : MacroM (List TotalPatSeg) := do
  match pattern with
  | `(bitsPattern| << $segments:bitsPatSeg,* >>) =>
      totalPatSegsAux [] segments.getElems.toList
  | _ =>
      Macro.throwUnsupported

private def typedBranchSegsAux (captured : List Name) : List (TSyntax `bitsPatSeg) → MacroM (List TypedBranchSeg)
  | [] =>
    pure []
  | segment :: rest => do
    let (current, captured') ← asTypedBranchSeg captured segment
    let tail ← typedBranchSegsAux captured' rest
    pure (current :: tail)

private def typedBranchSegs (pattern : TSyntax `bitsPattern) : MacroM (List TypedBranchSeg) := do
  match pattern with
  | `(bitsPattern| << $segments:bitsPatSeg,* >>) =>
    typedBranchSegsAux [] segments.getElems.toList
  | _ =>
    Macro.throwUnsupported

private def expandTotalPatSegs (bits : TSyntax `term) (segments : List TotalPatSeg)
    (body : TSyntax `term) : MacroM (TSyntax `term) := do
  match segments with
  | [] =>
      pure body
  | [segment] =>
    match segment with
    | .capture name width .raw =>
      `(let $name := LeanBitsyntax.Match.exactWidth $width $bits (by omega); $body)
    | .capture name width mode => do
      let rawTerm ← `(LeanBitsyntax.Match.exactWidth $width $bits (by omega))
      let captured ← expandCaptureValue mode width rawTerm
      `(let $name := $captured;
        $body)
    | .ignore width => do
      let ignoredId := mkIdent `__ignored
      `(let $ignoredId := LeanBitsyntax.Match.exactWidth $width $bits (by omega); $body)
  | segment :: rest => do
      let tailWidth ← sumWidthTerms (rest.map totalPatSegWidth)
      let restId := mkIdent `__rest
      let restTerm : TSyntax `term := ⟨restId.raw⟩
      let tail ← expandTotalPatSegs restTerm rest body
      match segment with
      | TotalPatSeg.capture name width CaptureMode.raw =>
          `(let ($name, $restId) := LeanBitsyntax.Match.splitExact $width $tailWidth $bits (by omega); $tail)
      | .capture name width mode => do
          let rawId := mkIdent `__segment
          let rawTerm : TSyntax `term := ⟨rawId.raw⟩
          let captured ← expandCaptureValue mode width rawTerm
          `(let ($rawId, $restId) := LeanBitsyntax.Match.splitExact $width $tailWidth $bits (by omega);
            let $name := $captured;
            $tail)
      | .ignore width => do
          let ignoredId := mkIdent `__ignored
          `(let ($ignoredId, $restId) := LeanBitsyntax.Match.splitExact $width $tailWidth $bits (by omega); $tail)

private def expandTotalPattern (bits : TSyntax `term) (pattern : TSyntax `bitsPattern)
  (body : TSyntax `term) : MacroM (TSyntax `term) := do
  let segments ← totalPatSegs pattern
  match segments with
  | _ :: _ =>
    expandTotalPatSegs bits segments body
  | [] =>
    Macro.throwUnsupported

private def expandTypedBranchSegs (bits : TSyntax `term) (segments : List TypedBranchSeg)
    (body fallback : TSyntax `term) : MacroM (TSyntax `term) := do
  match segments with
  | [] =>
      let emptyId := mkIdent `__empty
      `(LeanBitsyntax.Match.continueIfExact 0 $bits $fallback (fun $emptyId =>
        $body))
  | [segment] =>
      match segment with
      | .guard width expected => do
          let rawId := mkIdent `__segment
          `(LeanBitsyntax.Match.continueIfExact $width $bits $fallback (fun $rawId =>
            if $rawId = $expected then
              $body
            else
              $fallback))
      | TypedBranchSeg.capture name width CaptureMode.raw =>
          `(LeanBitsyntax.Match.continueIfExact $width $bits $fallback (fun $name =>
            $body))
      | .capture name width mode => do
          let rawId := mkIdent `__segment
          let rawTerm : TSyntax `term := ⟨rawId.raw⟩
          let captured ← expandCaptureValue mode width rawTerm
          `(LeanBitsyntax.Match.continueIfExact $width $bits $fallback (fun $rawId =>
            let $name := $captured;
            $body))
      | .ignore width => do
          let ignoredId := mkIdent `__ignored
          `(LeanBitsyntax.Match.continueIfExact $width $bits $fallback (fun $ignoredId =>
            $body))
  | segment :: rest => do
      let rawId := mkIdent `__segment
      let rawTerm : TSyntax `term := ⟨rawId.raw⟩
      let restId := mkIdent `__rest
      let restTerm : TSyntax `term := ⟨restId.raw⟩
      let tail ← expandTypedBranchSegs restTerm rest body fallback
      match segment with
      | .guard width expected =>
          `(LeanBitsyntax.Match.continueIfFits $width $bits $fallback (fun $rawId $restId =>
            if $rawId = $expected then
              $tail
            else
              $fallback))
      | TypedBranchSeg.capture name width CaptureMode.raw =>
          `(LeanBitsyntax.Match.continueIfFits $width $bits $fallback (fun $name $restId =>
            $tail))
      | .capture name width mode => do
          let captured ← expandCaptureValue mode width rawTerm
          `(LeanBitsyntax.Match.continueIfFits $width $bits $fallback (fun $rawId $restId =>
            let $name := $captured;
            $tail))
      | .ignore width => do
          let ignoredId := mkIdent `__ignored
          `(LeanBitsyntax.Match.continueIfFits $width $bits $fallback (fun $ignoredId $restId =>
            $tail))

private def expandTypedBranch (bits : TSyntax `term) (pattern : TSyntax `bitsPattern)
  (body fallback : TSyntax `term) : MacroM (TSyntax `term) := do
  let segments ← typedBranchSegs pattern
  expandTypedBranchSegs bits segments body fallback

private partial def restHasExplicitFallback : TSyntax `bitsMatchRest → Bool
  | `(bitsMatchRest| | _ => $_fallback) =>
      true
  | `(bitsMatchRest| | $_pattern:bitsPattern => $_body $rest:bitsMatchRest) =>
      restHasExplicitFallback rest
  | `(bitsMatchRest| | $_pattern:bitsPattern => $_body) =>
      false
  | _ =>
      false

private def armsHasExplicitFallback : TSyntax `bitsMatchArms → Bool
  | `(bitsMatchArms| | $_pattern:bitsPattern => $_body $rest:bitsMatchRest) =>
      restHasExplicitFallback rest
  | `(bitsMatchArms| | $_pattern:bitsPattern => $_body) =>
      false
  | _ =>
      false

private def singleArm? : TSyntax `bitsMatchArms → Option (TSyntax `bitsPattern × TSyntax `term)
  | `(bitsMatchArms| | $pattern:bitsPattern => $body) =>
      some (pattern, body)
  | _ =>
      none

private partial def expandMatchRest (bits defaultFallback : TSyntax `term) : TSyntax `bitsMatchRest → MacroM (TSyntax `term)
  | `(bitsMatchRest| | _ => $fallback) =>
      pure fallback
  | `(bitsMatchRest| | $pattern:bitsPattern => $body) => do
      expandTypedBranch bits pattern body defaultFallback
  | `(bitsMatchRest| | $pattern:bitsPattern => $body $rest:bitsMatchRest) => do
      let next ← expandMatchRest bits defaultFallback rest
      expandTypedBranch bits pattern body next
  | _ => Macro.throwUnsupported

private def expandMatchArms (bits defaultFallback : TSyntax `term) : TSyntax `bitsMatchArms → MacroM (TSyntax `term)
  | `(bitsMatchArms| | $pattern:bitsPattern => $body) => do
      expandTypedBranch bits pattern body defaultFallback
  | `(bitsMatchArms| | $pattern:bitsPattern => $body $rest:bitsMatchRest) => do
      let next ← expandMatchRest bits defaultFallback rest
      expandTypedBranch bits pattern body next
  | _ => Macro.throwUnsupported

macro_rules
  | `(bitmatchTerm| bitmatch $scrutinee:term with $arms:bitsMatchArms) => do
        let scrutineeId := mkIdent `__scrutinee
        let scrutineeTerm : TSyntax `term := ⟨scrutineeId.raw⟩
        if armsHasExplicitFallback arms then
          let expanded ← expandMatchArms scrutineeTerm scrutineeTerm arms
          `(let $scrutineeId := $scrutinee;
            $expanded)
        else
          match singleArm? arms with
          | some (pattern, body) =>
              let expanded ←
                try
                  expandTotalPattern scrutineeTerm pattern body
                catch _ =>
                  Macro.throwErrorAt arms "omitted fallback currently requires a single structurally total capture/ignore branch; add an explicit `| _ => ...` fallback"
              `(let $scrutineeId := $scrutinee;
                $expanded)
          | none =>
              Macro.throwErrorAt arms "omitted fallback currently requires a single structurally total capture/ignore branch; add an explicit `| _ => ...` fallback"

end LeanBitsyntax
