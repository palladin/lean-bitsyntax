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

end LeanBitsyntax.Match

namespace LeanBitsyntax

private inductive CaptureMode where
  | raw
  | unsigned
  | signed
  | little (byteCount : TSyntax `term)
  | signedLittle (byteCount : TSyntax `term)

private inductive PatSegKind where
  | guard (expected : TSyntax `term)
  | capture (name : TSyntax `ident) (mode : CaptureMode)
  | ignore

private structure PatSeg where
  source : Syntax
  width : TSyntax `term
  kind : PatSegKind

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
Fixed-width matching subset for `bitmatch`.

Currently supported pattern segments:
- bare numeric literals, defaulting to 8 bits
- sized numeric literals `n : w`
- modified numeric literals such as `n : w / little`
- width-explicit comparison terms `(expr) : w`
- captures `name : w` and modified captures such as `name : w / little`
- ignored segments `_ : w` and `_ : (expr)`
- width expressions built from statically available names in the surrounding context

Widths may not depend on earlier captures from the same pattern branch.

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

private def identMentionsAny (names : List Name) (val : Name) : Bool :=
  let val := val.eraseMacroScopes
  names.any fun captured =>
    captured.eraseMacroScopes.isPrefixOf val

private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\''

private def startsWithChars : List Char → List Char → Bool
  | [], _ =>
      true
  | _ :: _, [] =>
      false
  | x :: xs, y :: ys =>
      x == y && startsWithChars xs ys

private def textMentionsName (text needle : String) : Bool :=
  let needleChars := needle.toList
  let rec loop (prev? : Option Char) : List Char → Bool
    | [] =>
        false
    | chars@(c :: rest) =>
        let boundaryBefore :=
          match prev? with
          | some prev => !isIdentChar prev
          | none => true
        let boundaryAfter :=
          match chars.drop needleChars.length |>.head? with
          | some next => !isIdentChar next
          | none => true
        if startsWithChars needleChars chars && boundaryBefore && boundaryAfter then
          true
        else
          loop (some c) rest
  if needleChars.isEmpty then
    false
  else
    loop none text.toList

private def syntaxTextMentionsAny (names : List Name) (stx : Syntax) : Bool :=
  match stx.reprint with
  | some text =>
      names.any fun captured => textMentionsName text captured.eraseMacroScopes.toString
  | none =>
      false

private partial def syntaxMentionsAny (names : List Name) : Syntax → Bool
  | Syntax.ident _ _ val _ =>
    identMentionsAny names val
  | Syntax.node _ _ args =>
    args.toList.any (syntaxMentionsAny names)
  | _ =>
    false

private def widthSafeAgainst (captured : List Name) (segment : PatSeg) : Bool :=
  !(syntaxMentionsAny captured segment.width.raw ||
    syntaxTextMentionsAny captured segment.width.raw ||
    syntaxTextMentionsAny captured segment.source)

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

private def asPatSeg (segment : TSyntax `bitsPatSeg) : MacroM PatSeg := do
  let captureSeg (name : TSyntax `ident) (width : TSyntax `term) (mode : CaptureMode) : PatSeg :=
    { source := segment.raw, width := width, kind := .capture name mode }
  let ignoreSeg (width : TSyntax `term) : PatSeg :=
    { source := segment.raw, width := width, kind := .ignore }
  let guardSeg (width expected : TSyntax `term) : PatSeg :=
    { source := segment.raw, width := width, kind := .guard expected }
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

private def patSegCaptureName? : PatSeg → Option Name
  | segment =>
      match segment.kind with
      | .capture name _ => some name.getId
      | _ => none

private def ensureStaticWidthsAux (captured : List Name) : List PatSeg → MacroM Unit
  | [] =>
      pure ()
  | segment :: rest => do
      if widthSafeAgainst captured segment then
        let captured' :=
          match patSegCaptureName? segment with
          | some name => captured.concat name
          | none => captured
        ensureStaticWidthsAux captured' rest
      else
        Macro.throwErrorAt segment.width
          "pattern widths must be statically determined; width terms cannot depend on earlier captures"

private def patSegs (pattern : TSyntax `bitsPattern) : MacroM (List PatSeg) := do
  match pattern with
  | `(bitsPattern| << $segments:bitsPatSeg,* >>) =>
      let parsed ← segments.getElems.toList.mapM asPatSeg
      ensureStaticWidthsAux [] parsed
      pure parsed
  | _ =>
      Macro.throwUnsupported

private def ensureTotalPatSegsAux : List PatSeg → MacroM Unit
  | [] =>
      pure ()
  | segment :: rest =>
      match segment.kind with
      | .guard _ =>
          Macro.throwUnsupported
      | .capture _ _ =>
          ensureTotalPatSegsAux rest
      | .ignore =>
          ensureTotalPatSegsAux rest

private def totalPatSegs (pattern : TSyntax `bitsPattern) : MacroM (List PatSeg) := do
  let segments ← patSegs pattern
  ensureTotalPatSegsAux segments
  pure segments

private def expandPatSegs (bits : TSyntax `term) (segments : List PatSeg)
    (body : TSyntax `term) (fallback? : Option (TSyntax `term)) : MacroM (TSyntax `term) := do
  match segments with
  | [] =>
      pure body
  | [segment] =>
      match segment.kind with
      | .guard expected => do
          let rawId := mkIdent `__segment
          match fallback? with
          | some fallback =>
                `(let $rawId := LeanBitsyntax.Match.exactWidth $(segment.width) $bits (by
                  try simp [LeanBitsyntax.ByteWidth] at *
                  try omega);
                if $rawId = $expected then
                  $body
                else
                  $fallback)
          | none =>
              Macro.throwUnsupported
      | .capture name .raw =>
            `(let $name := LeanBitsyntax.Match.exactWidth $(segment.width) $bits (by
              try simp [LeanBitsyntax.ByteWidth] at *
              try omega);
            $body)
      | .capture name mode => do
          let rawId := mkIdent `__segment
          let rawTerm : TSyntax `term := ⟨rawId.raw⟩
          let captured ← expandCaptureValue mode segment.width rawTerm
          `(let $rawId := LeanBitsyntax.Match.exactWidth $(segment.width) $bits (by
            try simp [LeanBitsyntax.ByteWidth] at *
            try omega);
          let $name := $captured;
          $body)
      | .ignore => do
          let ignoredId := mkIdent `__ignored
          `(let $ignoredId := LeanBitsyntax.Match.exactWidth $(segment.width) $bits (by
            try simp [LeanBitsyntax.ByteWidth] at *
            try omega);
          $body)
  | segment :: rest => do
      let tailWidth ← sumWidthTerms (rest.map fun seg => seg.width)
      let rawId := mkIdent `__segment
      let rawTerm : TSyntax `term := ⟨rawId.raw⟩
      let restId := mkIdent `__rest
      let restTerm : TSyntax `term := ⟨restId.raw⟩
      let tail ← expandPatSegs restTerm rest body fallback?
      match segment.kind with
      | .guard expected => do
          match fallback? with
          | some fallback =>
                `(let ($rawId, $restId) := LeanBitsyntax.Match.splitExact $(segment.width) $tailWidth $bits (by
                  try simp [LeanBitsyntax.ByteWidth] at *
                  try omega);
                if $rawId = $expected then
                  $tail
                else
                  $fallback)
          | none =>
              Macro.throwUnsupported
      | .capture name .raw =>
            `(let ($name, $restId) := LeanBitsyntax.Match.splitExact $(segment.width) $tailWidth $bits (by
              try simp [LeanBitsyntax.ByteWidth] at *
              try omega);
            $tail)
      | .capture name mode => do
          let captured ← expandCaptureValue mode segment.width rawTerm
          `(let ($rawId, $restId) := LeanBitsyntax.Match.splitExact $(segment.width) $tailWidth $bits (by
            try simp [LeanBitsyntax.ByteWidth] at *
            try omega);
          let $name := $captured;
          $tail)
      | .ignore => do
          let ignoredId := mkIdent `__ignored
          `(let ($ignoredId, $restId) := LeanBitsyntax.Match.splitExact $(segment.width) $tailWidth $bits (by
            try simp [LeanBitsyntax.ByteWidth] at *
            try omega);
          $tail)

private def expandPattern (bits : TSyntax `term) (pattern : TSyntax `bitsPattern)
    (body : TSyntax `term) (fallback? : Option (TSyntax `term)) : MacroM (TSyntax `term) := do
  let segments ←
    match fallback? with
    | some _ =>
        patSegs pattern
    | none =>
        totalPatSegs pattern
  let totalWidth ← sumWidthTerms (segments.map fun segment => segment.width)
  let typedBitsId := mkIdent `__matched
  let typedBitsTerm : TSyntax `term := ⟨typedBitsId.raw⟩
  match segments, fallback? with
  | [], none =>
      Macro.throwUnsupported
  | _, _ =>
      let expanded ← expandPatSegs typedBitsTerm segments body fallback?
      `(let $typedBitsId := LeanBitsyntax.Match.exactWidth $totalWidth $bits (by
        try simp [LeanBitsyntax.ByteWidth] at *
        try omega);
      $expanded)

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
      expandPattern bits pattern body (some defaultFallback)
  | `(bitsMatchRest| | $pattern:bitsPattern => $body $rest:bitsMatchRest) => do
      let next ← expandMatchRest bits defaultFallback rest
      expandPattern bits pattern body (some next)
  | _ => Macro.throwUnsupported

private def expandMatchArms (bits defaultFallback : TSyntax `term) : TSyntax `bitsMatchArms → MacroM (TSyntax `term)
  | `(bitsMatchArms| | $pattern:bitsPattern => $body) => do
      expandPattern bits pattern body (some defaultFallback)
  | `(bitsMatchArms| | $pattern:bitsPattern => $body $rest:bitsMatchRest) => do
      let next ← expandMatchRest bits defaultFallback rest
      expandPattern bits pattern body (some next)
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
                  expandPattern scrutineeTerm pattern body none
                catch _ =>
                  Macro.throwErrorAt arms "omitted fallback currently requires a single structurally total capture/ignore branch; add an explicit `| _ => ...` fallback"
              `(let $scrutineeId := $scrutinee;
                $expanded)
          | none =>
              Macro.throwErrorAt arms "omitted fallback currently requires a single structurally total capture/ignore branch; add an explicit `| _ => ...` fallback"

end LeanBitsyntax
