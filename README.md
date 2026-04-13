# LeanBitsyntax

LeanBitsyntax is a Lean 4 experiment inspired by Erlang bit syntax. It borrows the `<<...>>` construction surface and selected semantic ideas, but re-expresses them in a typed, proof-oriented Lean setting. The current implementation keeps the exact `<<...>>` construction surface, but it does not introduce a separate dynamic bitstring runtime as the main semantic model. Instead, it treats `BitVec n` as the default representation whenever widths are known.

## Design

- BitVec-first core: fixed-width values are represented directly as `BitVec n`.
- Construction lowers to regular helpers: `<<...>>` expands to functions in `LeanBitsyntax.Build`, rather than generating ad hoc bit-twiddling code everywhere.
- Matching is a dedicated DSL: `bitmatch ... with` is implemented separately from Lean's native `match`, with typed `BitVec` remainder splitting rather than a dynamic intermediate bitstring wrapper.
- Left-to-right semantics: matcher branches consume segments in order, fail on the first mismatch, and then either use an explicit fallback or, for the restricted total-rewrite form, omit the fallback entirely.
- Static width discipline: matcher widths must be justified by arithmetic proofs from the branch's type information and any bounds implied by earlier captured `BitVec` widths.
- Explicit byte alignment for little-endian widths: use `bytes(expr)` when a statically known byte count should be interpreted as a bit width.

## Public Modules

- `LeanBitsyntax.Width`: width arithmetic helpers such as `ByteWidth`.
- `LeanBitsyntax.Core`: `BitVec` concat/split helpers used by the public DSLs.
- `LeanBitsyntax.Build`: typed segment constructors and endian/sign helpers.
- `LeanBitsyntax.Syntax`: exact `<<...>>` construction syntax.
- `LeanBitsyntax.Match`: `bitmatch` syntax and matcher lowering.

## Build And Smoke Tests

```sh
lake build
lake env lean Examples/Reverse32Bit.lean
lake env lean Examples/IPv4Checksum.lean
lake env lean Examples/IPv4PacketParsing.lean
lake env lean Examples/IPv6PacketParsing.lean
lake env lean LeanBitsyntax/Examples.lean
lake env lean Test/Parser.lean
lake env lean Test/Match.lean
lake env lean Test/MatchErrors.lean
```

## Using As A Dependency

For local development, add this package to your `lakefile.toml`:

```toml
[[require]]
name = "LeanBitsyntax"
path = "/absolute/path/to/lean-bitsyntax"
```

Then import the public root module from your downstream code:

```lean
import LeanBitsyntax

def packet : BitVec 32 :=
	<<1, 17, 42:16>>

def decoded : Nat :=
	bitmatch packet with
	| <<1, kind : 8, payload : 16>> => kind.toNat + payload.toNat
	| _ => 0
```

The root import re-exports the public modules listed below. If you want a pinned
non-local dependency later, replace `path = ...` with a Git-based `require` once
the repository has a stable remote URL and tags you want consumers to target.

## Construction DSL

The current `<<...>>` subset supports:

- bare numeric literals, defaulting to 8 bits
- sized numeric literals such as `42:16`
- width-explicit identifiers such as `sourceWord : 16`
- parenthesized terms such as `(0xAB#8)` or `(value) : 16`
- `big`, `little`, `signed`, `signed-big`, and `signed-little` on width-explicit identifier or term segments
- byte-aligned little-endian construction for widths that are multiples of 8

Example:

```lean
def packet : BitVec 32 := <<1, 17, 42:16>>
def mixed  : BitVec 32 := <<(0xAB#8), 1, 2, 3>>
def word   : BitVec 16 := <<sourceWord : 16 / little>>
def neg    : BitVec 8  := <<(signedByteValue) : 8 / signed>>
def signed : BitVec 16 := <<(-2) : 16 / signed-little>>
```

## Matching DSL

The current `bitmatch` subset supports:

- one or more pattern branches with an explicit final fallback for ordinary partial matches
- literal segments such as `1`, `42:16`, or `0x1234 : 16 / little`
- comparison terms such as `(marker) : 8` or `(-2) : 16 / signed-little`
- capture segments such as `kind : 8`, `word : 16 / little`, or `payload : (8 * payloadBytes)` when `payloadBytes` is already statically available
- ignored segments such as `_ : 16`, `_ : (headerBits)`, or `_ : bytes(4) / little`
- width expressions using ordinary Lean `Nat` terms from the surrounding context or earlier captures when the resulting split proofs can be discharged statically
- byte-aligned little-endian and signed-little forms through `bytes(expr)` under the same proof-driven discipline
- full-input matching only: leftover bits cause the branch to fail and fall through

If the explicit fallback is omitted, `bitmatch` currently accepts only a single
structurally total capture/ignore rewrite branch. That form is meant for direct
bit-preserving rewrites where the pattern fully determines the input shape and
the result type matches the scrutinee type. Writing an explicit final fallback
for that same single total branch is rejected as unnecessary.

Widths are checked statically. Dependent widths are accepted only when the
generated `splitExact` and `exactWidth` obligations can be proved from the
available arithmetic facts. For example,
`<<len : 2, payload : (len.toNat), _ : (30 - len.toNat)>>` is accepted on a
32-bit input because `len.toNat < 4` makes each split proof go through, while
`<<len : 8, payload : (8 * len.toNat)>>` on a 32-bit input is rejected because
the final full-input width equality cannot be proved. See `Test/Match.lean`
and `Test/MatchErrors.lean` for guarded success and failure cases.

Current capture semantics:

- plain captures bind the raw extracted `BitVec width`
- modifier-aware captures bind the normalized `BitVec width`
- use `.toNat` or `.toInt` explicitly at the use site

## Examples

Fixed-width matching:

```lean
def payload : Nat :=
	bitmatch packet with
	| <<2, _ : 8, _ : 16>> => 0
	| <<1, kind : 8, payload : 16>> => payload.toNat
	| <<(marker) : 8, _ : 8, _ : 16>> => 1
	| _ => 0
```

Modifier-aware capture:

```lean
def decodedWord : Nat :=
	bitmatch word with
	| <<decoded : 16 / little>> => decoded.toNat
	| _ => 0
```

Statically parameterized width:

```lean
def payloadFromKnownWidth (payloadBytes : Nat) (packet : BitVec (8 + (8 * payloadBytes))) : Nat :=
	bitmatch packet with
	| <<len : 8, payload : (8 * payloadBytes)>> => payload.toNat
	| _ => 0
```

Statically sized literal comparison:

```lean
def payloadTagMatches : Nat :=
	bitmatch <<3, 0xAABBCC:24>> with
	| <<len : 8, 0xAABBCC : 24>> => len.toNat
	| _ => 0
```

Byte-aligned little-endian capture:

```lean
def littlePayloadMatches : Nat :=
	bitmatch <<0xAABBCCDD:32 / little>> with
	| <<payload : bytes(4) / little>> => payload.toNat
	| _ => 0
```

Byte-aligned signed-little comparison:

```lean
def signedPayloadMatches : Nat :=
	bitmatch <<(-2) : 16 / signed-little>> with
	| <<(-2) : bytes(2) / signed-little>> => 1
	| _ => 0
```

## Current Limits

- This is not full Erlang bitsyntax parity.
- The construction DSL is still a curated subset, not a general segment grammar.
- The matcher is separate from Lean's native `match`; there is no pattern integration with ordinary inductive matches.
- Captures currently elaborate to `BitVec` values, not directly to `Nat` or `Int`.
- Dependent widths still fail when the required full-input or remainder-width arithmetic cannot be proved from the captured segment bounds.
- Little-endian widths still require the explicit `bytes(expr)` form.
- Floats, UTF encodings, and broader segment typing are not implemented.
- Pretty-printing and delaboration support are still minimal.

## Erlang References

The current surface syntax and some semantic choices are informed by the following Erlang/OTP references. They are sources of inspiration for this Lean design, not evidence that LeanBitsyntax is a direct port of Erlang's bitsyntax implementation.

- [Programming Efficiently with Binaries and Bit Strings](https://erlang.org/euc/07/papers/1700Gustafsson.pdf) - Erlang User Conference 2007 paper on bit strings, binary comprehensions, and efficient binary construction and matching.
- [Bit Syntax](https://www.erlang.org/doc/system/bit_syntax.html) - Erlang/OTP guide-level documentation with construction and matching examples such as `<<1, 17, 42:16>>`.
- [Bit Syntax Expressions](https://www.erlang.org/doc/system/expressions.html#bit-syntax-expressions) - the Reference Manual section that specifies segment syntax, defaults, truncation behavior, signedness, endianness, and matching rules.
- [Constructing and Matching Binaries](https://www.erlang.org/doc/system/binaryhandling.html) - the Efficiency Guide chapter covering runtime representation and optimization behavior for binary construction and matching.

## Reference Files

- `Examples/Reverse32Bit.lean` contains the separate Example 5.1 `reverse_32bit` translation inspired by the Erlang paper.
- `Examples/IPv4Checksum.lean` contains an IPv4 header checksum example inspired by Program 3 from the Erlang paper.
- `Examples/IPv4PacketParsing.lean` contains a fixed-header IPv4 parsing example.
- `Examples/IPv6PacketParsing.lean` contains an IPv6 base-header parsing example.
- `LeanBitsyntax/Examples.lean` contains the main usage examples.
- `Test/Parser.lean` checks the construction parser surface.
- `Test/Match.lean` checks matcher behavior for accepted static-width and little-endian cases.
- `Test/MatchErrors.lean` keeps the rejected dependent-width forms as guarded compile-error tests.

## License

This project is licensed under the MIT License. See `LICENSE`.