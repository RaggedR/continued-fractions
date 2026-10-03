# Handover: finish `all-the-proofs.tex`

**One thing is left: §6 step 5.** Everything else in that document is proved.
Written 3 October 2026.

## The target

§6 reduces the converse of Morse–Hedlund to five steps. Steps 1–4 are proved
(`prop:blocks`, `prop:derived` and the lemmas around them). Step 5 reads:

> Iterating produces `a₁, a₂, a₃, … ≥ 1` and hence an irrational
> `α = [0; a₁, a₂, …]`, and the nested prefixes `τ_{a₁}τ_{a₂}···τ_{a_j}`
> together with the shifts `k₀, k₁, …` pin a single `x`.

So: the *digits* come free from iterating step 4, and what is unproved is that
the data `(a_j, k_j)` determines a single pair `(α, x)` with
`ℓ = C(α,x)` or `Cp(α,x)`. That is a convergence argument — the Ostrowski
representation of `x`. It is the only analytic step in the document.

Do it **on paper first**, in `all-the-proofs.tex`, then formalise. Steps 2 and 4
were done that way on 3 October and both came out shorter than the literature
suggests. Lean has been excellent at exposing what is unproved and poor at
finding an argument.

## What you already have

In the paper:

| | |
|---|---|
| `thm:return`, `cor:gaps` | the return time, and that gaps are `a₁` or `a₁+1` |
| `lem:blocks` | `ℓ = 0^{k₀} τ_a(ℓ')` — the block decomposition |
| `thm:derive` | the derivation theorem, with the new intercept computed **exactly**: `derive(C(α,x)) = C⁺({1/α}, {−u₀})` |
| `lem:rs`, `cor:onesp` | `F(m+1) − F(m)` counts right-special factors; complexity `m+1` ⟺ exactly one of each length |
| `lem:rschain` | those right-special factors form a suffix chain |
| `lem:aper`, `lem:evper` | no right-special factor of length `m` ⟹ eventually periodic ⟹ bounded complexity |
| `prop:blocks` | block lengths are `a−1` and `a` |
| `lem:bridge`, `prop:derived` | `ℓ'` is Sturmian |
| §8 | the tower, and `sqrt_tower_period` |

In Lean (`lean/`, 5 files, 51 theorems, 0 sorries, build with `lean/build.sh`):
`derive_code`, `derive_codeUp`, `tower_eq`, `tower_period`, `complexity`,
`ncard_factors_codeUp`, `block_length`, `block_zero`, `sigma_pre`, `fib_limit`.
`lean/PLAN.md` Phase 9 is the Lean-side plan and is current.

## Three facts established while proving steps 2 and 4

All three were checked numerically; the first two are also proved in the paper.

1. **`11` is absent exactly when the slope is `≤ 1/2`, and then `a = ⌊1/α⌋ = a₁`.**
   Checked on 24 exact irrational slopes, no mismatch. So the block parameter of
   `prop:blocks` *is* the continued-fraction digit — but only after the letter
   exchange of step 1 has been applied.
2. **The letter exchange is `α ↦ 1−α`**, because the complement of `C(β,y)` is
   `C⁺(1−β,−y)` (the identity proved for `cor:complexityup`, and
   `codeUp_add_code_reflect` in `lean/Sturmian.lean`). It swaps lower and upper
   codings.
3. **That swap is the same alternation `tower_eq` already carries** as
   `if Even j then codeUp else code`. Step 5 must track it: iterating step 4
   alternates the coding type, so the `a_j` you read off are the digits of
   whichever of `α`, `1−α` is below `1/2` at that level.

Fact 3 is the thing most likely to be got wrong. `prop:blocks` gives `a ≥ 2`
always, while CF digits can be `1`; there is no contradiction, because `a₁ = 1`
is exactly the case where the exchange fires. Do not try to read the digits off
without the exchange.

## Suggested route for step 5

Two shapes, and the second is probably better here.

**Nested intervals.** Knowing `k₀, …, k_j` and `a₁, …, a_{j+1}` confines `x` to
an interval whose length → 0 (these are the Ostrowski intervals). Take `x` in
the intersection, then show `C(α,x)` has the same data as `ℓ` and conclude
`ℓ = C(α,x)` because the data determines arbitrarily long prefixes. Standard,
and self-contained.

**Invert the tower.** §5 computes the forward map `(α,x) ↦ (a_j, k_j)` exactly —
`thm:derive` gives the new intercept as `{−u₀}`, not merely its existence, and
that exactness is why §8 works. So step 5 is the statement that this map is
injective with the right image, and the convergence is only needed to show the
backward map is defined. This reuses machinery that already exists rather than
building Ostrowski theory from scratch, and it is the reading of "run §4 and §5
backwards" that the rest of §6 follows.

For the Lean side, Mathlib has what the analytic part needs:
`GenContFract.of_convergence`, `of_convergence_epsilon`, `abs_sub_convs_le`,
`ContinuantsRecurrence`, `Determinant`, and `TerminatesIffRat` for irrationality
of an infinite expansion. None of it has been needed so far — this is the first
place it will be. It will also want `Palindrome.stream_fst` generalised off `√n`.

## Method that worked

- **Numerics before prose, every time.** Both new propositions were checked in
  Python before a word went into the `.tex`: the predicted witnesses for step 2
  (`{00,10}` for blocks `{1,3}`, `{000,100}` for `{2,4}`), and the bridge in
  both directions for step 4. Two claims were wrong on the first test and one of
  those was a bug in the test, not the claim — check both before believing
  either.
- **Never test on a decimal truncation.** `0.302770` looks like an irrational
  and is not; its coding is eventually periodic and it produced a spurious
  counterexample. Build slopes as `sqrt(n) - floor(sqrt(n))`.
- **Three strikes.** Lothaire ch. 2 is not freely available and Vuillon's
  "Balanced words" defeated three download routes. Both are recorded in
  `papers/sturmian/README.md` with citations and a DOI rather than retried.
- **`LESSONS.md` governs the prose.** Read it before writing any sentence in the
  `.tex`. Robin rewrote nearly every sentence drafted on 30 September; the file
  is the distillation. Shortest relevant rules: no stage direction, no advance
  summaries of method, no restating a display in prose, concrete before general,
  rigour in the statement and not in a remark, and no paragraph over three lines
  in a definitional passage.

## Sources

`papers/sturmian/README.md` accounts for all of them, including the two that
could not be obtained (Morse–Hedlund 1940 is paywalled and in copyright;
Lothaire ch. 2 is not posted). The errata to Lothaire is the most informative
free document about that chapter: its Proposition 2.1.10 is a quantitative bound
`| |u|₁ − α|u| | < 1`, which is the converse of our `lem:count`, and 2.1.18 uses
it to show two candidate slopes coincide. **That is step 5's machinery**, so
start there if you want the classical route instead.
