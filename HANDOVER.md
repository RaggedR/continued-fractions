# Handover: formalise `all-the-proofs.tex` §6–§7 in Lean

**The paper is finished.** §6 step 5 — the last unproved item — was proved on
3 October 2026 and is now §7 of `all-the-proofs.tex`. `lean/PLAN.md` Phase 9 is
the remaining work and it is now pure formalisation.

Phase 9 has started, in `Sturmian.lean` §6.1: `lem:rs`, `cor:onesp`,
`lem:evper`, and the pair of words `prop:blocks` runs on. The proposition
itself is not formalised; `PLAN.md` lists what it still needs, and the first
item is subword closure of `factors`, which discharges every occurrence
deduction in the proof at once.

## What step 5 turned out to be

Not Ostrowski, and not the tower inverted. Both routes the previous handover
suggested were abandoned. Write `S(N)` for the number of `1`s in the first `N`
letters of `ℓ` and

    D(N) = S(N) − Nα ,   Δ_α(u) = |u|₁ − α|u| .

By `lem:mech`, `ℓ = C(α,x)` iff `⌊Nα + x⌋ = S(N)` for every `N`, which is the
linear condition `x ∈ ⋂_N [D(N), D(N)+1)`. So the intercept is a formula,

    x = sup_{N ≥ 0} (S(N) − Nα) ,

and everything reduces to `sup D − inf D ≤ 1`, i.e. to `|Δ_α(u)| < 1` for every
factor `u`. That is `prop:bound`, and it is an induction on `|u|` running down
the levels, not an analytic argument.

| | |
|---|---|
| `lem:slope` | `α` exists and is irrational: `β ↦ 1/(a+β)` contracts by `1/a² ≤ 1/4` |
| `lem:dev` | `Δ_α(τ_a(w)) = −α Δ_β(w)` — the deviation scales by `−α` per level |
| `prop:bound` | `|Δ_α(u)| < 1`, by induction on `|u|` |
| `lem:countup` | the `C⁺` count, `⌈Nα+x⌉ − ⌈x⌉` |
| `thm:step5` | `x = sup D`; `C` if the supremum is attained, `C⁺` if not |

Three things make it work, and all three were already in the paper:

1. **`prop:blocks` gives `a ≥ 2`** (after step 1's letter exchange). Hence
   `|τ_a(u')| ≥ 2|u'|`, so the induction on word length descends strictly even
   though the level changes — no base case at infinite depth is needed. The same
   `a ≥ 2` is what makes `lem:slope` a contraction.
2. **The gap inequality `aα < 1`** from §4 is the only slack in the system. The
   worst case of the lower bound is `α(2a+β) = αa + 1 < 2`, where
   `α(a+β) = 1` is an identity, not an estimate. The bound `< 1` is tight.
3. **`q` must be a *proper* prefix of its block** in `u = 0^s τ_a(u') q`.
   Otherwise absorb it into `u'`. This gives `t ≤ a−1`, and without it the
   case `s = a, t = a` is false. It is the one piece of real bookkeeping, and
   the first draft got it wrong.

The `C`/`C⁺` dichotomy is exactly whether `sup D` is attained. `thm:counterex`
is that supremum being `1` and unattained — not a separate pathology.

## What was wrong in the previous handover

Recorded because two of its three "established facts" steered toward the longer
route.

* **Mathlib's continued-fraction API is not needed.** `of_convergence`,
  `ContinuantsRecurrence`, `Determinant`, `TerminatesIffRat`, and a generalised
  `Palindrome.stream_fst` were all predicted for step 5. §7 uses none of them.
* **Lothaire's Proposition 2.1.10 is not needed either.** The errata pointed at
  `| |u|₁ − α|u| | < 1` as "step 5's machinery", which is right — it is exactly
  `prop:bound` — but it is provable in half a page from `lem:blocks`, not
  something to reconstruct from a book we cannot obtain.
* **`Sturmian ⟹ balanced` is a trap.** It gives `prop:bound` in three lines via
  the density, and it is the direction the literature defers to Lothaire ch. 2.
  CRM Theorem 6.10 states it and proves only the converse. Do not go that way:
  the derivation gives the bound directly.

## Numerics

**`step5_check.py` reproduces all of it** — run it, it asserts rather than
prints opinions. `prop:bound` and the decomposition over **3,022,668 factors**,
44 sequences, `n ∈ {2,3,5,6,8,10,11,12,13,29,43}` and four intercepts each:
`s ≤ a`, `t ≤ a−1`, `s = a ⟹ 1u'` a factor, the `lem:dev` identity, and
`|Δ| < 1` with `sup → 1` never attained. `thm:step5` by reconstructing `x` from
the sequence alone, to `10⁻⁴` by `N = 4000`. `thm:counterex` as case D.

No test touches a decimal truncation: slopes are `sqrt(n) - floor(sqrt(n))` and
the codings come from integer comparison in `ℤ[√n]`.

Two test bugs in one session, both reporting a false failure: a bracket that
trivially exceeded `1` for `|u| = 1`, and a decomposition that set `s = a`
where it should have been `min(a, |u|)`. **Check the test before believing a
counterexample** — that is now twice this has happened and twice the claim was
right.

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
Lothaire ch. 2 is not posted). Neither is needed now. The errata's Proposition
2.1.10 is `| |u|₁ − α|u| | < 1`, which is our `prop:bound`; the agreement is a
check on the statement, and the proof in §7 is our own.
