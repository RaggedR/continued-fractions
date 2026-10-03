# Handover: formalise `all-the-proofs.tex` §6–§7 in Lean

**The paper is finished.** §6 step 5 — the last unproved item — was proved on
3 October 2026 and is now §7 of `all-the-proofs.tex`. `lean/PLAN.md` Phase 9 is
the remaining work and it is now pure formalisation.

**Steps 1 to 4 of the converse are formalised**, in `Sturmian.lean` §6.1, on
`lem:rs`, `cor:onesp`, `lem:evper`, `lem:aper`, `lem:rschain` and
`lem:bridge`. `isSturmian_deriveSeq` is `prop:derived`.

What remains is **step 5 (§7), which has no Lean at all**, the letter-exchange
normalisation threaded through the tower, and the assembly into
`mechanical_of_isSturmian` and `thm:mh`. Step 5 is a different kind of work
from everything above: `lem:slope` is a contraction argument over `ℝ` with an
irrationality descent, and `prop:bound` is an induction on word length with
`Δ_α(u) = |u|₁ − α|u|` real-valued. The positional-and-`omega` discipline that
carried steps 1 to 4 will not carry it.

`PLAN.md` records where the Lean route beats the paper's — `blockLens_le`
collapses two paragraphs, `lem:bridge` goes positionally so `τ_a` is never a
word, and the whole of step 4 avoids comparing weights — and the two proof
slips formalising turned up in §6, both now fixed in the `.tex`.

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
| `thm:step5` | `x = sup D`; **three** cases — `C(α,x)` if attained, `C⁺(α,x)` if not and `x < 1`, `C⁺(α,0)` if not and `x = 1` |

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

The `C`/`C⁺` split is whether `sup D` is attained, and the unattained branch
splits again on `x = 1`, because `thm:mh` requires `x ∈ [0,1)` and so cannot
return `C⁺(α,1)`. `thm:counterex` is exactly that third case: `1c` has
`D(N) = 1 − {Nα}`, supremum `1`, attained nowhere — not a separate pathology.
**An earlier version of this file called it two cases. It is three, and the
third is the one the counterexample lives in.**

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

## The Lean brief for step 5

Nothing of §7 is formalised. Everything in `Sturmian.lean` §6.1 — the
right-special, block and window machinery — is irrelevant to it: that was
positional reasoning discharged by `omega`, and §7 is real-valued. The relevant
discipline is the one `PLAN.md` states for Phase 0: every proof is an
inequality between `Int.fract` terms, closed by the `Int.fract` API plus
`linarith`.

**Start with `lem:countup`.** It is the one missing piece of §1's API and it is
a five-line mirror of `sum_code` (`Sturmian.lean:138`): telescope
`codeUp_eq_sub_ceil` over `Finset.range N` with `Finset.sum_range_sub`, then
evaluate at `0`. `ceil_step` (`:76`) and `codeUp_eq_sub_ceil` (`:111`) already
exist, so there is no new ceiling arithmetic. Doing it first gives a short win
and the exact shape `thm:step5` consumes.

```lean
theorem sum_codeUp (hα0 : 0 < α) (hα1 : α < 1) (hx0 : 0 ≤ x) (hx1 : x < 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, (codeUp α x k : ℤ) = ⌈(N : ℝ) * α + x⌉ - ⌈x⌉
```

Then, in order:

1. **`lem:dev`** — pure algebra once `|τ_a(w)| = a|w| + |w|₁` and
   `|τ_a(w)|₁ = |w|` are available. Note those two facts are about *words*, and
   §6.1 deliberately avoids constructing `τ_a` as a word. Decide early whether
   `Δ_α` takes a word or a pair `(length, weight)`. **Prefer the pair**: every
   use of `Δ_α` in §7 needs only `|u|` and `|u|₁`, so `Δ` can be
   `fun (n w : ℕ) => (w : ℝ) - α * n` and `lem:dev` becomes an identity between
   two such pairs. That keeps `τ_a` out of the development entirely, as in §6.1.
2. **`prop:bound`** — induction on `|u|`, descending levels. The three things
   that make it work are already in the paper and are listed above: `a ≥ 2`
   (so `|τ_a(u')| ≥ 2|u'|` and the induction descends), the gap inequality
   `aα < 1` from §4 as the only slack, and `q` a *proper* prefix of its block
   (so `t ≤ a−1`). The bound `< 1` is tight — `α(a+β) = 1` is an identity, not
   an estimate — so do not expect slack to absorb a sloppy case.
3. **`lem:slope`** — the contraction. `β ↦ 1/(a+β)` has `|derivative| ≤ 1/a² ≤ 1/4`
   for `a ≥ 2`, so `j` levels confine `α` to an interval of length `4^{-j}`;
   uniqueness follows. Irrationality is a descent on denominators
   (`α = p/q` ⟹ `β = q/p − a` has denominator `p < q`), and complementing does
   not change a denominator. `prop:derived` is what supplies a block parameter
   at every level — i.e. `isSturmian_deriveSeq`, now available.
4. **`thm:step5`** — `x = sup_N (S(N) − Nα)`. Needs `sSup` over a set of reals
   bounded by `prop:bound`, and the three-case split above. `sum_code` gives
   the `C` branch directly; `sum_codeUp` the other two.

**Two pieces of plumbing that are not in any step.** Neither appears in the §6
step list, and both are real work:

* **The letter exchange.** §7 opens by normalising so `11` is absent, and
  *every level below is normalised the same way*. `step_one` delivers `00`
  **or** `11` absent, so the complementation has to be threaded through the
  whole tower. The identity is in the proof of `cor:complexityup`: the
  complement of `C(β,y)` is `C⁺(1−β,−y)`. In Lean the ingredients are
  `codeUp_add_code_reflect` and the complement argument inside
  `ncard_factors_codeUp`.
* **The assembly.** `mechanical_of_isSturmian` exists only as a statement in
  `PLAN.md` Phase 9. Combining it with `isSturmian_code` and
  `isSturmian_codeUp` closes `thm:mh`, and that is the end of Phase 9.

## Decisions waiting on Robin

* **A corrupt blob in local history.** Commit `a74730f` contains a 97MB
  (2.5MB packed) corruption of `lean/PLAN.md`, from a Python `str.replace("", …)`
  — see `LESSONS.md`. The file was restored in `14fa7fe` and the working tree
  is correct. Nothing is pushed, so the blob can still be dropped cleanly;
  doing so is a history rewrite, which the global `CLAUDE.md` forbids by
  default, so it needs Robin's explicit say-so. Otherwise it ships.
* **The root `README.md` restates the Lean line and theorem counts** that
  `lean/README.md` also carries. They drifted three commits apart once already
  this session. Making the root file point at `lean/README.md` instead of
  restating would stop it recurring, but that is a change to how the docs are
  organised, not to what they say.

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
