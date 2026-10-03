# Sturmian.lean — plan

Target: formalise `../all-the-proofs.tex`. Files `Sturmian.lean` (the words)
and `Lagrange.lean` (§9, continued fractions), joined to `Palindrome.lean` by
`SqrtN.lean`. Same build as `Palindrome.lean`:

```bash
cd ~/git/experiments/waarnar/loop-experiment/lean
lake env lean ~/git/continued-fractions/lean/Sturmian.lean
```

The two files meet at one definition. `Palindrome.alpha n k = (P + √n)/Q` is the
`k`th complete quotient, so `Int.fract (alpha n k)` is the tail `αₖ` of §8 of
`all-the-proofs.tex`: `alpha n 0 = √n`, so `Int.fract (alpha n 0) = √n - a₀` is
the slope. Everything about `√n` is stated through that.

## Status

**All eight phases are complete, and so is Lagrange's 1770 half.**
`Sturmian.lean` 2057 lines, `Quadratic.lean` 544, `Lagrange.lean` 212,
`SqrtN.lean` 127, 0 errors, 0 warnings, 0 sorries, 51 theorems checked by
`#print axioms` across the five files.

`all-the-proofs.tex` is formalised apart from the **one** thing it still
declares unproved: the converse half of Morse–Hedlund (§10 item 1).

    derive_code       : derived   α x a = codeUp β (refl   α x 0)
    derive_codeUp     : derivedUp α x a = code   β (reflUp α x 0)
    tower_eq          : tower α a (j+1) = (if Even j then codeUp else code) (α (j+1)) (α (j+1))
    tower_period      : α L = α 0 → tower α a L = fun k => code (α 0) 0 (k+1)
    sqrt_tower_period : tower (sqrtTail n) (sqrtQuot n) (period n hn)
                          = fun k => code (sqrtTail n 0) 0 (k+1)
    complexity        : {w : Fin m → ℕ | ∃ k, w = factor α x m k}.ncard = m + 1
    ncard_factors_codeUp : (factors (codeUp α x) m).ncard = m + 1
    fib_sturmian_not_code
                      : IsSturmian (cons1 (code φ⁻¹ φ⁻¹)) ∧
                        ¬ ∃ α' x, 0 < α' ∧ α' < 1 ∧ 0 ≤ x ∧ x < 1 ∧
                          cons1 (code φ⁻¹ φ⁻¹) = code α' x
    fib_derive        : derived φ⁻¹ φ⁻¹ 1 = code φ⁻¹ φ⁻¹
    sigma_pre         : sigma (pre c m) = pre c (ones φ⁻¹ φ⁻¹ m)
    fib_limit         : sigma^[j] [1] = pre c (fibLen j)
    quadratic_of_eventually_periodic
                      : Irrational (α 0) → α (m+L) = α m → 1 ≤ L →
                        ∃ A B C : ℤ, A ≠ 0 ∧ A * α 0 ^ 2 + B * α 0 + C = 0
    exists_reduced    : Adm n s₀ → ∃ m, Reduced n ((step n)^[m] s₀).1 _
    eventually_periodic
                      : Adm n s₀ → ∃ m L, 0 < L ∧
                        ∀ k, m ≤ k → (step n)^[k+L] s₀ = (step n)^[k] s₀

`sqrt_tower_period` is one headline: for every non-square `n`, deriving `L`
times returns the sequence with its first letter removed.  `sturmian.tex`
observes it for `n = 2` and `n = 7`.

`fib_sturmian_not_code` is the other, and it is now self-contained: both halves
are proved in Lean.  Before Phase 2 the word *Sturmian* appeared in no
statement, so the refutation of `sturmian.tex` §2 took *it is Sturmian* from
the paper.  It no longer does.

`tower_eq` is stated for an abstract sequence of tails with
`(a j : ℝ) + α (j+1) = 1 / α j`, so it needs no import and is not about `√n`;
`SqrtN.lean` supplies the instance from `alpha_succ`, `floor_alpha`,
`state_period`, `period_pos` and `sqrt_irrational`.

## Building

```bash
lean/build.sh            # builds all four files, ~3 min, prints the axiom report
```

`lake env lean` refuses files outside its own root, so the script borrows the
Mathlib of an unrelated project on the same toolchain (`v4.30.0-rc2`) and drives
`lean` through `lake env sh`, putting our own `.olean`s on `LEAN_PATH`. Override
with `MATHLIB_PROJECT=...` if that project moves.

`Palindrome`, `Lagrange` and `Sturmian` are mutually independent; only
`SqrtN.lean` imports all three.

**A lakefile here is not worth it**, contrary to an earlier note in this file. It
would need its own Mathlib checkout — measured at **7.1GB** — which is a real
cost on a disk with ~36GB free, in exchange for build ergonomics the script
already provides. Revisit only if this development becomes a standalone package
that other projects import.

## Remaining

One target: the converse half of Morse–Hedlund.  `all-the-proofs.tex` §6 is
complete as of 3 October 2026 — steps 2 and 4 (`prop:blocks`, `prop:derived`)
and then step 5, which is §7 of that document (`lem:slope`, `prop:bound`,
`thm:step5`).  **No open mathematics remains.**  Of the formalisation, `lem:rs`
and `cor:onesp` are done; the rest is **Phase 9** below.

## Design

`Palindrome.lean` won by keeping everything over `ℤ` and letting `omega` work.
That is not available here: a coding is `⌊kα + x⌋` for a real `α`. The
replacement discipline is **every proof is an inequality between `Int.fract`
terms**, discharged by the `Int.fract` API plus `linarith`. No `ℝ`-valued
induction, no limits, except in Phase 1.

```lean
def code   (α x : ℝ) (k : ℕ) : ℕ := if 1 - α ≤ Int.fract (x + k*α) then 1 else 0
def codeUp (α x : ℝ) (k : ℕ) : ℕ :=
  if 1 - α < Int.fract (x + k*α) ∨ Int.fract (x + k*α) = 0 then 1 else 0
```

Phases 0, 3, 4 and 5 need no density, no limits and no cardinality argument.
Phase 2 needs density and a cardinality argument (in the event, no limits).
They were done in the order 0, 3, 4, 5, 6, 2 — the reverse of the order the
sections appear in, and the reverse of the note in memory. The √n headline
(Phase 5) lands without ever touching Phase 1.

## Phase 0 — codings (§1)

| Lemma | Lean |
|---|---|
| 1.1 | `code_eq_sub_floor : code α x k = ⌊(k+1)*α + x⌋ - ⌊k*α + x⌋` |
| 1.1 | `codeUp_eq_sub_ceil` |
| 1.3 | `code_eq_codeUp_of_fract_ne_zero : (∀ k, Int.fract (x + k*α) ≠ 0) → code α x = codeUp α x` |
| 1.4 | `sum_code : ∑ k ∈ range N, code α x k = ⌊N*α + x⌋` |
| 1.5 | `code_succ : code α x (k+1) = code α (Int.fract (x+α)) k` |

Small. `Int.fract_add_int`, `Int.floor_add_fract`, `Int.fract_eq_self`.
Confidence 95%.

## Phase 1 — density (§2)

```lean
theorem exists_fract_mem_Ico (hα : Irrational α) (x : ℝ) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε) (hcε : c + ε ≤ 1) :
    ∃ k : ℕ, 1 ≤ k ∧ c ≤ Int.fract (x + k*α) ∧ Int.fract (x + k*α) < c + ε
theorem exists_fract_mem_Ioo
theorem Icc_subset_closure_orbit (hα : Irrational α) (x : ℝ) :
    Set.Icc (0:ℝ) 1 ⊆ closure (Set.range fun k : ℕ => Int.fract (x + k*α))
```

`DenseRange (fun k : ℕ => Int.fract (x + k*α))` — the statement this plan
first gave — is false: the range lies in `[0,1)`, so it is not dense in `ℝ`.
The tex says dense *in* `[0,1)`; `Icc_subset_closure_orbit` is that, and the
interval forms are what §3 and §6 consume.

Mathlib has `AddCircle.denseRange_zsmul_iff`, but for `ℤ`-orbits on
`ℝ ⧸ ℤ`. Transferring it costs more than the direct proof, which is Dirichlet
by pigeonhole plus two **ladders**: the step count that lands in `[c, c+δ)` is
`⌈(c-y+1)/δ⌉₊` going up and `⌊(y+2-c)/δ⌋₊` coming down. Both are explicit
witnesses, so there is no induction and no wrap-around case analysis.
Irrationality is used exactly once, to make the step `δ` nonzero; Dirichlet
itself does not need it.

## Phase 3 — return time and blocks (§4)

`Theorem 4.1` is the keystone and is pure arithmetic:

```lean
theorem return_time (hα : 0 < α) (hα1 : α < 1) (hu : u ∈ Set.Ico (0:ℝ) 1) :
    IsLeast {t : ℕ | 1 ≤ t ∧ 1 - α ≤ Int.fract (x + t*α)}
            (if u < β then a₁ + 1 else a₁)
```

with `x = 1 - α + α*u`, `a₁ = ⌊1/α⌋`, `β = Int.fract (1/α)`. The proof in the
tex is three inequalities; in Lean it is the same three plus `Int.fract` unfolds.

Positions of the `1`s: use `Nat.nth (fun k => code α x k = 1)`. Infinitude comes
free from `return_time`, so the `Nat.nth` API for infinite predicates applies.
Then

```lean
def derive (α : ℝ) (ℓ : ℕ → ℕ) (i : ℕ) : ℕ := nth ℓ (i+1) - nth ℓ i - ⌊1/α⌋ + 1
```

Confidence 85%. Main risk is `Nat.nth` API friction, not mathematics.

## Phase 4 — the derivation theorem (§5)

```lean
theorem derive_code :
    derive α (code α x) = codeUp (Int.fract (1/α)) (Int.fract (-u₀))
theorem derive_codeUp :
    derive α (codeUp α x) = code (Int.fract (1/α)) (1 - u₀)
```

where `u₀ = (Int.fract (x + (nth _ 0)*α) - (1-α))/α`.

**The memory note says to state this existentially to dodge the shift
bookkeeping. That is now unnecessary** — §5 computes the intercept exactly, and
the exact form is what Phase 5 consumes. State it as an equality.

Proof: `u (i+1) = Int.fract (u i + 1 - β)` by `return_time`, then
`v i = Int.fract (-u i)` satisfies `v (i+1) = Int.fract (v i + β)` by induction,
then the letter rule is one `if_congr`. Confidence 80%, ~250 lines.

## Phase 5 — square roots (§8) — the headline

```lean
theorem derive_iterate (hn : ¬IsSquare n) (j : ℕ) (hj : 1 ≤ j) :
    derive^[j] (code (Int.fract (alpha n 0)) 0)
      = (if Odd j then codeUp else code) (Int.fract (alpha n j))
                                         (Int.fract (alpha n j))

theorem derive_period (hn : ¬IsSquare n) :
    derive^[period n hn] (code (Int.fract (alpha n 0)) 0)
      = fun k => code (Int.fract (alpha n 0)) 0 (k+1)
```

The induction step is the one-line computation `u₀ = 1 - β` of the tex, twice.
The corollary consumes `Palindrome.purely_periodic` and `Palindrome.alpha_succ`.
It needs `Int.fract (alpha n (j+1)) = Int.fract (1 / Int.fract (alpha n j))`,
which is `alpha_succ` modulo a `fract` rearrangement — **check this first**, it
is the joint between the two files and the only place the plan can fail early.

This is the new theorem: `sturmian.tex` observes the return-after-L for `n = 2`
and `n = 7`; here it holds for every non-square `n`. Confidence 75%.

## Phase 6 — the counterexample (§6)

```lean
def cons1 (ℓ : ℕ → ℕ) : ℕ → ℕ := fun k => if k = 0 then 1 else ℓ (k-1)

theorem codeUp_zero_eq (hα : Irrational α) (hα0 : 0 < α) (hα1 : α < 1) :
    codeUp α 0 = cons1 (code α α)

theorem not_code (hα : Irrational α) (hα0 : 0 < α) (hα1 : α < 1) :
    ¬ ∃ α' x : ℝ, 0 < α' ∧ α' < 1 ∧ 0 ≤ x ∧ x < 1 ∧ cons1 (code α α) = code α' x
```

`not_code_fib` is the instance at `α = (√5-1)/2` of `all-the-proofs.tex`
Theorem 6.1, a correction to `sturmian.tex` §2.

The slopes agree without a limit: `sum_code` on both sides gives
`⌊Nα' + x⌋ = 1 + ⌊Nα⌋`, hence `|N(α'-α)| < 2` for every `N`, hence `α' = α` by
Archimedes. Then `⌊fract(Nα) + x⌋ = 1` for every `N ≥ 1`, which Phase 1
contradicts.

## Phase 2 — complexity (§3) — **done**

```lean
theorem complexity (hα : Irrational α) (hα0 : 0 < α) (hα1 : α < 1) (x : ℝ) (m : ℕ) :
    {w : Fin m → ℕ | ∃ k : ℕ, w = factor α x m k}.ncard = m + 1
def IsSturmian (ℓ : ℕ → ℕ) : Prop := ∀ m : ℕ, 1 ≤ m → (factors ℓ m).ncard = m + 1
```

`x ∈ [0,1)` turned out not to be needed: the factor set depends on `x` only
through `Int.fract`, so the theorem holds for every real base point.

**The counting went a different way from the sketch above.**  The sketch said
to index the cells with `Finset.orderIsoOfFin`; that costs a `Fin m`-indexed
enumeration with dependent `r - 1` and `r` endpoints.  Instead there is one
definition doing three jobs:

```lean
noncomputable def cuts (α : ℝ) (m : ℕ) : Finset ℝ :=
  (Finset.Icc 1 m).image (fun j : ℕ => Int.fract (-((j : ℝ) * α)))
noncomputable def cell (α : ℝ) (m : ℕ) (t : ℝ) : ℕ :=
  ((cuts α m).filter (fun p => p ≤ t)).card
```

`cell` is the cell label; restricted to `cuts` it is *strictly monotone*, hence
injective, from an `m`-element set into `{1,…,m}`, hence a **bijection** onto
`{1,…,m}` (`exists_cut_cell`) — so "the cut point of rank `r`" is available
with no `Fin` and no sorting; and the cardinality itself is
`#{p ∈ cuts | cell p ≤ r} = #(Icc 1 r) = r`.  Irrationality enters in exactly
two places: `card_cuts` (the cut points are distinct) and density.

The cell bounds are carried abstractly as `c = 0 ∨ c ∈ cuts` and
`d = 1 ∨ d ∈ cuts`, which is just enough to get `0 ≤ c < d ≤ 1` in all four
corner cases without a case split on `r = 0` / `r = m` inside the main
argument.

Actual cost: ~230 lines for Theorem 3.1, confidence was 60% and the estimate
of ~400 lines was high.

### Corollary 3.2 — the upper coding

The tex proves it by rerunning §3 with `⌈·⌉` for `⌊·⌋`.  **That is
unnecessary**, and the Lean does not do it:

```lean
theorem codeUp_add_code_reflect (hα0 : 0 < α) (x : ℝ) (k : ℕ) :
    codeUp α x k + code (1 - α) (-x) k = 1
```

The upper coding of slope `α` is the *bitwise complement* of the lower coding
of slope `1 - α` at base `-x`.  `codeUp` is `1` exactly on the arc
`(1-α,1) ∪ {0}`, whose complement in `[0,1)` is `(0,1-α]`, and the reflection
`v ↦ 1 - v` carries that onto `[α,1) = [1-(1-α),1)` — the lower arc of slope
`1 - α`.  No index shift is needed, because
`Int.fract (-x + k(1-α)) = Int.fract (-(x + kα))`.

Complementation is a bijection on words, so Corollary 3.2 is 50 lines on top of
Theorem 3.1 rather than a parallel development on `(0,1]`.  Going the other way
would have been genuinely longer: the upper coding's natural base-point range
is `(0,1]`, not `[0,1)`, because `codeUp` reads `fract = 0` as the letter `1`.

This identity is **not** in `all-the-proofs.tex`; it is recorded there now as a
remark in §3.

## Phase 7 — the substitution (§7) — **done**

```lean
theorem fib_derive : derived invPhi invPhi 1 = code invPhi invPhi
theorem sigma_pre (m : ℕ) :
    sigma (pre (code invPhi invPhi) m) = pre (code invPhi invPhi) (ones invPhi invPhi m)
theorem fib_limit (j : ℕ) : sigma^[j] [1] = pre (code invPhi invPhi) (fibLen j)
```

Two things the sketch got wrong.

**`lem:blocks` was not already in Lean.** The sketch assumed Phase 3 had it; it
did not. It is cheap, though, because `ones_succ_le` ("nothing between
consecutive `1`s is a `1`") was already there:

```lean
theorem block_length : ones α x (i + 1) = ones α x i + (a + derived α x a i)
theorem block_zero (hj0 : 0 < j) (hj : ones α x i + j < ones α x (i + 1)) :
    code α x (ones α x i + j) = 0
```

Both live at the end of §4.2, where Lemma 4.3 belongs. ~25 lines.

**`σ(c) = c` and the limit are stated on prefixes.** `σ` of an infinite
sequence is not a function of position without first inverting the block-start
map, which is a bookkeeping swamp. The prefix form avoids it entirely and is
the standard rigorous reading: `sigma_pre` says `σ` applied to the first `m`
letters gives the first `ones m` letters, and `fib_limit` says `σʲ(1)` is the
prefix of `c` of length `fibLen j`, with `fibLen` strictly increasing
(`fibLen_lt_succ`) so the limit exists. The induction is three lines once
`sigma_append` and `pre_succ` are in place.

`fib_derive` is ~5 lines: it is `step_low` at the fixed point `β = α`, so the
only new computation is `1/α = 1 + α` (`invPhi_rec`). Which is why §7 sits
*after* §8 in the file — it consumes `step_low` and `isLeast_code_slope`.

## Phase 8 — Euler's half of Lagrange (§9) — **done**

In its own file, `Lagrange.lean` (212 lines), because §9 is about continued
fractions and not about words: it mentions no coding, and is stated for an
abstract tail sequence with `(a j : ℝ) + α (j+1) = 1 / α j` — the convention of
`tower_eq` and `sqrtTail_rec`, *not* the `a_{j+1}` of the tex. It imports only
Mathlib.

```lean
def N (b : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, (b : ℤ)]
def cfWord (a : ℕ → ℕ) (m : ℕ) : ℕ → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => 1
  | L + 1 => cfWord a m L * N (a (m + L))

theorem cfWord_apply :
    α m * ((cfWord a m L 1 0 : ℝ) * α (m + L) + (cfWord a m L 1 1 : ℝ))
      = (cfWord a m L 0 0 : ℝ) * α (m + L) + (cfWord a m L 0 1 : ℝ)
theorem quadratic_of_periodic (hper : α (m + L) = α m) (hL : 1 ≤ L) :
    ∃ r s t : ℤ, 0 < r ∧ (r : ℝ) * α m ^ 2 + s * α m + t = 0
theorem quadratic_of_eventually_periodic (h0 : Irrational (α 0)) … :
    ∃ A B C : ℤ, A ≠ 0 ∧ (A : ℝ) * α 0 ^ 2 + B * α 0 + C = 0
```

Three things worth recording.

**The Möbius action is stated multiplicatively**, so no denominator ever has to
be shown nonzero, and the induction step is a single `linear_combination`
against `α (m+L) * (a (m+L) + α (m+L+1)) = 1`.

**`0 < r`, not just `(r, s-p, q) ≠ 0`.** The tex claims only the triple is
nonzero, which leaves open that the relation is linear. Positivity of the
leading coefficient falls out of the product's shape,
`!![p,q;r,s] * !![0,1;1,b] = !![q, p+q*b; s, r+s*b]` — the new bottom-left entry
is the old bottom-right one, so once the bottom row is positive it stays
positive (`cfWord_entries`).

**The transport to `α 0` needs no discriminant.** Substituting
`α m = (Q - S·α 0)/(R·α 0 - P)` gives leading coefficient `r*S² - s*S*R + t*R²`,
which is the form `(r,s,t)` evaluated at the *rational* point `-S/R`; it cannot
vanish because the form's roots are `α m` and its conjugate, neither rational.
`irrational_tail` supplies the irrationality, propagating it down from `α 0`.

Since the file is abstract it needs a witness, or the theorem could be vacuous.
`Sturmian.sqrt_quadratic` in `SqrtN.lean` is it: the same `sqrtTail`/`sqrtQuot`
pair that instantiates `tower_period` also instantiates this. A concrete check
in `Lagrange.lean` confirms that `[1;1,1,…]` yields `(r,s,t) = (1,1,-1)`, i.e.
`x² + x - 1 = 0`, the equation of `1/φ` from §7.

## Lagrange 1770 (§9, the other half) — **done**

`Quadratic.lean` (544 lines).  The remaining target from the original memory
note, and it came in well under the 400–700 line estimate, for two reasons.

**Almost nothing in `Palindrome.lean` was specific to `√n`.** `quo`, `step`,
`unstep`, `Reduced`, `finite_reduced`, `step_mapsTo`, `step_injOn` are all
statements about the *discriminant* `n` and an arbitrary state; only
`state n k = (step n)^[k] (0,1)` fixes the start.  So the general case is an
extension, not a rewrite, and §2 of `Quadratic.lean` gets pure periodicity on
the reduced set by citing `Palindrome` directly.

**One thing did have to change.** `Palindrome.quo n P Q = (a₀ + P)/Q` is
`⌊(P+√n)/Q⌋` only for `Q > 0`, which for `√n` is automatic (`Q_pos_all`).  For a
general quadratic irrational the `Q`s must change sign, so

```lean
def quo (n : ℕ) (P Q : ℤ) : ℤ :=
  if 0 < Q then Palindrome.quo n P Q else -(Palindrome.quo n P (-Q)) - 1
```

with `floor_surd` proving it is the floor either way.  The negative branch is
`⌊-x⌋ = -⌊x⌋ - 1`, legitimate because a surd is never an integer.

### The preperiod, without convergents

`exists_reduced` is the only new mathematics, and the textbook route — the
convergents `pₖ/qₖ`, the bound `|α - pₖ/qₖ| < 1/qₖ²`, then either the invariant
discriminant of `Aₖx² + Bₖx + Cₖ` or uniqueness of the CF expansion — is
**avoidable**.  Mathlib does have what that route needs
(`GenContFract.of_convergence`, `abs_sub_convs_le`, `ContinuantsRecurrence`,
`Determinant`), but it would also need the `stream_fst` bridge generalised.
None of it is used.  Instead:

* `α̅ₖ < 0` forces `α̅ₖ₊₁ ∈ (-1,0)`, which *is* reduced.  So if the orbit is
  never reduced then `α̅ₖ > 0` for every `k ≥ 1`.
* Positivity of `α̅ₖ₊₁ = 1/(α̅ₖ - aₖ)` forces `α̅ₖ > aₖ ≥ 1`, so `αₖ` *and* `α̅ₖ`
  exceed 1 from index 1 on.
* `αₖ₊₁ - α̅ₖ₊₁ = (α̅ₖ - αₖ)·αₖ₊₁α̅ₖ₊₁` identically, so the gap
  `|αₖ - α̅ₖ| = 2√n/|Qₖ|` strictly *increases*.
* Hence `|Qₖ|` is a strictly decreasing sequence of positive integers.
  Infinite descent.

This matches the source.  `αₖ·α̅ₖ = -Qₖ₋₁/Qₖ`, so `α̅ₖ < 0` says `Qₖ₋₁` and `Qₖ`
have the same sign — which is Lagrange's own criterion, *Additions* art. 41
("deux consécutifs de même signe").  The design was arrived at independently and
then found to be his; `papers/README.md` indexes the article.

The paper now carries this proof too, as `all-the-proofs.tex`
Theorem `thm:lagrange1770`, so §10's unproved list is down to one item.

### Instances

The theorem is stated for an abstract admissible state, so it needs witnesses.
`eventually_periodic_sqrt` checks that starting at `(0,1)` reproduces
`Palindrome.state` exactly (a consistency check — `purely_periodic` is sharper,
with preperiod 1), and `eventually_periodic_golden` is the case
`Palindrome.lean` cannot reach: `φ = (1+√5)/2`, where `Q = 2 ∣ 5 - 1²`.

## Phase 9 — the converse of Morse–Hedlund (§6)

The only thing left in `all-the-proofs.tex`.

```lean
theorem mechanical_of_isSturmian (ℓ : ℕ → ℕ) (hb : ∀ k, ℓ k ≤ 1)
    (hap : ¬ ∃ p, 0 < p ∧ ∀ k, ℓ (k + p) = ℓ k) (hS : IsSturmian ℓ) :
    ∃ α x : ℝ, Irrational α ∧ 0 < α ∧ α < 1 ∧ 0 ≤ x ∧ x < 1 ∧
      (ℓ = code α x ∨ ℓ = codeUp α x)
```

With `isSturmian_code` and `isSturmian_codeUp` that closes `thm:mh`; with
`fib_sturmian_not_code` it says precisely why the `sturmian.tex` §2 form was
wrong — both codings are needed and neither alone suffices.

### Sources

`papers/sturmian/README.md` has the full accounting.  In short: the original is
Morse–Hedlund, *Symbolic Dynamics II. Sturmian Trajectories*, Amer. J. Math.
**62** (1940) 1–42, paywalled and in copyright until 2035; the proof is in
Lothaire, *Algebraic Combinatorics on Words* (CUP 2002) ch. 2, by Berstel and
Séébold, which is **not** freely available — Berstel's Lothaire page posts only
contents, solutions and errata for that volume.  Three openly-offered PDFs sit
in `papers/sturmian/`: they give the statement, confirm our definitions are
verbatim the standard ones, and carry the *finite* theory in full, but all three
defer the infinite step to Lothaire ch. 2.

One oblique glimpse of the real proof *is* available, from the book's errata.
The Sturmian corrections sit on pp. 56–61, and the correction to Proposition
2.1.18 quotes its proof: *"We may suppose that β < α.  For any factor u of s
such that (α−β) ≥ 2/|u|, one has π(u)−α > −1/|u| by Proposition 2.1.10 …"*.
So `π(u)` is the frequency of `1`s in a factor, **Proposition 2.1.10 is a
quantitative bound `|π(u)·|u| − α·|u|| < 1`**, and 2.1.18 uses it to show two
candidate slopes coincide.  That bound is exactly the converse of our `sum_code`
(`∑_{k<N} code α x k = ⌊Nα + x⌋`), and it is step 5's machinery — it is our
`prop:bound`.  The agreement is a check on the statement only: §7 proves it in
half a page from `lem:blocks`, by induction on word length.  Do **not** route it
through `Sturmian ⟹ balanced`; that is the direction the literature defers to
Lothaire ch. 2, and the derivation gives the bound directly.

So the decomposition below is `all-the-proofs.tex` §6's own, **not** transcribed
from a proof anyone on this project has read.  Flagged, because the one time
this plan guessed at a decomposition it was wrong: Phase 7's sketch assumed
`lem:blocks` was already formalised, and it was not.

### The route is already chosen, and it is not Lothaire's

§6 says the route that fits this document is to **run §4 and §5 backwards**.
That matters.  The standard treatment builds a factor-set and bispecial-factor
API from scratch; §§4, 5 and 7 are already formalised here.  Berstel's
standard-sequence recurrence `sₙ = sₙ₋₁^{dₙ} sₙ₋₂`, with `[0; 1+d₁, d₂, …]` the
continued fraction of the slope, is the *inverse of our derivation tower*.  So
Phase 9 ought to be an inversion of `derived`/`tower`, not a new development.

Status of §6's five steps.  **All five were proved by 3 October 2026**; step 5 is
§7 of `all-the-proofs.tex`.  Step 2 was the step this plan called the real
infrastructure, and it was not.

| step | content | tex | Lean |
|---|---|---|---|
| 1 | `F(1)=2`, `F(2)=3`, so exactly one of `00`/`11` is absent | proved | not started |
| `lem:rs` | `F(m+1) − F(m)` counts right-special factors of length `m` | proved | **`ncard_factors_succ`** |
| `cor:onesp` | `F(m) = m+1` ⟺ one right-special factor per length | proved | **`isSturmian_iff_ncard_rightSpecial`** |
| 2 | block lengths take two consecutive values `a-1`, `a` | **proved** — `prop:blocks` | not started |
| 3 | `ℓ = 0^{k₀} τ_a(ℓ')` | proved | `block_length`, `block_zero`, but see below |
| 4a | `F_{ℓ'}(m) = m+1`: the derived sequence is again Sturmian | **proved** — `prop:derived` | not started |
| 4b | both letters of `ℓ'` occur | absorbed into 4a (`m = 1`) | — |
| 5 | the limit pins a single `α = [0;a₁,a₂,…]` and a single `x` | **proved** — §7 | not started |

**Step 3 is less reusable than it looks.** `block_length` and `block_zero` are
stated for `code α x` — they presuppose a coding, which is exactly what Phase 9
is trying to produce.  They must be restated for an abstract `ℓ` whose block
lengths take two consecutive values, i.e. downstream of step 2.  Cheap, but it
is work; §6's "applies verbatim" is about the mathematics, not the Lean.

### Where the cost is

**Step 2 is proved, and it is not the palindrome argument.**  It is now
`all-the-proofs.tex` Proposition `prop:blocks`, about half a page, and the only
tool is

```
F(m+1) − F(m) = #{right-special factors of length m}            (lem:rs)
```

— so complexity `m+1` is *equivalent* to having exactly one right-special factor
of each length (`cor:onesp`).  Then `0^{j+1}` and `1·0^j` have the same length
and differ in their first letter, so at most one is right-special; `0^{j+1}` is
right-special iff `j ≤ a−2`, and `1·0^j` iff `j` is a block length and some
block is longer.  Uniqueness forces every non-maximal block length to be
`≥ a−1`.  The over-long-initial-block case falls to the same inequality.

That changes the Lean cost of this phase substantially.  **What is needed is a
right-special-factor API, not a bispecial one** — and `lem:rs` is a statement
about a surjection with fibres of size 1 or 2 between `factors ℓ (m+1)` and
`factors ℓ m`, which the `factors`/`ncard` machinery from Phase 2 already
supports.  The claim in *Prior art* below that no proof assistant has the needed
API still stands, but the API is now much smaller than it looked.

Verified numerically before writing: the right-special count is 1 at every
length for three codings; block lengths `{1,3}` give the two right-special
factors `00`, `10` at length 2 and `{2,4}` give `000`, `100` at length 3 — the
predicted witnesses; and prefixing an over-long `0`-block to a genuine Sturmian
tail breaks the count at exactly the predicted length.

**Step 5 needed no convergence argument and no Ostrowski theory.**  The
prediction that Mathlib's continued-fraction API would finally be needed was
wrong: §7 uses none of it.  `lem:slope` gets `α` from the fact that
`β ↦ 1/(a+β)` has derivative at most `1/a² ≤ 1/4` when `a ≥ 2`, so the levels
confine `α` to intervals of length `4^{-j}`; irrationality is a descent on
denominators.  `prop:bound` is an induction on word length.  Everything is
elementary and finite — `Finset`, `Nat`, and one geometric series.

**Step 4a** may fall out of the tower for free, since `derive_code` and
`derive_codeUp` already say what deriving a coding gives.

### Order, and where it can still fail

```
lem:rs, cor:onesp  ──►  2  ──►  3'  ──►  1  ──►  4  ──►  5
```

All five steps are proved; all of this is now formalisation.  `lem:rs` and
`cor:onesp` were formalised on 3 October 2026 as `ncard_factors_succ` and
`isSturmian_iff_ncard_rightSpecial`, next to `IsSturmian` in `Sturmian.lean`;
they make step 2 mechanical.  Next is step 2, then `3'` (step 3 restated for an
abstract `ℓ`, see above), then step 1, then step 4 — which needs `lem:rschain`
and `lem:aper` as well as `lem:bridge`, all three proved in the paper and all
three small.

### What `lem:rs` cost, and what it bought

43 lines.  Three things are worth knowing before building on it.

* **`rightSpecial ℓ m` is `extBy ℓ m 0 ∩ extBy ℓ m 1`**, where `extBy ℓ m b` is
  the set of length-`m` words whose extension by `b` is a factor.  The count
  then falls out of `Set.ncard_union_add_ncard_inter` with `extBy_union`
  (`extBy ℓ m 0 ∪ extBy ℓ m 1 = factors ℓ m`, i.e. every factor extends) — no
  fibrewise sum, no `Finset` transfer.
* **Right-special is a conjunction, not a cardinality.** Over `{0,1}` the two
  agree, and the conjunction is far cheaper to case-split on in step 2.  Every
  statement therefore carries `hb : ∀ k, ℓ k ≤ 1` rather than deriving
  binarity.
* **`Fin.snoc` is dependent, and this bites twice.** `fun u => Fin.snoc u b`
  will not elaborate without the ascription `(… : Fin (m+1) → ℕ)`, and
  `rw [← h]` for `h : w (Fin.last m) = 1` abstracts the `1` in `m + 1` and
  fails on the motive.  Rewrite forwards into `Fin.snoc_init_self` instead.
  A `show … ∈ _` is not enough either — the underscore leaves the motive open,
  so the ascription has to be written out.

### Step 2 — what is formalised, and what it still needs

In `Sturmian.lean` §6.1, all clean:

| | |
|---|---|
| `EventuallyPeriodic` | a preperiod `q` and a period `p` |
| `exists_bound_of_eventuallyPeriodic` | **`lem:evper`** — bounded complexity |
| `not_eventuallyPeriodic` | Sturmian ⟹ not eventually periodic |
| `exists_one_ge` | infinitely many `1`s, the proof's first line |
| `zeros`, `oneZeros`, `zerosOne`, `oneZerosOne` | `0^m`, `1 0^j`, `0^m 1`, `1 0^j 1` |
| `mem_factors_iff` and four word forms | membership as occurrence at a position |
| `rightSpecial_zeros_iff`, `rightSpecial_oneZeros_iff` | right-specialness as two named words |
| `not_both_rightSpecial` | **the engine** — `0^{j+1}` and `1 0^j` cannot both be right-special |

`prop:blocks` itself is not formalised.  What it needs next, in order:

1. ~~Subword closure of `factors`.~~ **Done, and not as a subword lemma.**
   Every remaining step is of the form *`1 0^s 1` is a factor and `s ≥ j+2`, so
   `1 0^{j+1}` and `0^{j+2}` and `0^{j+1} 1` are factors.*  A generic subword
   lemma would state each of those as a cast-laden `Fin` reindexing.  Instead
   `mem_factors_iff` turns membership into *occurrence at a position*, and the
   four words get `mem_factors_zeros_iff`, `mem_factors_oneZeros_iff`,
   `mem_factors_zerosOne_iff`, `mem_factors_oneZerosOne_iff`.  Each deduction
   is then a witness shift and `omega` closes it — no reindexing, no casts.
2. `blockLens ℓ = {j | oneZerosOne j ∈ factors ℓ (j+2)}`, the set `S`;
   nonempty from `exists_one_ge` and a `Nat.find` for the next `1`;
   `1 ≤ j` for `j ∈ S` from `11` absent.
3. `S` bounded, from (1) and `not_both_rightSpecial`.  Then `a = max S`, and
   `0^j` is a factor exactly for `j ≤ a`.
4. The display `j ∈ S, j < max S ⟹ j ≥ a-1`, again from (1) and the engine.
5. `max S = a` and `S = {a-1, a}`.  This is the one place needing something
   new: **a single block length makes `ℓ` eventually periodic**, which then
   meets `not_eventuallyPeriodic`.  Expect the sequence to be shown equal to
   `(1 0^j)^∞` past its initial block.

**Nothing here is open mathematics any more.**  Step 5 is `all-the-proofs.tex`
§7, proved 3 October 2026 and checked over ≈3·10⁶ factors in exact arithmetic.
No new Mathlib surface is wanted: the survey that expected
`GenContFract.of_convergence` and a generalised `Palindrome.stream_fst` was
wrong on both counts.

**A line estimate for the whole phase can now be written**, and the reason it
could not has gone: every step has a paper proof.  The three new objects are
`Δ_α(u) = |u|₁ − α|u|` on `List Bool`, the decomposition
`u = 0^s τ_a(u') q` with `q` a proper block prefix, and the nested intervals of
`lem:slope`.  The decomposition is the one piece with real bookkeeping.

## Prior art: what proof assistants already have

Checked October 2026, and the answer for Phase 9 is **nothing**.

The Isabelle AFP entry *Combinatorics on Words Basics* (Holub–Raška–Starosta,
2021) defines Sturmian words as lower mechanical words and proves elementary
facts — that is our §1, already done here.  It has no complexity function and no
balancedness.  Mathlib has neither, nor a factor-set or bispecial-factor API.
Nothing found for Rocq.

So Phase 9 means building a factor-set and right-special-factor API from
scratch.  That is the argument for doing the phase at all: the statement is
classical, but the infrastructure would be the first of its kind, and Berstel's
definitions being verbatim ours (see `papers/sturmian/README.md`) means it would
be recognisable to anyone else working in the area.  Note that after 3 October
the API needed is *right*-special, not bispecial — the palindrome machinery the
classical route wants is not on the critical path.


## Order of work

Done:

```
0 ──► 3 ──► 4 ──► 5        (no density, no cardinals, ends at the headline)
                   └► 6    (needs 1)
      1 ──► 2              (density; 2 closes the §6 refutation)
                   └► 7    (needs step_low from 8)
8                          (Lagrange.lean, independent of everything else)
```

Done since:

```
9 (Lagrange 1770)            (Quadratic.lean, extends Palindrome.lean)
```

Next, and now the only thing left:

```
9 (converse Morse–Hedlund)   4a ──► 2 ──► 3' ──► 1, 4b ──► 5
```
