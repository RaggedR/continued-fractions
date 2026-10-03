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

Nothing inside `all-the-proofs.tex`.  Two larger targets remain, each its own
project; both are described under **Not attempted** below.

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

## Not attempted

- **The converse of Morse–Hedlund** (§6, steps 2/4/5): complexity `m+1` ⟹
  balanced ⟹ mechanical. `all-the-proofs.tex` does not support it, but it is
  classical: transcribe from Lothaire, *Algebraic Combinatorics on Words*,
  ch. 2 (Berstel–Séébold).

  Checked October 2026: **no proof assistant has it.** The Isabelle AFP entry
  *Combinatorics on Words Basics* (Holub–Raška–Starosta, 2021) defines Sturmian
  words as lower mechanical words and proves elementary facts — that is our §1.
  No complexity function, no balancedness. Mathlib has nothing; nothing found
  for Rocq. So the first third of this is building a factor-set and
  bispecial-factor API that exists nowhere, which is why it gets no line
  estimate: the risk is infrastructure, not mathematics.


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
reverse Morse–Hedlund (§6)   — needs a factor-set API first
```
