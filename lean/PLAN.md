# Sturmian.lean — plan

Target: formalise `../all-the-proofs.tex`. New file `Sturmian.lean`, same build
as `Palindrome.lean`:

```bash
cd ~/git/experiments/waarnar/loop-experiment/lean
lake env lean ~/git/continued-fractions/lean/Sturmian.lean
```

The two files meet at one definition. `Palindrome.alpha n k = (P + √n)/Q` is the
`k`th complete quotient, so `Int.fract (alpha n k)` is the tail `αₖ` of §8 of
`all-the-proofs.tex`: `alpha n 0 = √n`, so `Int.fract (alpha n 0) = √n - a₀` is
the slope. Everything about `√n` is stated through that.

## Status

Phases 0, 1, 3, 4, 5 and 6 are complete.  `Sturmian.lean` 1419 lines,
`SqrtN.lean` 95 lines, 0 errors, 0 warnings, 0 sorries, 21 theorems checked by
`#print axioms`.

    derive_code       : derived   α x a = codeUp β (refl   α x 0)
    derive_codeUp     : derivedUp α x a = code   β (reflUp α x 0)
    tower_eq          : tower α a (j+1) = (if Even j then codeUp else code) (α (j+1)) (α (j+1))
    tower_period      : α L = α 0 → tower α a L = fun k => code (α 0) 0 (k+1)
    sqrt_tower_period : tower (sqrtTail n) (sqrtQuot n) (period n hn)
                          = fun k => code (sqrtTail n 0) 0 (k+1)
    not_code_fib      : ¬ ∃ α' x, 0 < α' ∧ α' < 1 ∧ 0 ≤ x ∧ x < 1 ∧
                          cons1 (code φ⁻¹ φ⁻¹) = code α' x

The last is the headline: for every non-square `n`, deriving `L` times returns
the sequence with its first letter removed.  `sturmian.tex` observes it for
`n = 2` and `n = 7`.

`tower_eq` is stated for an abstract sequence of tails with
`(a j : ℝ) + α (j+1) = 1 / α j`, so it needs no import and is not about `√n`;
`SqrtN.lean` supplies the instance from `alpha_succ`, `floor_alpha`,
`state_period`, `period_pos` and `sqrt_irrational`.

## Building

`lake env lean` refuses files outside its root, so compile through `lake env sh`
and put the `.olean`s on `LEAN_PATH`:

```bash
W=~/git/experiments/waarnar/loop-experiment/lean
OUT=/tmp/cf-oleans && mkdir -p $OUT
cd $W && lake env sh -c "cd ~/git/continued-fractions/lean && lean -o $OUT/Palindrome.olean Palindrome.lean"
cd $W && lake env sh -c "cd ~/git/continued-fractions/lean && lean -o $OUT/Sturmian.olean   Sturmian.lean"
cd $W && lake env sh -c "cd ~/git/continued-fractions/lean && LEAN_PATH=\$LEAN_PATH:$OUT lean SqrtN.lean"
```

A lakefile for `lean/` would replace all three lines and is worth doing if the
development grows further.

## Remaining

Phase 2 (complexity), Phase 7 (the substitution), Phase 8 (Euler's half of
Lagrange). Two larger targets are out of scope below.

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
Phase 2 needs all three. **Do them in the order 0, 3, 4, 5, then 6, then 2** —
the reverse of the order the sections appear in, and the reverse of the note in
memory. The √n headline (Phase 5) lands without ever touching Phase 1.

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

## Phase 2 — complexity (§3)

```lean
theorem complexity (hα : Irrational α) (hx : x ∈ Set.Ico (0:ℝ) 1) (m : ℕ) :
    {w | ∃ k, w = fun j : Fin (m+1) => code α x (k+j)}.ncard = m + 2
```

Three parts:
1. `⌊t + j*α⌋ = ⌊j*α⌋ + if Int.fract (-j*α) ≤ t then 1 else 0` — easy.
2. The word determines, and is determined by, the cell of `[0,1)` cut by the `m`
   points `Int.fract (-j*α)`, `1 ≤ j ≤ m`. Index the cells with
   `Finset.orderIsoOfFin` on the `Finset` of cut points; distinctness is
   irrationality.
3. Every cell is hit — Phase 1.

The counting in part 2 is the cost, not the mathematics. ~400 lines, confidence
60%. The only phase that can swallow a week, and now the next one.

**It is load-bearing.** No Lean theorem so far contains the word Sturmian;
`Sturmian` is a namespace and `F(m) = m+1` appears in no statement. Until this
phase lands, `not_code_fib` proves that the prefixed Fibonacci sequence is not
a lower coding, and takes *it is Sturmian* from the paper — so the refutation
of `sturmian.tex` §2 is only half checked.

## Phase 7 — the substitution (§7)

```lean
theorem fib_derive  : derived φ⁻¹ φ⁻¹ 1 = code φ⁻¹ φ⁻¹          -- c' = c
theorem fib_subst   : σ (code φ⁻¹ φ⁻¹) = code φ⁻¹ φ⁻¹           -- σ(c) = c
theorem fib_limit   : code φ⁻¹ φ⁻¹ = lim_j σ^[j] [1]
```

with `σ 1 = [1,0]`, `σ 0 = [1]`, which is `τ_{a₁}` at `a₁ = 1`.

This is the opening of `sturmian.tex` §1 and it had no phase. `derive_code`
already gives `c' = c` once `u₀ = 1 - α` is computed, the same one-line
computation Phase 5 does twice; `{-u₀} = α` and `Cp(α,α) = C(α,α)` by
`code_eq_codeUp`.

The third line is the only new work: `σʲ(1)` is a prefix of `σʲ⁺¹(1)`, so the
limit exists. A `List`-valued iterate plus a prefix-stability induction;
no analysis. ~150 lines, confidence 80%.

## Phase 8 — Euler's half of Lagrange (§9)

```lean
theorem quadratic_of_periodic (hper : α m = α (m + L)) (hL : 0 < L) :
    ∃ r s t : ℤ, (r, s, t) ≠ 0 ∧ r * α m ^ 2 + s * α m + t = 0
```

Eventually periodic ⟹ quadratic irrational. Composing `L` Möbius maps
`α j = 1/(a (j+1) + α (j+1))` gives `α m = (p α m + q)/(r α m + s)`, hence
`r α m ² + (s - p) α m - q = 0`.

Euler, 1737. `Palindrome.lean` already has `M`, `initWord`, `periodWord` and
`det_periodWord`, so the composite is a matrix product and the coefficients are
its entries. ~200 lines, confidence 80%.

Phases 2, 7 and 8 together finish `all-the-proofs.tex` apart from the two
things that document itself declares unproved. That is the natural stopping
point: the paper and the Lean then say the same thing.

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

- **Lagrange for a general quadratic irrational** (§9, the 1770 half). The
  other open target in memory. `Reduced`, `step`/`unstep`, `finite_reduced` and
  `exists_iterate_eq_self` in `Palindrome.lean` are Lagrange's argument at
  `D = n, Q = 1`; they generalise to `(P + √D)/Q` with `Q ∣ D - P²`. The new
  work is the preperiod, since pure periodicity is what is lost.
  400–700 lines.

## Order of work

Done:

```
0 ──► 3 ──► 4 ──► 5        (no density, no cardinals, ends at the headline)
                   └► 6    (needs 1)
      1                    (density, used by 2 and 6)
```

Next, in order:

```
2 ──► 7 ──► 8              (finishes all-the-proofs.tex)
```

Then, each its own project and independent of the other:

```
Lagrange general (§9, 1770)
reverse Morse–Hedlund (§6)   — needs a factor-set API first
```
