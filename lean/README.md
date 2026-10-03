# Legendre's palindrome theorem in Lean 4

`Palindrome.lean` — a complete formalisation of `../palindrome.tex`.
**954 lines, 0 errors, 0 warnings, 0 sorries.**

## The theorems

```lean
theorem purely_periodic (n : ℕ) (hn : ¬IsSquare n) :
    ∃ L, 0 < L ∧ ∀ k, 1 ≤ k → state n (k + L) = state n k

theorem palindrome (n : ℕ) (hn : ¬IsSquare n) {i : ℕ}
    (h₁ : 1 ≤ i) (h₂ : i < period n hn) :
    a n i = a n (period n hn - i)

theorem a_period (n : ℕ) (hn : ¬IsSquare n) : a n (period n hn) = 2 * a0 n

theorem stream_fst (n : ℕ) (hn : ¬IsSquare n) (k : ℕ) :
    GenContFract.IntFractPair.stream (Real.sqrt n) k
      = some ⟨a n k, Int.fract (alpha n k)⟩
```

The last one is the bridge: with it, the first three are statements about
Mathlib's continued fraction of `√n`, not about a private definition.

Matrix side (`§4`):

```lean
theorem M_eq_T_mul_J (a : ℤ) : M a = !![1, a; 0, 1] * J        -- T is the alphabet
theorem T_isParabolic : (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ).IsParabolic
theorem symm_initWord : (initWord n hn)ᵀ = initWord n hn       -- the palindrome, as a matrix
theorem det_periodWord : (periodWord n hn).det = (-1) ^ period n hn
theorem trace_periodWord : (periodWord n hn).trace = 2 * (M (a0 n) * initWord n hn) 0 0
theorem isHyperbolic_periodWord : (periodWord n hn).IsHyperbolic
```

## Verification

`#print axioms` at the end of the file, re-checked on every build:

```
'Palindrome.purely_periodic'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Palindrome.palindrome'             depends on axioms: [propext, Classical.choice, Quot.sound]
'Palindrome.a_period'               depends on axioms: [propext, Classical.choice, Quot.sound]
'Palindrome.Q_eq_one_iff'           depends on axioms: [propext, Classical.choice, Quot.sound]
'Palindrome.symm_initWord'          depends on axioms: [propext, Classical.choice, Quot.sound]
'Palindrome.det_periodWord'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Palindrome.trace_periodWord'       depends on axioms: [propext, Classical.choice, Quot.sound]
'Palindrome.isHyperbolic_periodWord' depends on axioms: [propext, Classical.choice, Quot.sound]
'Palindrome.T_isParabolic'          depends on axioms: [propext, Classical.choice, Quot.sound]
'Palindrome.stream_eq'              depends on axioms: [propext, Classical.choice, Quot.sound]
'Palindrome.stream_fst'             depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`. Four `#guard`s also check that the definitions compute the
partial quotients in `period.py` (√7, √13, √46) — so the recurrence is the PQa
recurrence, not a plausible near-miss.

## Three things that made it cheap

**1. Galois' theorem is not needed.** The first draft had a monolithic sorry
called `galois` (reduced *iff* purely periodic), estimated at 400–700 lines.
Pure periodicity of *one orbit* needs only: the orbit lies in a finite set, the
set is forward-invariant, and the map is injective on it. Pigeonhole gives
eventual periodicity; injectivity removes the tail of the rho. That argument is

```lean
theorem exists_iterate_eq_self {α : Type*} {S : Set α} (hS : S.Finite)
    {f : α → α} (hmap : Set.MapsTo f S S) (hinj : Set.InjOn f S)
    {x : α} (hx : x ∈ S) : ∃ L, 0 < L ∧ f^[L] x = x
```

~15 lines, no number theory. Belongs in `Mathlib.Dynamics`; worth upstreaming.

**2. Injectivity is a computation.** `unstep` inverts `step` explicitly — and it
is `step` with `P` and `P'` exchanged. So the invertibility of the algorithm and
the palindrome are the *same symmetry*, which is why the classical proof uses a
transpose. `unstep_step` then does triple duty: injectivity, `state_period`
(`state L = (a₀, 1)`), and via `quo_step_fst` the palindrome itself.

**3. `Reduced` is linear.** Stating reducedness as what it is, rather than as
Lemma 2's squared conclusions, makes it linear. Since `√n` is irrational,
`m < √n ↔ m ≤ a₀` and `√n < m ↔ a₀ < m` for every integer `m`:

| on `α` | | here |
| --- | --- | --- |
| `α̅ < 0`  | `P < √n`     | `P ≤ a₀` |
| `α̅ > -1` | `√n < P + Q` | `a₀ < P + Q` |
| `α > 1`  | `Q - P < √n` | `Q - P ≤ a₀` |

Lemma 2's bounds `0 < P < √n`, `0 < Q < 2√n` then follow by `omega`; on paper
they need a case analysis on the sign of `P`. The `a₀² < n < (a₀+1)²` sandwich
is used in exactly two places, both in `step_mapsTo`, and both are contradiction
arguments of the same shape — precisely where the conjugate bound `-1 < α̅ < 0`
lives.

## Design

All content is a statement about **integer sequences**. `ℝ` appears only in §5,
in the bridge. The reason: the hard content is finite combinatorics over `ℤ`,
where `omega`, `nlinarith` and `decide` work; routing through Mathlib's
real-number stream would mean fighting `⌊·⌋` of an irrational at every step.

## Correction to `palindrome.tex`

§2 stated `n - P_{i+1}² = (n - P_i²) + Q_i(2P_i - a_iQ_i)`. The factor `a_i` is
missing; the correct identity is `+ Q_i·a_i(2P_i - a_iQ_i)`. The printed version
fails for 14,725 states with `n < 2000`. The conclusion survives — `Q_i` divides
either form — so the theorem was unaffected. Fixed in the tex; recorded here as
`sub_P_succ_sq`.

## What Mathlib already provided

| | |
|---|---|
| `Matrix.discr`, `IsParabolic`/`IsHyperbolic`/`IsElliptic` + conjugation invariance | `LinearAlgebra/Matrix/GeneralLinearGroup/FinTwo.lean` |
| `ModularGroup.T` = `!![1,1;0,1]`, `ModularGroup.S` | `LinearAlgebra/Matrix/SpecialLinearGroup.lean` |
| `irrational_sqrt_natCast_iff` | `NumberTheory/Real/Irrational.lean` |
| `IntFractPair.stream`, `stream_zero`, `stream_succ_of_some` | `Algebra/ContinuedFractions/Computation/{Basic,Translations}.lean` |
| `Matrix.transpose_list_prod`, `Set.Finite.injOn_iff_bijOn_of_mapsTo` | — |

**Nothing** on periodicity: no Lagrange theorem, no quadratic-irrational
predicate, no reduced surds. `grep -rn "eriodic" Mathlib/Algebra/ContinuedFractions/`
returns nothing. That gap is what this file fills.

## Building

The Mathlib forks in `~/git/` have no build, and `mathlib4-fork-primitive` is a
broken git worktree (parent `~/git/mathlib4-fork/.git` missing). Built against
the Mathlib inside an unrelated project, same toolchain `v4.30.0-rc2`:

```bash
cd ~/git/experiments/waarnar/loop-experiment/lean
lake env lean ~/git/continued-fractions/lean/Palindrome.lean   # ~35s
```
