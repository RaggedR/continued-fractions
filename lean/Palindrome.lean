/-
The palindrome in the continued fraction of `√n`  —  design skeleton.

Companion to `palindrome.tex` (Legendre's theorem, resting on Galois').  The
strategy here is deliberate and is the main thing this file is testing:

  *  All of the mathematical content is a statement about **integer sequences**.
     The PQa recurrence `(P k, Q k)` is defined over `ℤ`, `Reduced` is stated as
     four integer inequalities rather than with `√n`, and the palindrome is an
     identity between integers.  Nothing before §5 mentions `ℝ`.

  *  Mathlib's `GenContFract.of (√n)` appears **once**, in §5, as a bridge.  It
     is what makes the result about Mathlib's continued fractions rather than
     about our own definition, and it is the only place `⌊·⌋` of an irrational
     has to be fought.

Mathlib supplies more than expected on the matrix side: `Matrix.discr`,
`Matrix.IsParabolic/IsHyperbolic/IsElliptic` and `ModularGroup.T` already exist,
so §4 is mostly assembly.  It supplies **nothing** on the periodicity side:
there is no notion of a quadratic irrational and no Lagrange theorem anywhere.
§2 and §3 are therefore the real work.
-/
import Mathlib.Algebra.ContinuedFractions.Computation.Basic
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.NumberTheory.Real.Irrational

namespace Palindrome

open Matrix

/-! ## §1  The PQa recurrence, entirely over `ℤ` -/

/-- `a0 n = ⌊√n⌋`, computed in `ℕ` and cast. -/
def a0 (n : ℕ) : ℤ := (Nat.sqrt n : ℤ)

/-- The partial quotient read off a state: `⌊(a₀ + P)/Q⌋`. -/
def quo (n : ℕ) (P Q : ℤ) : ℤ := (a0 n + P) / Q

/-- One PQa step: `P' = aQ - P`, `Q' = (n - P'²)/Q`.

Defining this as a standalone map, rather than inlining it into a recursion, is
what lets §3 treat periodicity as a statement about *iterating a function on a
finite set*. -/
def step (n : ℕ) (s : ℤ × ℤ) : ℤ × ℤ :=
  let p := quo n s.1 s.2 * s.2 - s.1
  (p, ((n : ℤ) - p ^ 2) / s.2)

/-- **The inverse step.**  Given a reduced `(P', Q')`, the previous state is
recoverable: `Q = (n - P'²)/Q'`, then `a = ⌊(a₀ + P')/Q⌋`, then `P = aQ - P'`.

The derivation is that for reduced `α'` one has `-1/α̅' = (√n + P')/Q`, so the
partial quotient is read off `α'` alone.  Note the shape: this is `step` with
`P` and `P'` exchanged — the invertibility of the algorithm and the palindrome
are the same symmetry, which is why `palindrome.tex` proves the palindrome by
transposing a matrix. -/
def unstep (n : ℕ) (s : ℤ × ℤ) : ℤ × ℤ :=
  let Q := ((n : ℤ) - s.1 ^ 2) / s.2
  (quo n s.1 Q * Q - s.1, Q)

/-- The PQa state sequence for `√n`: iterate `step` from `(P₀, Q₀) = (0, 1)`. -/
def state (n : ℕ) (k : ℕ) : ℤ × ℤ := (step n)^[k] (0, 1)

lemma state_succ (n : ℕ) (k : ℕ) : state n (k + 1) = step n (state n k) :=
  Function.iterate_succ_apply' _ _ _

lemma state_add (n : ℕ) (j k : ℕ) : state n (j + k) = (step n)^[j] (state n k) := by
  simp [state, ← Function.iterate_add_apply]

/-- `P k`, the numerator offset of the `k`-th complete quotient. -/
def P (n : ℕ) (k : ℕ) : ℤ := (state n k).1

/-- `Q k`, the denominator of the `k`-th complete quotient. -/
def Q (n : ℕ) (k : ℕ) : ℤ := (state n k).2

/-- `a k`, the `k`-th partial quotient. -/
def a (n : ℕ) (k : ℕ) : ℤ := quo n (P n k) (Q n k)

@[simp] lemma P_zero (n : ℕ) : P n 0 = 0 := rfl
@[simp] lemma Q_zero (n : ℕ) : Q n 0 = 1 := rfl

lemma P_succ (n : ℕ) (k : ℕ) : P n (k + 1) = a n k * Q n k - P n k := by
  simp [P, Q, a, state_succ, step, quo]

lemma Q_succ (n : ℕ) (k : ℕ) :
    Q n (k + 1) = ((n : ℤ) - P n (k + 1) ^ 2) / Q n k := by
  simp [P, Q, state_succ, step]

/-- `a₀` really is the zeroth partial quotient. -/
@[simp] lemma a_zero (n : ℕ) : a n 0 = a0 n := by
  simp [a, quo, P, Q, state]

/-! Sanity checks: these agree with `period.py` and with the tables in
`palindrome.tex` and `cube-roots.tex`.  `#guard` fails at elaboration if the
definitions drift. -/
section Guards
#guard ((List.range 5).map (a 7)  == [2, 1, 1, 1, 4])
#guard ((List.range 6).map (a 13) == [3, 1, 1, 1, 1, 6])
#guard ((List.range 5).map (Q 7)  == [1, 3, 2, 3, 1])
#guard ((List.range 13).map (a 46) == [6, 1, 3, 1, 1, 2, 6, 2, 1, 1, 3, 1, 12])
end Guards

/-! ## §2  Integrality, and reduced surds

`palindrome.tex` §2 and Lemma 2.  The divisibility invariant is what makes the
recurrence exact; the four inequalities are Lemma 2 with `√n` cleared, which is
what keeps this section inside `ℤ`. -/

/-- The identity behind the whole integrality argument:
`n - P_{k+1}² = (n - P_k²) + Q_k · a_k · (2P_k - a_k Q_k)`.

(`palindrome.tex` §2 states this without the factor `a_k`; that version is false
— it fails for 14,725 states with `n < 2000` — though the conclusion survives,
since `Q_k` divides either form.) -/
lemma sub_P_succ_sq (n : ℕ) (k : ℕ) :
    (n : ℤ) - P n (k + 1) ^ 2
      = ((n : ℤ) - P n k ^ 2) + Q n k * (a n k * (2 * P n k - a n k * Q n k)) := by
  rw [P_succ]; ring

/-- `Q k ∣ n - (P k)²` for every `k`: the divisibility that makes every step of
the recurrence an exact integer division. -/
theorem Q_dvd (n : ℕ) (k : ℕ) : Q n k ∣ (n : ℤ) - P n k ^ 2 := by
  induction k with
  | zero => simp
  | succ m ih =>
      have h : Q n m ∣ (n : ℤ) - P n (m + 1) ^ 2 := by
        rw [sub_P_succ_sq]
        exact dvd_add ih (dvd_mul_right _ _)
      exact ⟨Q n m, by rw [Q_succ]; exact (Int.ediv_mul_cancel h).symm⟩

/-- Consecutive denominators multiply to `n - P²`.  This is the form the later
arguments want, since it exhibits the previous `Q` as an explicit cofactor. -/
theorem Q_mul_Q_succ (n : ℕ) (k : ℕ) :
    Q n k * Q n (k + 1) = (n : ℤ) - P n (k + 1) ^ 2 := by
  have h : Q n k ∣ (n : ℤ) - P n (k + 1) ^ 2 := by
    rw [sub_P_succ_sq]
    exact dvd_add (Q_dvd n k) (dvd_mul_right _ _)
  rw [Q_succ]; exact Int.mul_ediv_cancel' h

/-- `(P + √n)/Q` is a **reduced** surd: `α > 1` and `-1 < α̅ < 0`.

Stated without `√n`.  Because `n` is not a square, `√n` is irrational, so for
every integer `m` one has `m < √n ↔ m ≤ a₀` and `√n < m ↔ a₀ < m`.  Each
defining condition therefore becomes a *linear* inequality:

| on `α` | | here |
| --- | --- | --- |
| `α̅ < 0`  | `P < √n`     | `P ≤ a₀` |
| `α̅ > -1` | `√n < P + Q` | `a₀ < P + Q` |
| `α > 1`  | `Q - P < √n` | `Q - P ≤ a₀` |

Linearity is the point.  The bounds of `palindrome.tex` Lemma 2 — `0 < P < √n`
and `0 < Q < 2√n` — then follow by `omega`, where on paper they need a case
analysis on the sign of `P`.  The divisibility is carried along because every
state of the recurrence satisfies it (`Q_dvd`) and `unstep` needs it. -/
structure Reduced (n : ℕ) (P Q : ℤ) : Prop where
  Q_pos : 0 < Q
  P_le : P ≤ a0 n
  lt_add : a0 n < P + Q
  sub_le : Q - P ≤ a0 n
  dvd : Q ∣ (n : ℤ) - P ^ 2

namespace Reduced
variable {n : ℕ} {P Q : ℤ}

/-- `0 < P`: add `Q - P ≤ a₀` to `a₀ < P + Q`.  Lemma 2's case analysis, gone. -/
lemma P_pos (h : Reduced n P Q) : 0 < P := by
  have := h.lt_add; have := h.sub_le; omega

/-- `Q ≤ 2a₀`, the integral form of `Q < 2√n`. -/
lemma Q_le (h : Reduced n P Q) : Q ≤ 2 * a0 n := by
  have := h.P_le; have := h.sub_le; omega

/-- `0 ≤ a₀ - P < Q`: exactly what makes the partial quotient recoverable. -/
lemma sub_nonneg (h : Reduced n P Q) : 0 ≤ a0 n - P := by have := h.P_le; omega

lemma sub_lt (h : Reduced n P Q) : a0 n - P < Q := by have := h.lt_add; omega

end Reduced

/-- Partial quotients of reduced surds are at least 1, since `Q ≤ a₀ + P`. -/
lemma one_le_quo (n : ℕ) {P Q : ℤ} (hs : Reduced n P Q) : 1 ≤ quo n P Q := by
  have hQ : (0 : ℤ) < Q := hs.Q_pos
  have hdm : Q * quo n P Q + (a0 n + P) % Q = a0 n + P := by
    rw [quo]; exact Int.mul_ediv_add_emod _ _
  have hr0 : 0 ≤ (a0 n + P) % Q := Int.emod_nonneg _ hQ.ne'
  have hr1 : (a0 n + P) % Q < Q := Int.emod_lt_of_pos _ hQ
  have := hs.sub_le
  nlinarith

/-- Only finitely many reduced surds belong to a given `n` — the pigeonhole
that forces periodicity.  Immediate from `Reduced` as stated, since it bounds
`P` and `Q` in `ℤ`. -/
theorem finite_reduced (n : ℕ) : {x : ℤ × ℤ | Reduced n x.1 x.2}.Finite := by
  apply Set.Finite.subset
    ((Set.finite_Ioo (0 : ℤ) (a0 n + 1)).prod (Set.finite_Ioo (0 : ℤ) (2 * a0 n + 1)))
  rintro ⟨p, q⟩ h
  exact ⟨⟨h.P_pos, by have := h.P_le; omega⟩, h.Q_pos, by have := h.Q_le; omega⟩

/-! ## §3  Pure periodicity, without Galois' theorem

The classical route here is Galois' theorem: a surd is reduced *iff* its
expansion is purely periodic.  We do not need the biconditional, and we do not
need it for all surds — only that one orbit is purely periodic.  That follows
from three facts, of which the third is a computation rather than a theorem:

  1.  the orbit lies in a finite set  (`finite_reduced`),
  2.  the set is forward-invariant    (`step_mapsTo`),
  3.  `step` is **injective** on it   (`unstep_step`, via the explicit inverse).

Pigeonhole then gives eventual periodicity, and injectivity removes the tail of
the rho, so the period starts at once.  Stated for a general map below, since
nothing about continued fractions is involved. -/

/-- **An injective self-map of a finite invariant set has purely periodic
orbits.**  No number theory; this belongs in `Mathlib.Dynamics` and is
plausibly worth upstreaming on its own.  The proof follows
`LinearEquiv.isOfFinOrder_of_finite_of_span_eq_top_of_mapsTo`. -/
theorem exists_iterate_eq_self {α : Type*} {S : Set α} (hS : S.Finite)
    {f : α → α} (hmap : Set.MapsTo f S S) (hinj : Set.InjOn f S)
    {x : α} (hx : x ∈ S) : ∃ L, 0 < L ∧ f^[L] x = x := by
  have hbij : Set.BijOn f S S := (hS.injOn_iff_bijOn_of_mapsTo hmap).mp hinj
  have : Finite S := Set.finite_coe_iff.mpr hS
  set e := Set.BijOn.equiv f hbij with he
  have hfin : IsOfFinOrder e := isOfFinOrder_of_finite e
  refine ⟨orderOf e, hfin.orderOf_pos, ?_⟩
  have key : ∀ (m : ℕ) (y : S), (e ^ m) y = ⟨f^[m] y, hmap.iterate m y.2⟩ := by
    intro m
    induction m with
    | zero => intro y; rfl
    | succ i ih =>
        intro y
        rw [pow_succ, Equiv.Perm.mul_apply, ih (e y)]
        simp [he, Set.BijOn.equiv, Function.iterate_succ_apply]
  have h := key (orderOf e) ⟨x, hx⟩
  rw [pow_orderOf_eq_one] at h
  simpa [Subtype.ext_iff] using h.symm

/-- `a₀² < n`, strict because `n` is not a square. -/
lemma a0_sq_lt (n : ℕ) (hn : ¬IsSquare n) : a0 n ^ 2 < (n : ℤ) := by
  have h1 : Nat.sqrt n ^ 2 ≤ n := Nat.sqrt_le' n
  rcases eq_or_lt_of_le h1 with h | h
  · exact absurd (⟨Nat.sqrt n, by rw [pow_two] at h; exact h.symm⟩ : IsSquare n) hn
  · simp only [a0]; exact_mod_cast h

/-- `n < (a₀ + 1)²`. -/
lemma lt_a0_succ_sq (n : ℕ) : (n : ℤ) < (a0 n + 1) ^ 2 := by
  have h : (n : ℤ) < ((Nat.sqrt n + 1 : ℕ) : ℤ) ^ 2 := by exact_mod_cast Nat.lt_succ_sqrt' n
  push_cast at h
  simpa [a0] using h

/-- **`step` preserves reducedness** (`palindrome.tex`, Lemma 3).

The classical argument is about the conjugate: `α̅' = 1/(α̅ - A)` with
`α̅ ∈ (-1,0)` and `A ≥ 1`, so `|α̅ - A| > 1` and `α̅' ∈ (-1,0)`.  Here each step
is an integer inequality.  Writing `a = a₀`, `A = ⌊(a+P)/Q⌋`, `P' = AQ - P`:

* `P' ≤ a` and `a < P' + Q` are the two halves of the floor property, linear;
* `1 ≤ A` needs only `Q ≤ a + P`, linear;
* `Q ≤ P + P'` follows, hence `Q - P' ≤ P ≤ a`;
* `a < P' + Q'` — if not, `Q·Q' ≤ Q(a - P') ≤ (a+P')(a-P') = a² - P'²`, giving
  `n ≤ a²`, against `a² < n`;
* `Q' - P' ≤ a` — if not, `Q·Q' ≥ Q(a+P'+1) ≥ (a-P'+1)(a+P'+1) = (a+1)² - P'²`,
  giving `n ≥ (a+1)²`, against `n < (a+1)²`.

The two quadratic steps are the only places the `a² < n < (a+1)²` sandwich is
used, and they are exactly where the conjugate bound `-1 < α̅ < 0` lives. -/
theorem step_mapsTo (n : ℕ) (hn : ¬IsSquare n) :
    Set.MapsTo (step n) {x : ℤ × ℤ | Reduced n x.1 x.2} {x : ℤ × ℤ | Reduced n x.1 x.2} := by
  rintro ⟨P, Q⟩ hs
  have hQ : (0 : ℤ) < Q := hs.Q_pos
  have hP : P ≤ a0 n := hs.P_le
  have hQP : Q - P ≤ a0 n := hs.sub_le
  have ha2 : a0 n ^ 2 < (n : ℤ) := a0_sq_lt n hn
  have hn1 : (n : ℤ) < (a0 n + 1) ^ 2 := lt_a0_succ_sq n
  obtain ⟨A, hA⟩ : ∃ A, A = quo n P Q := ⟨_, rfl⟩
  -- the floor property, as a division with remainder
  have hdm : Q * A + (a0 n + P) % Q = a0 n + P := by
    rw [hA, quo]; exact Int.mul_ediv_add_emod _ _
  have hr0 : 0 ≤ (a0 n + P) % Q := Int.emod_nonneg _ hQ.ne'
  have hr1 : (a0 n + P) % Q < Q := Int.emod_lt_of_pos _ hQ
  have hA1 : Q * A ≤ a0 n + P := by omega
  have hA2 : a0 n + P < Q * A + Q := by omega
  obtain ⟨p, hp⟩ : ∃ p, p = A * Q - P := ⟨_, rfl⟩
  have hPle : p ≤ a0 n := by rw [hp]; nlinarith
  have halt : a0 n < p + Q := by rw [hp]; nlinarith
  have hAge1 : 1 ≤ A := by nlinarith
  have hQlePp : Q ≤ P + p := by rw [hp]; nlinarith
  have hQsub : Q - p ≤ a0 n := by omega
  have hPgt : -a0 n < p := by omega
  -- the divisibility survives, with the old `Q` as cofactor
  have hdvd : Q ∣ (n : ℤ) - p ^ 2 := by
    rw [hp]
    have e : (n : ℤ) - (A * Q - P) ^ 2
        = ((n : ℤ) - P ^ 2) + Q * (A * (2 * P - A * Q)) := by ring
    rw [e]; exact dvd_add hs.dvd (dvd_mul_right _ _)
  obtain ⟨q, hq⟩ : ∃ q, q = ((n : ℤ) - p ^ 2) / Q := ⟨_, rfl⟩
  have hQQ : Q * q = (n : ℤ) - p ^ 2 := by rw [hq]; exact Int.mul_ediv_cancel' hdvd
  have hnum : 0 < (n : ℤ) - p ^ 2 := by nlinarith
  have hqpos : 0 < q := by
    rcases lt_trichotomy q 0 with h | h | h
    · nlinarith
    · rw [h, mul_zero] at hQQ; omega
    · exact h
  have hstep : step n (P, Q) = (p, q) := by simp only [hq, hp, hA]; rfl
  show Reduced n (step n (P, Q)).1 (step n (P, Q)).2
  rw [hstep]
  refine ⟨hqpos, hPle, ?_, ?_, ⟨Q, by rw [← hQQ]; ring⟩⟩
  · -- a₀ < p + q : else Q·q ≤ (a₀+p)(a₀-p) = a₀² - p², so n ≤ a₀²
    by_contra hcon
    push Not at hcon
    nlinarith [hQQ, ha2, mul_le_mul (show Q ≤ a0 n + p by omega)
      (show q ≤ a0 n - p by omega) (by omega : (0:ℤ) ≤ q) (by omega : (0:ℤ) ≤ a0 n + p)]
  · -- q - p ≤ a₀ : else Q·q ≥ (a₀-p+1)(a₀+p+1) = (a₀+1)² - p², so n ≥ (a₀+1)²
    by_contra hcon
    push Not at hcon
    nlinarith [hQQ, hn1, mul_le_mul (show a0 n - p + 1 ≤ Q by omega)
      (show a0 n + p + 1 ≤ q by omega) (by omega : (0:ℤ) ≤ a0 n + p + 1)
      (by omega : (0:ℤ) ≤ Q)]

/-- `n` is not a square, so `n - m²` never vanishes. -/
lemma sub_sq_ne_zero (n : ℕ) (hn : ¬IsSquare n) (m : ℤ) : (n : ℤ) - m ^ 2 ≠ 0 := by
  intro h
  have h2 : (n : ℤ) = m * m := by rw [pow_two] at h; linarith
  exact hn ⟨m.natAbs, Nat.cast_injective (R := ℤ) (by rw [Int.natAbs_mul_self]; exact h2)⟩

/-- `unstep` with its `let` unfolded. -/
lemma unstep_eq (n : ℕ) (p q : ℤ) :
    unstep n (p, q)
      = (quo n p (((n : ℤ) - p ^ 2) / q) * (((n : ℤ) - p ^ 2) / q) - p,
         ((n : ℤ) - p ^ 2) / q) := rfl

/-- **`unstep` inverts `step` on reduced states.**  An identity between exact
integer divisions, not an inequality argument.  The two facts that make it work
are the *linear* consequences of `Reduced`: `0 ≤ a₀ - P` and `a₀ - P < Q`, which
force `⌊(a₀ - P)/Q⌋ = 0` and so recover the partial quotient from the next state
alone.  Recovering the previous denominator is `Q · Q' = n - P'²` read backwards.

Checked numerically on 71,936 reduced states for `n < 4000` before being stated
(`scratchpad/inverse.py`, zero failures). -/
theorem unstep_step (n : ℕ) (hn : ¬IsSquare n) {s : ℤ × ℤ}
    (hs : Reduced n s.1 s.2) : unstep n (step n s) = s := by
  obtain ⟨P, Q⟩ := s
  have hQ : Q ≠ 0 := hs.Q_pos.ne'
  have hstep : step n (P, Q)
      = (quo n P Q * Q - P, ((n : ℤ) - (quo n P Q * Q - P) ^ 2) / Q) := rfl
  obtain ⟨A, hA⟩ : ∃ A, A = quo n P Q := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, p = A * Q - P := ⟨_, rfl⟩
  -- the divisibility survives a step, so `Q · Q' = n - P'²`
  have hdvd : Q ∣ (n : ℤ) - p ^ 2 := by
    rw [hp]
    have e : (n : ℤ) - (A * Q - P) ^ 2
        = ((n : ℤ) - P ^ 2) + Q * (A * (2 * P - A * Q)) := by ring
    rw [e]; exact dvd_add hs.dvd (dvd_mul_right _ _)
  obtain ⟨q, hq⟩ : ∃ q, q = ((n : ℤ) - p ^ 2) / Q := ⟨_, rfl⟩
  have hmul : Q * q = (n : ℤ) - p ^ 2 := by rw [hq]; exact Int.mul_ediv_cancel' hdvd
  have hne : (n : ℤ) - p ^ 2 ≠ 0 := sub_sq_ne_zero n hn p
  have hqne : q ≠ 0 := by intro h; rw [h, mul_zero] at hmul; exact hne hmul.symm
  -- recover the previous denominator
  have hQrec : ((n : ℤ) - p ^ 2) / q = Q := by
    rw [← hmul, Int.mul_ediv_cancel _ hqne]
  -- recover the partial quotient: `⌊(a₀ + p)/Q⌋ = A` because `⌊(a₀ - P)/Q⌋ = 0`
  have hquo : quo n p Q = A := by
    rw [quo, hp]
    have e : a0 n + (A * Q - P) = (a0 n - P) + A * Q := by ring
    rw [e, Int.add_mul_ediv_right _ _ hQ,
      Int.ediv_eq_zero_of_lt hs.sub_nonneg hs.sub_lt, zero_add]
  rw [hstep, ← hA, ← hp, ← hq, unstep_eq, hQrec, hquo, hp,
    show A * Q - (A * Q - P) = P from by ring]

/-- `step` is injective on reduced states — immediate from `unstep_step`. -/
theorem step_injOn (n : ℕ) (hn : ¬IsSquare n) :
    Set.InjOn (step n) {x : ℤ × ℤ | Reduced n x.1 x.2} := fun _ hx _ hy h => by
  rw [← unstep_step n hn hx, ← unstep_step n hn hy, h]

/-- The first complete quotient is `(a₀ + √n)/(n - a₀²)`. -/
lemma state_one (n : ℕ) : state n 1 = (a0 n, (n : ℤ) - a0 n ^ 2) := by
  simp [state, step, quo]

/-- **Every complete quotient from index 1 on is reduced** (`palindrome.tex`,
Lemma 3).  The base case is the sandwich `a₀² < n < (a₀+1)²` and nothing else;
the step is `step_mapsTo`. -/
theorem reduced_state (n : ℕ) (hn : ¬IsSquare n) {k : ℕ} (hk : 1 ≤ k) :
    state n k ∈ {x : ℤ × ℤ | Reduced n x.1 x.2} := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction j with
  | zero =>
      rw [Nat.add_zero, state_one]
      have h1 := a0_sq_lt n hn
      have h2 := lt_a0_succ_sq n
      exact ⟨by nlinarith, le_rfl, by nlinarith, by nlinarith, dvd_refl _⟩
  | succ i ih =>
      rw [show 1 + (i + 1) = (1 + i) + 1 from by ring, state_succ]
      exact step_mapsTo n hn (ih (by omega))

theorem Q_ne_zero (n : ℕ) (hn : ¬IsSquare n) (k : ℕ) : Q n k ≠ 0 := by
  cases k with
  | zero => simp
  | succ m => exact (reduced_state n hn (by omega : 1 ≤ m + 1)).Q_pos.ne'

/-- Pure periodicity of the expansion of `√n` from index 1 — what the classical
argument gets from Galois' theorem, obtained here from finiteness plus an
explicit inverse. -/
theorem purely_periodic (n : ℕ) (hn : ¬IsSquare n) :
    ∃ L, 0 < L ∧ ∀ k, 1 ≤ k → state n (k + L) = state n k := by
  obtain ⟨L, hL₀, hL⟩ := exists_iterate_eq_self (finite_reduced n) (step_mapsTo n hn)
    (step_injOn n hn) (x := state n 1) (reduced_state n hn le_rfl)
  refine ⟨L, hL₀, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have : state n (1 + j + L) = (step n)^[j] ((step n)^[L] (state n 1)) := by
    simp [state_add, ← Function.iterate_add_apply, Nat.add_comm]
  rw [this, hL, ← state_add, Nat.add_comm]

/-- The period: the least `L > 0` with `state n (k + L) = state n k` for `k ≥ 1`. -/
noncomputable def period (n : ℕ) (hn : ¬IsSquare n) : ℕ :=
  @Nat.find _ (Classical.decPred _) (purely_periodic n hn)

/-- The defining property of `period`, with the `Classical` instance supplied. -/
lemma period_spec (n : ℕ) (hn : ¬IsSquare n) :
    0 < period n hn ∧ ∀ k, 1 ≤ k → state n (k + period n hn) = state n k :=
  @Nat.find_spec _ (Classical.decPred _) (purely_periodic n hn)

lemma period_pos (n : ℕ) (hn : ¬IsSquare n) : 0 < period n hn := (period_spec n hn).1

lemma state_period_add (n : ℕ) (hn : ¬IsSquare n) {k : ℕ} (hk : 1 ≤ k) :
    state n (k + period n hn) = state n k := (period_spec n hn).2 k hk

/-- **The block closes at `(a₀, 1)`.**  Run the period once and come back to
`state 1`; then `unstep` that, and the computation `(n - a₀²)/(n - a₀²) = 1`
does the rest.  This is the `Q = 1, P = a₀` test that `period.py` uses to detect
the end of the block, here derived rather than assumed. -/
theorem state_period (n : ℕ) (hn : ¬IsSquare n) : state n (period n hn) = (a0 n, 1) := by
  have hL := period_pos n hn
  have h1 : step n (state n (period n hn)) = state n 1 := by
    rw [← state_succ, show period n hn + 1 = 1 + period n hn from by ring]
    exact state_period_add n hn le_rfl
  have h2 := unstep_step n hn (reduced_state n hn hL)
  rw [h1, state_one] at h2
  have hne : (n : ℤ) - a0 n ^ 2 ≠ 0 := sub_sq_ne_zero n hn _
  rw [← h2, unstep_eq]
  simp only [Int.ediv_self hne, Int.ediv_one, quo, mul_one, Prod.mk.injEq]
  exact ⟨by ring, trivial⟩

/-- **The block closes with `2a₀`** — `palindrome.tex` Theorem 1, first half. -/
theorem a_period (n : ℕ) (hn : ¬IsSquare n) : a n (period n hn) = 2 * a0 n := by
  have h := state_period n hn
  simp only [a, quo, P, Q, h]
  rw [Int.ediv_one]; ring

/-- `Reduced` for the state sequence, in `P`/`Q` form. -/
lemma reduced_PQ (n : ℕ) (hn : ¬IsSquare n) {k : ℕ} (hk : 1 ≤ k) :
    Reduced n (P n k) (Q n k) := reduced_state n hn hk

/-- Running the period any number of times returns to the same state. -/
lemma state_mul_period (n : ℕ) (hn : ¬IsSquare n) : ∀ j, 1 ≤ j →
    state n (j * period n hn) = state n (period n hn) := by
  intro j
  induction j with
  | zero => intro h; exact absurd h (by omega)
  | succ m ih =>
      intro _
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · norm_num
      · have hP := period_pos n hn
        have h1 : 1 ≤ m * period n hn := Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by omega) (by omega))
        rw [show (m + 1) * period n hn = m * period n hn + period n hn from by ring,
          state_period_add n hn h1, ih hm]

/-- If `Q k = 1` then `k` is itself a period, so `L ∣ k`. -/
lemma period_dvd_of_Q_eq_one (n : ℕ) (hn : ¬IsSquare n) :
    ∀ k, 1 ≤ k → Q n k = 1 → period n hn ∣ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hQ1
    -- `Q k = 1` forces `P k = a₀`, so the state is exactly `state L`
    have hP : P n k = a0 n := by
      have h1 := (reduced_PQ n hn hk).P_le
      have h2 := (reduced_PQ n hn hk).lt_add
      omega
    have hst : state n k = (a0 n, 1) := by
      have h : state n k = (P n k, Q n k) := rfl
      rw [h, hP, hQ1]
    have hper : 0 < k ∧ ∀ t, 1 ≤ t → state n (t + k) = state n t := by
      refine ⟨hk, fun t ht => ?_⟩
      rw [state_add, hst, ← state_period n hn, ← state_add]
      exact state_period_add n hn ht
    have hLk : period n hn ≤ k :=
      @Nat.find_min' _ (Classical.decPred _) (purely_periodic n hn) k hper
    rcases eq_or_lt_of_le hLk with h | h
    · exact h ▸ dvd_refl _
    · have hp := period_pos n hn
      have hkL : 1 ≤ k - period n hn := by omega
      have hQ' : Q n (k - period n hn) = 1 := by
        have he : state n (k - period n hn) = state n k := by
          rw [← state_period_add n hn hkL,
            show k - period n hn + period n hn = k from by omega]
        show (state n (k - period n hn)).2 = 1
        rw [he]; exact hQ1
      obtain ⟨c, hc⟩ := ih (k - period n hn) (by omega) hkL hQ'
      refine ⟨c + 1, ?_⟩
      have he : k = (k - period n hn) + period n hn := by omega
      rw [he, hc]; ring

/-- **The period closes exactly where `Q` returns to 1.** -/
theorem Q_eq_one_iff (n : ℕ) (hn : ¬IsSquare n) {k : ℕ} (hk : 1 ≤ k) :
    Q n k = 1 ↔ period n hn ∣ k := by
  refine ⟨period_dvd_of_Q_eq_one n hn k hk, fun hd => ?_⟩
  obtain ⟨j, hj⟩ := hd
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · omega
    · exact h
  show (state n k).2 = 1
  rw [hj, mul_comm, state_mul_period n hn j hj1, state_period]

/-- **The partial quotient is recoverable from the next numerator.**
`⌊(a₀ + P')/Q⌋ = ⌊(a₀ + P)/Q⌋`, because `0 ≤ a₀ - P < Q`.  Extracted from the
proof of `unstep_step`, and the engine of the palindrome. -/
lemma quo_step_fst (n : ℕ) {s : ℤ × ℤ} (hs : Reduced n s.1 s.2) :
    quo n (step n s).1 s.2 = quo n s.1 s.2 := by
  obtain ⟨P, Q⟩ := s
  have hQ : Q ≠ 0 := hs.Q_pos.ne'
  show quo n (quo n P Q * Q - P) Q = quo n P Q
  rw [quo, show a0 n + (quo n P Q * Q - P) = (a0 n - P) + quo n P Q * Q from by ring,
    Int.add_mul_ediv_right _ _ hQ, Int.ediv_eq_zero_of_lt hs.sub_nonneg hs.sub_lt, zero_add]

/-! ### The reversal

`rev` swaps `Q_k` for `Q_{k-1}`, keeping `P_k`.  It conjugates `step` into
`unstep`, so it reverses the cycle; and it fixes the cycle of `√n` because
`rev (state 1) = (a₀, 1) = state L`.  A cycle equal to its own reversal is the
palindrome. -/

/-- The reversal involution on states. -/
def rev (n : ℕ) (s : ℤ × ℤ) : ℤ × ℤ := (s.1, ((n : ℤ) - s.1 ^ 2) / s.2)

lemma rev_step_eq (n : ℕ) (hn : ¬IsSquare n) {s : ℤ × ℤ} (hs : Reduced n s.1 s.2) :
    rev n (step n s) = ((step n s).1, s.2) := by
  obtain ⟨P, Q⟩ := s
  have hQ : Q ≠ 0 := hs.Q_pos.ne'
  obtain ⟨p, hp⟩ : ∃ p, p = quo n P Q * Q - P := ⟨_, rfl⟩
  have hdvd : Q ∣ (n : ℤ) - p ^ 2 := by
    rw [hp]
    have e : (n : ℤ) - (quo n P Q * Q - P) ^ 2
        = ((n : ℤ) - P ^ 2) + Q * (quo n P Q * (2 * P - quo n P Q * Q)) := by ring
    rw [e]; exact dvd_add hs.dvd (dvd_mul_right _ _)
  obtain ⟨q, hq⟩ : ∃ q, q = ((n : ℤ) - p ^ 2) / Q := ⟨_, rfl⟩
  have hQQ : Q * q = (n : ℤ) - p ^ 2 := by rw [hq]; exact Int.mul_ediv_cancel' hdvd
  have hstep : step n (P, Q) = (p, q) := by simp only [hq, hp]; rfl
  have hne : (n : ℤ) - p ^ 2 ≠ 0 := sub_sq_ne_zero n hn p
  have hqne : q ≠ 0 := by intro h; rw [h, mul_zero] at hQQ; exact hne hQQ.symm
  rw [hstep, rev, ← hQQ, Int.mul_ediv_cancel _ hqne]

lemma unstep_rev_eq (n : ℕ) (hn : ¬IsSquare n) {s : ℤ × ℤ} (hs : Reduced n s.1 s.2) :
    unstep n (rev n s) = ((step n s).1, s.2) := by
  obtain ⟨P, Q⟩ := s
  have hQ : Q ≠ 0 := hs.Q_pos.ne'
  obtain ⟨R, hR⟩ : ∃ R, R = ((n : ℤ) - P ^ 2) / Q := ⟨_, rfl⟩
  have hQR : Q * R = (n : ℤ) - P ^ 2 := by rw [hR]; exact Int.mul_ediv_cancel' hs.dvd
  have hne : (n : ℤ) - P ^ 2 ≠ 0 := sub_sq_ne_zero n hn P
  have hRne : R ≠ 0 := by intro h; rw [h, mul_zero] at hQR; exact hne hQR.symm
  have : rev n (P, Q) = (P, R) := by rw [rev, ← hR]
  rw [this, unstep_eq, ← hQR, Int.mul_ediv_cancel _ hRne]
  rfl

/-- **`rev` conjugates `step` into `unstep`** — both sides are `(P', Q)`. -/
lemma rev_step (n : ℕ) (hn : ¬IsSquare n) {s : ℤ × ℤ} (hs : Reduced n s.1 s.2) :
    rev n (step n s) = unstep n (rev n s) := by
  rw [rev_step_eq n hn hs, unstep_rev_eq n hn hs]

/-- **The cycle is its own reversal:** `state (L + 1 - k) = rev (state k)`. -/
theorem state_rev (n : ℕ) (hn : ¬IsSquare n) {k : ℕ} (h1 : 1 ≤ k)
    (h2 : k ≤ period n hn) : state n (period n hn + 1 - k) = rev n (state n k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h1
  induction j with
  | zero =>
      have hne : (n : ℤ) - a0 n ^ 2 ≠ 0 := sub_sq_ne_zero n hn _
      rw [show period n hn + 1 - (1 + 0) = period n hn from by omega, state_period,
        Nat.add_zero, state_one, rev, Int.ediv_self hne]
  | succ i ih =>
      have hkL : 1 + i ≤ period n hn := by omega
      have hi1 : (1 : ℕ) ≤ 1 + i := by omega
      have hIH := ih hi1 hkL
      have hLk : 1 ≤ period n hn - (1 + i) := by omega
      rw [show 1 + (i + 1) = (1 + i) + 1 from by ring, state_succ,
        rev_step n hn (reduced_state n hn hi1), ← hIH,
        show period n hn + 1 - (1 + i) = (period n hn - (1 + i)) + 1 from by omega,
        state_succ, unstep_step n hn (reduced_state n hn hLk),
        show period n hn + 1 - ((1 + i) + 1) = period n hn - (1 + i) from by omega]

/-- **Legendre's theorem, the palindrome.**  `palindrome.tex` Theorem 1.

`state (L - i) = rev (state (i+1)) = (P_{i+1}, Q_i)`, so `a_{L-i} = ⌊(a₀+P_{i+1})/Q_i⌋`,
and `quo_step_fst` says that is `⌊(a₀+P_i)/Q_i⌋ = a_i`. -/
theorem palindrome (n : ℕ) (hn : ¬IsSquare n) {i : ℕ}
    (h₁ : 1 ≤ i) (h₂ : i < period n hn) :
    a n i = a n (period n hn - i) := by
  have hr : state n (period n hn - i) = rev n (state n (i + 1)) := by
    have h := state_rev n hn (k := i + 1) (by omega) (by omega)
    rwa [show period n hn + 1 - (i + 1) = period n hn - i from by omega] at h
  have hrev : rev n (state n (i + 1)) = (P n (i + 1), Q n i) := by
    rw [rev]
    refine Prod.ext rfl ?_
    show ((n : ℤ) - (state n (i + 1)).1 ^ 2) / (state n (i + 1)).2 = Q n i
    rw [show (state n (i + 1)).1 = P n (i + 1) from rfl,
      show (state n (i + 1)).2 = Q n (i + 1) from rfl,
      ← Q_mul_Q_succ n i, Int.mul_ediv_cancel _ (Q_ne_zero n hn (i + 1))]
  have hq : quo n (P n (i + 1)) (Q n i) = a n i := by
    have h := quo_step_fst n (reduced_state n hn h₁)
    have hP1 : (step n (state n i)).1 = P n (i + 1) := by
      show (step n (state n i)).1 = (state n (i + 1)).1
      rw [state_succ]
    rw [hP1] at h
    exact h
  have hPm : P n (period n hn - i) = P n (i + 1) := by
    show (state n (period n hn - i)).1 = P n (i + 1)
    rw [hr, hrev]
  have hQm : Q n (period n hn - i) = Q n i := by
    show (state n (period n hn - i)).2 = Q n i
    rw [hr, hrev]
  show quo n (P n i) (Q n i) = quo n (P n (period n hn - i)) (Q n (period n hn - i))
  rw [hPm, hQm]
  exact hq.symm

/-! ## §4  The matrix side

`M a = Tᵃ · J`, and the trichotomy, which Mathlib already has.  The lemmas in
this section are *proved*, not deferred — they are the cheap half, and proving
them here is what checks that the design lines up with Mathlib's API. -/

/-- `M a = !![a, 1; 1, 0]`, the matrix of `x ↦ a + 1/x`. -/
def M (a : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![a, 1; 1, 0]

/-- `J = !![0, 1; 1, 0]`, the matrix of `x ↦ 1/x`. -/
def J : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

/-- **`T` is the alphabet.**  `M a = Tᵃ · J`, with `Tᵃ = !![1, a; 0, 1]`. -/
theorem M_eq_T_mul_J (a : ℤ) : M a = !![1, a; 0, 1] * J := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, J, Matrix.mul_apply, Fin.sum_univ_two]

/-- Every letter of the alphabet is symmetric.  This is the whole mechanism of
the palindrome: transposing a product of symmetric matrices reverses it. -/
@[simp] theorem M_transpose (a : ℤ) : (M a)ᵀ = M a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M]

@[simp] theorem det_M (a : ℤ) : (M a).det = -1 := by
  simp [M, Matrix.det_fin_two_of]

@[simp] theorem trace_M (a : ℤ) : (M a).trace = a := by
  simp [M, Matrix.trace_fin_two]

@[simp] lemma M_apply_00 (c : ℤ) : M c 0 0 = c := by simp [M]
@[simp] lemma M_apply_01 (c : ℤ) : M c 0 1 = 1 := by simp [M]
@[simp] lemma M_apply_10 (c : ℤ) : M c 1 0 = 1 := by simp [M]
@[simp] lemma M_apply_11 (c : ℤ) : M c 1 1 = 0 := by simp [M]

/-- **`T` is the degenerate case.**  `T = !![1,1;0,1]` is parabolic: its
discriminant vanishes and it is not scalar, which is exactly
non-diagonalisability. -/
theorem T_isParabolic : (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ).IsParabolic := by
  rw [Matrix.isParabolic_iff_of_upperTriangular] <;>
    simp [ModularGroup.coe_T]

/-- Reversing a list built by mapping over `range`. -/
lemma reverse_map_range {α : Type*} (L : ℕ) (f : ℕ → α) :
    ((List.range L).map f).reverse = (List.range L).map (fun i => f (L - 1 - i)) := by
  rw [← List.map_reverse, List.range_eq_range', List.reverse_range', List.map_map,
    ← List.range_eq_range']
  simp [Function.comp_def]

/-- `det` of a word in the alphabet is `(-1)` to the length, since every letter
has determinant `-1`. -/
lemma det_map_M_prod (l : List ℤ) : ((l.map M).prod).det = (-1) ^ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [Matrix.det_mul, ih, pow_succ]

/-- The partial quotients of one period, `[a₁, …, a_L]`. -/
noncomputable def periodQuots (n : ℕ) (hn : ¬IsSquare n) : List ℤ :=
  (List.range (period n hn)).map fun i => a n (i + 1)

/-- The period with its last letter `2a₀` removed: `[a₁, …, a_{L-1}]`.  This is
the part that is a palindrome. -/
noncomputable def initQuots (n : ℕ) (hn : ¬IsSquare n) : List ℤ :=
  (List.range (period n hn - 1)).map fun i => a n (i + 1)

/-- The word spelled by one period, `M a₁ ⋯ M a_L`. -/
noncomputable def periodWord (n : ℕ) (hn : ¬IsSquare n) : Matrix (Fin 2) (Fin 2) ℤ :=
  ((periodQuots n hn).map M).prod

/-- `B = M a₁ ⋯ M a_{L-1}`. -/
noncomputable def initWord (n : ℕ) (hn : ¬IsSquare n) : Matrix (Fin 2) (Fin 2) ℤ :=
  ((initQuots n hn).map M).prod

@[simp] lemma length_periodQuots (n : ℕ) (hn : ¬IsSquare n) :
    (periodQuots n hn).length = period n hn := by simp [periodQuots]

@[simp] lemma length_initQuots (n : ℕ) (hn : ¬IsSquare n) :
    (initQuots n hn).length = period n hn - 1 := by simp [initQuots]

/-- `det = (-1)^L`.  So the period word lies in `SL₂(ℤ)` exactly when `L` is
even — the same invariant as the solvability of `x² - n y² = -1`, and the same
one that decides `2cosh R` against `2sinh R`. -/
theorem det_periodWord (n : ℕ) (hn : ¬IsSquare n) :
    (periodWord n hn).det = (-1) ^ (period n hn) := by
  rw [periodWord, det_map_M_prod, length_periodQuots]

/-- **The palindrome, as a matrix identity.**  `B = M a₁ ⋯ M a_{L-1}` is
symmetric.

Two ingredients, and they are the two halves of the story: `M a` is symmetric,
so transposing a word reverses it; and the list `[a₁, …, a_{L-1}]` is its own
reverse, which is `palindrome`. -/
theorem symm_initWord (n : ℕ) (hn : ¬IsSquare n) :
    (initWord n hn)ᵀ = initWord n hn := by
  have hrev : (initQuots n hn).reverse = initQuots n hn := by
    rw [initQuots, reverse_map_range]
    refine List.map_congr_left fun i hi => ?_
    have hiL : i < period n hn - 1 := by simpa using List.mem_range.mp hi
    have hL := period_pos n hn
    rw [show period n hn - 1 - 1 - i + 1 = period n hn - (i + 1) from by omega]
    exact (palindrome n hn (by omega) (by omega)).symm
  rw [initWord, Matrix.transpose_list_prod, List.map_map,
    show (Matrix.transpose ∘ M) = M from funext fun x => M_transpose x,
    ← List.map_reverse, hrev]

/-- `[a₁, …, a_L] = [a₁, …, a_{L-1}] ++ [2a₀]`. -/
lemma periodQuots_eq (n : ℕ) (hn : ¬IsSquare n) :
    periodQuots n hn = initQuots n hn ++ [2 * a0 n] := by
  have hL := period_pos n hn
  rw [periodQuots, initQuots, show period n hn = (period n hn - 1) + 1 from by omega,
    List.range_succ, List.map_append]
  simp only [List.map_cons, List.map_nil]
  rw [show period n hn - 1 + 1 = period n hn from by omega, a_period]

/-- `A = B · M(2a₀)`. -/
lemma periodWord_eq (n : ℕ) (hn : ¬IsSquare n) :
    periodWord n hn = initWord n hn * M (2 * a0 n) := by
  rw [periodWord, periodQuots_eq, List.map_append, List.prod_append, initWord]
  simp

/-- **`tr A = 2x`.**  Here `x` is the top-left entry of the convergent word
`M a₀ · B`, which is the fundamental Pell solution.  The proof is two lines of
`ring` once `B` is known to be symmetric: writing `B = !![r,s;s,t]`,

`tr (B · M(2a₀)) = 2a₀ r + 2s`  and  `(M a₀ · B) 0 0 = a₀ r + s`.

So the trace formula is a *corollary of the palindrome*, not an independent
fact. -/
theorem trace_periodWord (n : ℕ) (hn : ¬IsSquare n) :
    (periodWord n hn).trace = 2 * (M (a0 n) * initWord n hn) 0 0 := by
  have hB : (initWord n hn) 0 1 = (initWord n hn) 1 0 := by
    have := symm_initWord n hn
    calc (initWord n hn) 0 1 = ((initWord n hn)ᵀ) 1 0 := rfl
      _ = (initWord n hn) 1 0 := by rw [this]
  rw [periodWord_eq]
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    M_apply_00, M_apply_01, M_apply_10, M_apply_11]
  rw [hB]; ring

/-! ### Hyperbolicity

`discr = tr² - 4·det`, and `det = (-1)^L`.  For odd `L` the discriminant is
`tr² + 4` and there is nothing to prove.  For even `L` one needs `|tr| ≥ 3`,
which comes from the entries of a word in the alphabet being nonnegative with a
top-left entry at least 1 — an induction on the word. -/

/-- Entries of a word in the alphabet, when every letter is at least 1. -/
lemma M_prod_entries (l : List ℤ) (h : ∀ x ∈ l, 1 ≤ x) :
    1 ≤ (l.map M).prod 0 0 ∧ 0 ≤ (l.map M).prod 0 1 ∧
      0 ≤ (l.map M).prod 1 0 ∧ 0 ≤ (l.map M).prod 1 1 := by
  induction l with
  | nil => norm_num
  | cons x xs ih =>
      obtain ⟨h00, h01, h10, h11⟩ := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
      have hx : 1 ≤ x := h x (List.mem_cons_self ..)
      simp only [List.map_cons, List.prod_cons, Matrix.mul_apply, Fin.sum_univ_two,
        M_apply_00, M_apply_01, M_apply_10, M_apply_11]
      refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- A nonempty word has `(1,0)` entry at least 1: it is the `(0,0)` entry of the
tail. -/
lemma one_le_M_prod_10 (x : ℤ) (l : List ℤ) (h : ∀ y ∈ x :: l, 1 ≤ y) :
    1 ≤ ((x :: l).map M).prod 1 0 := by
  have := (M_prod_entries l fun y hy => h y (List.mem_cons_of_mem _ hy)).1
  simp only [List.map_cons, List.prod_cons, Matrix.mul_apply, Fin.sum_univ_two,
    M_apply_10, M_apply_11]
  linarith

lemma one_le_a0 (n : ℕ) (hn : ¬IsSquare n) : 1 ≤ a0 n := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn ⟨0, rfl⟩
  have : 1 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  simpa [a0] using this

lemma one_le_initQuots (n : ℕ) (hn : ¬IsSquare n) :
    ∀ x ∈ initQuots n hn, 1 ≤ x := by
  intro x hx
  rw [initQuots, List.mem_map] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact one_le_quo n (reduced_state n hn (by omega))

/-- **The period word is hyperbolic**, in Mathlib's sense. -/
theorem isHyperbolic_periodWord (n : ℕ) (hn : ¬IsSquare n) :
    (periodWord n hn).IsHyperbolic := by
  have hdet := det_periodWord n hn
  have htr := trace_periodWord n hn
  rw [Matrix.IsHyperbolic, Matrix.discr_fin_two, hdet, htr]
  rcases Nat.even_or_odd (period n hn) with he | ho
  · -- L even: need |x| ≥ 2, from a nonempty word with entries ≥ 1
    rw [he.neg_one_pow]
    have hL : 2 ≤ period n hn := by
      have := period_pos n hn
      rcases he with ⟨m, hm⟩; omega
    obtain ⟨y, ys, hys⟩ : ∃ y ys, initQuots n hn = y :: ys := by
      have : (initQuots n hn).length ≠ 0 := by rw [length_initQuots]; omega
      exact List.exists_cons_of_ne_nil (fun hc => by simp [hc] at this)
    have h10 : 1 ≤ (initWord n hn) 1 0 := by
      rw [initWord, hys]
      exact one_le_M_prod_10 y ys (by rw [← hys]; exact one_le_initQuots n hn)
    have h00 : 1 ≤ (initWord n hn) 0 0 :=
      (M_prod_entries _ (one_le_initQuots n hn)).1
    have ha := one_le_a0 n hn
    have hx : 2 ≤ (M (a0 n) * initWord n hn) 0 0 := by
      simp only [Matrix.mul_apply, Fin.sum_univ_two, M_apply_00, M_apply_01]
      nlinarith
    nlinarith
  · -- L odd: discr = tr² + 4
    rw [ho.neg_one_pow]
    nlinarith [sq_nonneg (2 * (M (a0 n) * initWord n hn) 0 0)]

/-! ## §5  The bridge to Mathlib's continued fractions

Everything above is about the integer sequence `a n k`.  This section is the one
place `ℝ` appears, and it is what makes the results statements about
`GenContFract.of (√n)` rather than about our own definition. -/

/-- The `k`-th complete quotient, as a real number. -/
noncomputable def alpha (n : ℕ) (k : ℕ) : ℝ := ((P n k : ℝ) + Real.sqrt n) / (Q n k : ℝ)

lemma sqrt_irrational (n : ℕ) (hn : ¬IsSquare n) : Irrational (Real.sqrt n) :=
  irrational_sqrt_natCast_iff.mpr hn

@[simp] lemma alpha_zero (n : ℕ) : alpha n 0 = Real.sqrt n := by simp [alpha]

lemma a0_le_sqrt (n : ℕ) : (a0 n : ℝ) ≤ Real.sqrt n := by
  have h : ((Nat.sqrt n : ℝ)) ^ 2 ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le' n
  calc (a0 n : ℝ) = Real.sqrt (((Nat.sqrt n : ℝ)) ^ 2) := by
        rw [Real.sqrt_sq (by positivity)]; simp [a0]
    _ ≤ Real.sqrt n := Real.sqrt_le_sqrt h

lemma sqrt_lt_a0_succ (n : ℕ) : Real.sqrt n < (a0 n : ℝ) + 1 := by
  have h : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) ^ 2 := by
    have h2 := Nat.lt_succ_sqrt' n
    exact_mod_cast h2
  calc Real.sqrt n < Real.sqrt (((Nat.sqrt n : ℝ) + 1) ^ 2) := Real.sqrt_lt_sqrt (by positivity) h
    _ = (a0 n : ℝ) + 1 := by rw [Real.sqrt_sq (by positivity)]; simp [a0]

lemma Q_pos_all (n : ℕ) (hn : ¬IsSquare n) (k : ℕ) : (0 : ℤ) < Q n k := by
  cases k with
  | zero => simp
  | succ m => exact (reduced_PQ n hn (by omega)).Q_pos

/-- **The floor of the surd is the integer-arithmetic partial quotient:**
`⌊(P + √n)/Q⌋ = ⌊(a₀ + P)/Q⌋`.  The bridge in miniature — the only reason the
exact integer recurrence computes the real algorithm. -/
lemma floor_alpha (n : ℕ) (hn : ¬IsSquare n) (k : ℕ) : ⌊alpha n k⌋ = a n k := by
  have hQ : (0 : ℤ) < Q n k := Q_pos_all n hn k
  have hQR : (0 : ℝ) < (Q n k : ℝ) := by exact_mod_cast hQ
  have hdm : Q n k * a n k + (a0 n + P n k) % Q n k = a0 n + P n k := by
    rw [a, quo]; exact Int.mul_ediv_add_emod _ _
  have hr0 : 0 ≤ (a0 n + P n k) % Q n k := Int.emod_nonneg _ hQ.ne'
  have hr1 : (a0 n + P n k) % Q n k < Q n k := Int.emod_lt_of_pos _ hQ
  have h1 : a n k * Q n k ≤ a0 n + P n k := by nlinarith
  have h2 : a0 n + P n k + 1 ≤ (a n k + 1) * Q n k := by nlinarith
  have h1R : (a n k : ℝ) * (Q n k : ℝ) ≤ (a0 n : ℝ) + (P n k : ℝ) := by exact_mod_cast h1
  have h2R : (a0 n : ℝ) + (P n k : ℝ) + 1 ≤ ((a n k : ℝ) + 1) * (Q n k : ℝ) := by
    exact_mod_cast h2
  rw [alpha, Int.floor_eq_iff, le_div_iff₀ hQR, div_lt_iff₀ hQR]
  refine ⟨by nlinarith [a0_le_sqrt n], by nlinarith [sqrt_lt_a0_succ n]⟩

lemma alpha_succ (n : ℕ) (hn : ¬IsSquare n) (k : ℕ) :
    alpha n (k + 1) = (alpha n k - (a n k : ℝ))⁻¹ := by
  have hQk : ((Q n k : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr (Q_ne_zero n hn k)
  have hQk1 : ((Q n (k + 1) : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr (Q_ne_zero n hn (k + 1))
  have hsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hPk1 : (P n (k + 1) : ℝ) = (a n k : ℝ) * (Q n k : ℝ) - (P n k : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (P_succ n k)
  have hQQ : (Q n k : ℝ) * (Q n (k + 1) : ℝ) = (n : ℝ) - (P n (k + 1) : ℝ) ^ 2 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Q_mul_Q_succ n k)
  have hne : Real.sqrt n - (P n (k + 1) : ℝ) ≠ 0 := by
    intro h
    exact sqrt_irrational n hn ⟨((P n (k + 1) : ℤ) : ℚ), by push_cast; linarith⟩
  have key : alpha n k - (a n k : ℝ) = (Real.sqrt n - (P n (k + 1) : ℝ)) / (Q n k : ℝ) := by
    rw [alpha, hPk1]; field_simp; ring
  rw [key, inv_div, alpha, div_eq_div_iff hQk1 hne]
  nlinarith [hsq, hQQ]

lemma fract_alpha_ne_zero (n : ℕ) (hn : ¬IsSquare n) (k : ℕ) :
    Int.fract (alpha n k) ≠ 0 := by
  rw [Int.fract, sub_ne_zero, floor_alpha n hn k]
  intro h
  have hQ : ((Q n k : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr (Q_ne_zero n hn k)
  rw [alpha, div_eq_iff hQ] at h
  exact sqrt_irrational n hn ⟨((a n k * Q n k - P n k : ℤ) : ℚ), by push_cast; linarith⟩

/-- **The integer recurrence computes Mathlib's stream for `√n`.** -/
theorem stream_eq (n : ℕ) (hn : ¬IsSquare n) (k : ℕ) :
    GenContFract.IntFractPair.stream (Real.sqrt n) k
      = some (GenContFract.IntFractPair.of (alpha n k)) := by
  induction k with
  | zero => rw [GenContFract.IntFractPair.stream_zero, alpha_zero]
  | succ m ih =>
      rw [GenContFract.IntFractPair.stream_succ_of_some ih (fract_alpha_ne_zero n hn m)]
      congr 2
      rw [show (GenContFract.IntFractPair.of (alpha n m)).fr = Int.fract (alpha n m) from rfl,
        Int.fract, floor_alpha n hn m, ← alpha_succ n hn m]

/-- **The partial quotients of Mathlib's continued fraction of `√n` are the
integers `a n k`.**  With this, `palindrome` and `a_period` are statements about
`GenContFract.of (√n)`. -/
theorem stream_fst (n : ℕ) (hn : ¬IsSquare n) (k : ℕ) :
    GenContFract.IntFractPair.stream (Real.sqrt n) k
      = some ⟨a n k, Int.fract (alpha n k)⟩ := by
  rw [stream_eq n hn k, GenContFract.IntFractPair.of, floor_alpha n hn k]

end Palindrome

/-! ## Axiom audit

Machine-checkable record of what is actually proved.  Every statement below
depends only on `propext`, `Classical.choice` and `Quot.sound` — the standard
Mathlib axioms — and **not** on `sorryAx`.  That includes `purely_periodic`
(Lagrange for `√n`), `palindrome` (Legendre), and `stream_fst`, which ties the
integer recurrence to Mathlib's `GenContFract`.  The file contains no `sorry`. -/
section AxiomAudit
#print axioms Palindrome.purely_periodic
#print axioms Palindrome.palindrome
#print axioms Palindrome.a_period
#print axioms Palindrome.Q_eq_one_iff
#print axioms Palindrome.symm_initWord
#print axioms Palindrome.det_periodWord
#print axioms Palindrome.trace_periodWord
#print axioms Palindrome.isHyperbolic_periodWord
#print axioms Palindrome.T_isParabolic
#print axioms Palindrome.stream_eq
#print axioms Palindrome.stream_fst
end AxiomAudit
