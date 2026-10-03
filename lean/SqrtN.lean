/-
# The tower of derived sequences of √n

The instantiation of `Sturmian.tower_period` at `α = √n - ⌊√n⌋`, using
`Palindrome.lean` for the continued fraction of `√n`.  This is Corollary 8.3 of
`../all-the-proofs.tex`.  The same tail sequence instantiates
`Lagrange.quadratic_of_eventually_periodic` (§9) at the end of the file, which
is what shows that theorem's hypotheses are satisfiable.

  for every non-square `n`, exactly `L` derivations return the sequence with its
  first letter removed, where `L` is the period of the continued fraction.

`sturmian.tex` observes this for `n = 2` and `n = 7`.
-/
import Lagrange
import Palindrome
import Sturmian

namespace Sturmian

variable {n : ℕ}

/-- The slope at level `j`: the `j`-th tail of the continued fraction of `√n`. -/
noncomputable def sqrtTail (n : ℕ) (j : ℕ) : ℝ := Int.fract (Palindrome.alpha n j)

/-- The partial quotient at level `j`. -/
noncomputable def sqrtQuot (n : ℕ) (j : ℕ) : ℕ := (Palindrome.a n (j + 1)).toNat

lemma sqrtTail_pos (hn : ¬IsSquare n) (j : ℕ) : 0 < sqrtTail n j :=
  lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm (Palindrome.fract_alpha_ne_zero n hn j))

lemma sqrtTail_lt_one (j : ℕ) : sqrtTail n j < 1 := Int.fract_lt_one _

lemma one_le_a_succ (hn : ¬IsSquare n) (j : ℕ) : 1 ≤ Palindrome.a n (j + 1) :=
  Palindrome.one_le_quo n (Palindrome.reduced_PQ n hn (by omega))

/-- The continued fraction algorithm, in the form `tower_eq` wants. -/
lemma sqrtTail_rec (hn : ¬IsSquare n) (j : ℕ) :
    (sqrtQuot n j : ℝ) + sqrtTail n (j + 1) = 1 / sqrtTail n j := by
  have hq : ((sqrtQuot n j : ℕ) : ℝ) = (Palindrome.a n (j + 1) : ℝ) := by
    unfold sqrtQuot
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ))
      (Int.toNat_of_nonneg (by linarith [one_le_a_succ hn j]))
  have hfr : sqrtTail n j = Palindrome.alpha n j - (Palindrome.a n j : ℝ) := by
    unfold sqrtTail
    rw [Int.fract, Palindrome.floor_alpha n hn j]
  have h1 : Palindrome.alpha n (j + 1) = 1 / sqrtTail n j := by
    rw [Palindrome.alpha_succ n hn j, hfr, one_div]
  have h2 : (Palindrome.a n (j + 1) : ℝ) + sqrtTail n (j + 1) = Palindrome.alpha n (j + 1) := by
    unfold sqrtTail
    rw [Int.fract, Palindrome.floor_alpha n hn (j + 1)]
    ring
  rw [hq, h2, h1]

/-- Pure periodicity, transported to the tails. -/
lemma sqrtTail_period (hn : ¬IsSquare n) :
    sqrtTail n (Palindrome.period n hn) = sqrtTail n 0 := by
  have hst := Palindrome.state_period n hn
  have hal : Palindrome.alpha n (Palindrome.period n hn)
      = ((Palindrome.a0 n : ℤ) : ℝ) + Real.sqrt n := by
    unfold Palindrome.alpha Palindrome.P Palindrome.Q
    rw [hst]
    norm_num
  unfold sqrtTail
  rw [hal, Palindrome.alpha_zero, Int.fract_intCast_add]

/-- The orbit of the slope never meets `0`, so the two codings agree on it. -/
lemma sqrt_fract_ne_zero (hn : ¬IsSquare n) (k : ℕ) :
    Int.fract (sqrtTail n 0 + (k : ℝ) * sqrtTail n 0) ≠ 0 := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, sqrtTail n 0 = Real.sqrt n - (m : ℝ) :=
    ⟨⌊Real.sqrt n⌋, by unfold sqrtTail; rw [Palindrome.alpha_zero, Int.fract]⟩
  intro h
  rw [Int.fract_eq_zero_iff] at h
  obtain ⟨z, hz⟩ := h
  have hk : ((k : ℤ) + 1 : ℤ) ≠ 0 := by positivity
  have hirr : Irrational ((((k : ℤ) + 1 : ℤ) : ℝ) * Real.sqrt n) :=
    (Palindrome.sqrt_irrational n hn).intCast_mul hk
  have heq : ((((k : ℤ) + 1 : ℤ) : ℝ)) * Real.sqrt n
      = ((z + ((k : ℤ) + 1) * m : ℤ) : ℝ) := by
    rw [hm] at hz
    push_cast at hz ⊢
    linear_combination -hz
  rw [heq] at hirr
  exact (Int.not_irrational _) hirr

/-- **The tower of `√n` returns after `L` derivations.**  For every non-square
`n`, deriving the Sturmian sequence of slope `√n - ⌊√n⌋` exactly `L` times gives
back the sequence with its first letter removed, `L` the period of the continued
fraction of `√n`. -/
theorem sqrt_tower_period (n : ℕ) (hn : ¬IsSquare n) :
    tower (sqrtTail n) (sqrtQuot n) (Palindrome.period n hn)
      = fun k => code (sqrtTail n 0) 0 (k + 1) :=
  tower_period (sqrtTail_rec hn) (sqrtTail_pos hn) (fun j => sqrtTail_lt_one j)
    (Palindrome.period_pos n hn) (sqrtTail_period hn) (sqrt_fract_ne_zero hn)

/-! ## §9 — the same tails instantiate Euler's theorem

`Lagrange.lean` is stated for an abstract tail sequence, so it needs a witness.
The conclusion for `√n` is of course no surprise; the point is that the
hypotheses of `Lagrange.quadratic_of_eventually_periodic` are satisfiable, so
the theorem is not vacuous. -/

lemma one_le_sqrtQuot (hn : ¬IsSquare n) (j : ℕ) : 1 ≤ sqrtQuot n j := by
  have h := one_le_a_succ hn j
  unfold sqrtQuot
  omega

lemma sqrtTail_zero_irrational (hn : ¬IsSquare n) : Irrational (sqrtTail n 0) := by
  have h : sqrtTail n 0 = Real.sqrt n - ((⌊Real.sqrt n⌋ : ℤ) : ℝ) := by
    unfold sqrtTail
    rw [Palindrome.alpha_zero, Int.fract]
  rw [h]
  exact Irrational.sub_intCast (Palindrome.sqrt_irrational n hn) _

/-- Euler's theorem applied to `√n - ⌊√n⌋`, whose continued fraction is purely
periodic by `Palindrome.purely_periodic`. -/
theorem sqrt_quadratic (n : ℕ) (hn : ¬IsSquare n) :
    ∃ A B C : ℤ, A ≠ 0 ∧ (A : ℝ) * sqrtTail n 0 ^ 2 + B * sqrtTail n 0 + C = 0 :=
  Lagrange.quadratic_of_eventually_periodic (m := 0) (L := Palindrome.period n hn)
    (sqrtTail_pos hn) (sqrtTail_rec hn) (one_le_sqrtQuot hn)
    (sqrtTail_zero_irrational hn) (by simpa using sqrtTail_period hn)
    (Palindrome.period_pos n hn)

#print axioms sqrt_tower_period
#print axioms sqrt_quadratic

end Sturmian
