/-
# Euler's half of Lagrange's theorem

§9 of `../all-the-proofs.tex`: if the continued fraction of `α` is eventually
periodic then `α` is a quadratic irrational.  Euler, 1737.

Everything here is stated for an abstract sequence of tails `α : ℕ → ℝ` with
partial quotients `a : ℕ → ℕ` satisfying

    (a j : ℝ) + α (j + 1) = 1 / α j,

the same convention as `Sturmian.tower_eq` and `Sturmian.sqrtTail_rec`.  So this
file needs neither `Palindrome.lean` nor `Sturmian.lean`; `SqrtN.lean` supplies
the `√n` instance, which is what shows the hypotheses are satisfiable.

The converse — every quadratic irrational has an eventually periodic continued
fraction, Lagrange 1770 — is *not* here.  For `√n - ⌊√n⌋` it is
`Palindrome.purely_periodic`; the general case needs the preperiod.
-/
import Mathlib

namespace Lagrange

variable {α : ℕ → ℝ} {a : ℕ → ℕ} {m L : ℕ}

/-- One Möbius step: `z ↦ (0·z + 1)/(1·z + b)`, so that `α j = 1/(a j + α (j+1))`
exhibits `α j` as `N (a j)` applied to `α (j + 1)`. -/
def N (b : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, (b : ℤ)]

/-- The composite of the `L` Möbius steps from level `m` down to level `m + L`. -/
def cfWord (a : ℕ → ℕ) (m : ℕ) : ℕ → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => 1
  | L + 1 => cfWord a m L * N (a (m + L))

lemma cfWord_one (a : ℕ → ℕ) (m : ℕ) : cfWord a m 1 = N (a m) := by
  simp [cfWord]

/-! ### Entries of the product

`!![p, q; r, s] * !![0, 1; 1, b] = !![q, p + q*b; s, r + s*b]`. -/

lemma cfWord_succ_00 (a : ℕ → ℕ) (m L : ℕ) :
    cfWord a m (L + 1) 0 0 = cfWord a m L 0 1 := by
  simp [cfWord, N, Matrix.mul_apply, Fin.sum_univ_two]

lemma cfWord_succ_01 (a : ℕ → ℕ) (m L : ℕ) :
    cfWord a m (L + 1) 0 1 = cfWord a m L 0 0 + cfWord a m L 0 1 * a (m + L) := by
  simp [cfWord, N, Matrix.mul_apply, Fin.sum_univ_two]

lemma cfWord_succ_10 (a : ℕ → ℕ) (m L : ℕ) :
    cfWord a m (L + 1) 1 0 = cfWord a m L 1 1 := by
  simp [cfWord, N, Matrix.mul_apply, Fin.sum_univ_two]

lemma cfWord_succ_11 (a : ℕ → ℕ) (m L : ℕ) :
    cfWord a m (L + 1) 1 1 = cfWord a m L 1 0 + cfWord a m L 1 1 * a (m + L) := by
  simp [cfWord, N, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### The Möbius action

Stated multiplicatively, so no denominator has to be shown nonzero. -/

theorem cfWord_apply (hpos : ∀ j, 0 < α j)
    (hstep : ∀ j, (a j : ℝ) + α (j + 1) = 1 / α j) (m L : ℕ) :
    α m * ((cfWord a m L 1 0 : ℝ) * α (m + L) + (cfWord a m L 1 1 : ℝ))
      = (cfWord a m L 0 0 : ℝ) * α (m + L) + (cfWord a m L 0 1 : ℝ) := by
  induction L with
  | zero =>
      have h : cfWord a m 0 = 1 := rfl
      rw [h]
      simp
  | succ L ih =>
      have hy : α (m + L) * ((a (m + L) : ℝ) + α (m + L + 1)) = 1 := by
        rw [hstep (m + L), mul_one_div, div_self (ne_of_gt (hpos (m + L)))]
      rw [cfWord_succ_00, cfWord_succ_01, cfWord_succ_10, cfWord_succ_11]
      push_cast
      rw [show m + (L + 1) = m + L + 1 from rfl]
      linear_combination ((a (m + L) : ℝ) + α (m + L + 1)) * ih
        - (α m * (cfWord a m L 1 0 : ℝ) - (cfWord a m L 0 0 : ℝ)) * hy

/-! ### The entries grow

The induction is on the shape `(p, q, r, s) ↦ (q, p + q b, s, r + s b)`: the new
bottom-left entry is the old bottom-right one, so once the bottom row is
positive it stays positive. -/

theorem cfWord_entries (ha : ∀ j, 1 ≤ a j) (m : ℕ) :
    ∀ L, 1 ≤ L → 0 ≤ cfWord a m L 0 0 ∧ 0 ≤ cfWord a m L 0 1 ∧
      1 ≤ cfWord a m L 1 0 ∧ 1 ≤ cfWord a m L 1 1 := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base =>
      have hb : (1 : ℤ) ≤ (a m : ℤ) := by exact_mod_cast ha m
      rw [cfWord_one]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [N]
      · simp [N]
      · simp [N]
      · simpa [N] using hb
  | succ L hL ih =>
      obtain ⟨h00, h01, h10, h11⟩ := ih
      have hb : (1 : ℤ) ≤ (a (m + L) : ℤ) := by exact_mod_cast ha (m + L)
      rw [cfWord_succ_00, cfWord_succ_01, cfWord_succ_10, cfWord_succ_11]
      refine ⟨h01, ?_, h11, ?_⟩
      · positivity
      · nlinarith

/-! ### Euler's theorem for the periodic tail -/

/-- **A purely periodic tail is a quadratic irrational.**  The leading
coefficient is positive, so the relation really is quadratic. -/
theorem quadratic_of_periodic (hpos : ∀ j, 0 < α j)
    (hstep : ∀ j, (a j : ℝ) + α (j + 1) = 1 / α j) (ha : ∀ j, 1 ≤ a j)
    (hper : α (m + L) = α m) (hL : 1 ≤ L) :
    ∃ r s t : ℤ, 0 < r ∧ (r : ℝ) * α m ^ 2 + s * α m + t = 0 := by
  obtain ⟨-, -, h10, -⟩ := cfWord_entries ha m L hL
  refine ⟨cfWord a m L 1 0, cfWord a m L 1 1 - cfWord a m L 0 0,
    -(cfWord a m L 0 1), by omega, ?_⟩
  have h := cfWord_apply hpos hstep m L
  rw [hper] at h
  push_cast
  linear_combination h

/-! ### Irrationality propagates down the tails -/

theorem irrational_tail (hstep : ∀ j, (a j : ℝ) + α (j + 1) = 1 / α j)
    (h0 : Irrational (α 0)) : ∀ j, Irrational (α j) := by
  intro j
  induction j with
  | zero => exact h0
  | succ j ih =>
      have h : α (j + 1) = (α j)⁻¹ - (a j : ℤ) := by
        have hs := hstep j
        push_cast
        rw [← one_div (α j)]
        linarith
      rw [h]
      exact Irrational.sub_intCast (irrational_inv_iff.mpr ih) _

/-! ### Euler's theorem

`α 0` is the image of `α m` under a Möbius map with integer coefficients
`!![P, Q; R, S]`, so substituting `α m = (Q - S·α 0)/(R·α 0 - P)` into the
quadratic for `α m` and clearing denominators gives a quadratic for `α 0`.  Its
leading coefficient is the value of the form `(r,s,t)` at the *rational* point
`-S/R`, which is nonzero because the roots of `(r,s,t)` are `α m` and its
conjugate, and neither is rational. -/

/-- **Euler, 1737.**  If the continued fraction of `α 0` is eventually periodic
then `α 0` is a quadratic irrational. -/
theorem quadratic_of_eventually_periodic (hpos : ∀ j, 0 < α j)
    (hstep : ∀ j, (a j : ℝ) + α (j + 1) = 1 / α j) (ha : ∀ j, 1 ≤ a j)
    (h0 : Irrational (α 0)) (hper : α (m + L) = α m) (hL : 1 ≤ L) :
    ∃ A B C : ℤ, A ≠ 0 ∧ (A : ℝ) * α 0 ^ 2 + B * α 0 + C = 0 := by
  obtain ⟨r, s, t, hr, hq⟩ := quadratic_of_periodic hpos hstep ha hper hL
  have hirr := irrational_tail hstep h0 m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨r, s, t, by omega, hq⟩
  obtain ⟨-, -, hR, -⟩ := cfWord_entries ha 0 m hm
  set P : ℤ := cfWord a 0 m 0 0 with hP
  set Q : ℤ := cfWord a 0 m 0 1 with hQ
  set R : ℤ := cfWord a 0 m 1 0 with hRdef
  set S : ℤ := cfWord a 0 m 1 1 with hS
  have hmob : α 0 * ((R : ℝ) * α m + (S : ℝ)) = (P : ℝ) * α m + (Q : ℝ) := by
    simpa using cfWord_apply hpos hstep 0 m
  have hm' : α m * ((R : ℝ) * α 0 - (P : ℝ)) = (Q : ℝ) - (S : ℝ) * α 0 := by
    linarith [hmob]
  have hR0 : (R : ℝ) ≠ 0 := by
    have h : (0 : ℤ) < R := by omega
    exact_mod_cast h.ne'
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  refine ⟨r * S ^ 2 - s * S * R + t * R ^ 2,
    -(2 * r * Q * S) + s * (Q * R + S * P) - 2 * t * R * P,
    r * Q ^ 2 - s * Q * P + t * P ^ 2, ?_, ?_⟩
  · intro hA
    have hA' : (r : ℝ) * (S : ℝ) ^ 2 - (s : ℝ) * (S : ℝ) * (R : ℝ)
        + (t : ℝ) * (R : ℝ) ^ 2 = 0 := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hA
    have hk : (r : ℝ) * (-(S : ℝ) / (R : ℝ)) ^ 2 + (s : ℝ) * (-(S : ℝ) / (R : ℝ))
        + (t : ℝ) = 0 := by
      field_simp
      linarith [hA']
    have hfac : (α m - -(S : ℝ) / (R : ℝ))
        * ((r : ℝ) * (α m + -(S : ℝ) / (R : ℝ)) + (s : ℝ)) = 0 := by
      linear_combination hq - hk
    rcases mul_eq_zero.mp hfac with h | h
    · refine hirr.ne_rational (-S) R ?_
      push_cast
      linarith [h]
    · refine hirr.ne_rational (S * r - s * R) (R * r) ?_
      field_simp at h ⊢
      push_cast
      linarith [h]
  · push_cast
    linear_combination ((R : ℝ) * α 0 - (P : ℝ)) ^ 2 * hq
      - ((r : ℝ) * (((Q : ℝ) - (S : ℝ) * α 0) + α m * ((R : ℝ) * α 0 - (P : ℝ)))
          + (s : ℝ) * ((R : ℝ) * α 0 - (P : ℝ))) * hm'

/-! ### A concrete check

For the purely periodic continued fraction `[1;1,1,…]` the theorem's
coefficients are `(r,s,t) = (1,1,-1)`, i.e. `x² + x - 1 = 0` — the equation of
`1/φ` derived in §7 of `../all-the-proofs.tex`. -/

example : (cfWord (fun _ => 1) 0 1 1 0, cfWord (fun _ => 1) 0 1 1 1 - cfWord (fun _ => 1) 0 1 0 0,
    -(cfWord (fun _ => 1) 0 1 0 1)) = ((1 : ℤ), (1 : ℤ), (-1 : ℤ)) := by
  simp [cfWord_one, N]

#print axioms cfWord_apply
#print axioms quadratic_of_periodic
#print axioms quadratic_of_eventually_periodic

end Lagrange
