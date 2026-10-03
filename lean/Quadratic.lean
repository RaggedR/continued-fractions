import Palindrome

namespace Quadratic

open Palindrome (a0 Reduced)

variable {n : ℕ} {P Q : ℤ}

/-! ## §1 A general quadratic irrational

`Palindrome.lean` fixes the start of the recurrence at `(P₀, Q₀) = (0, 1)`,
which is `√n`.  Almost nothing else there is specific to that start: `quo`,
`step`, `unstep`, `Reduced`, `finite_reduced`, `step_mapsTo`, `step_injOn` are
all statements about the *discriminant* `n` and an arbitrary state.  So the
general case is an extension, not a rewrite.

One thing does have to change.  `Palindrome.quo n P Q = (a₀ + P) / Q` is
`⌊(P + √n)/Q⌋` only when `Q > 0`, and for `√n` that is automatic
(`Q_pos_all`).  For a general quadratic irrational the `Q`s genuinely change
sign — and the sign is the whole story, since

    α_k · α̅_k = -Q_{k-1}/Q_k,

so `α̅_k < 0` exactly when `Q_{k-1}` and `Q_k` have the *same* sign.  That is
Lagrange's criterion, *Additions* (1770) art. 41: "lorsque dans la série des
nombres E, E₁, E₂,… on en trouvera deux consécutifs de même signe, celui des
deux qui sera moindre que √B sera déjà nécessairement périodique." -/

/-- An **admissible** state: `Q ≠ 0` and `Q ∣ n - P²`, so that `(P + √n)/Q`
has `(P' , Q')` integral after a step. -/
structure Adm (n : ℕ) (s : ℤ × ℤ) : Prop where
  Q_ne : s.2 ≠ 0
  dvd : s.2 ∣ (n : ℤ) - s.1 ^ 2

/-- The partial quotient `⌊(P + √n)/Q⌋`, for either sign of `Q`.

For `Q < 0` write `α = -(P + √n)/(-Q)`; since `√n` is irrational `α ∉ ℤ`, so
`⌊α⌋ = -⌊(P + √n)/(-Q)⌋ - 1`, and the inner floor is the `Q > 0` case. -/
def quo (n : ℕ) (P Q : ℤ) : ℤ :=
  if 0 < Q then Palindrome.quo n P Q else -(Palindrome.quo n P (-Q)) - 1

lemma quo_of_pos (hQ : 0 < Q) : quo n P Q = Palindrome.quo n P Q := if_pos hQ

/-- One step of the algorithm, valid for either sign of `Q`. -/
def step (n : ℕ) (s : ℤ × ℤ) : ℤ × ℤ :=
  let p := quo n s.1 s.2 * s.2 - s.1
  (p, ((n : ℤ) - p ^ 2) / s.2)

lemma step_of_pos {s : ℤ × ℤ} (hQ : 0 < s.2) : step n s = Palindrome.step n s := by
  simp only [step, Palindrome.step, quo_of_pos hQ]

/-! ### Admissibility is preserved

This is the general form of `Palindrome.sub_P_succ_sq`: shifting `P` by a
multiple of `Q` does not change `n - P²` modulo `Q`. -/

lemma dvd_sub_sq (n : ℕ) {P Q : ℤ} (h : Q ∣ (n : ℤ) - P ^ 2) (a : ℤ) :
    Q ∣ (n : ℤ) - (a * Q - P) ^ 2 := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c - (a ^ 2 * Q - 2 * a * P), by linear_combination hc⟩

lemma adm_step (n : ℕ) (hn : ¬IsSquare n) {s : ℤ × ℤ} (h : Adm n s) :
    Adm n (step n s) := by
  obtain ⟨hQ, hdvd⟩ := h
  have hd : s.2 ∣ (n : ℤ) - (quo n s.1 s.2 * s.2 - s.1) ^ 2 := dvd_sub_sq n hdvd _
  obtain ⟨c, hc⟩ := hd
  constructor
  · show ((n : ℤ) - (quo n s.1 s.2 * s.2 - s.1) ^ 2) / s.2 ≠ 0
    rw [hc, Int.mul_ediv_cancel_left _ hQ]
    intro h0
    exact Palindrome.sub_sq_ne_zero n hn _ (by rw [hc, h0, mul_zero])
  · show ((n : ℤ) - (quo n s.1 s.2 * s.2 - s.1) ^ 2) / s.2
      ∣ (n : ℤ) - (quo n s.1 s.2 * s.2 - s.1) ^ 2
    rw [hc, Int.mul_ediv_cancel_left _ hQ]
    exact Dvd.intro_left _ rfl

lemma adm_iterate (n : ℕ) (hn : ¬IsSquare n) {s : ℤ × ℤ} (h : Adm n s) (k : ℕ) :
    Adm n ((step n)^[k] s) := by
  induction k with
  | zero => exact h
  | succ k ih => rw [Function.iterate_succ_apply']; exact adm_step n hn ih

/-! ### The surd, and that `quo` really is its floor -/

/-- The real number `(P + √n)/Q`. -/
noncomputable def surd (n : ℕ) (s : ℤ × ℤ) : ℝ :=
  ((s.1 : ℝ) + Real.sqrt n) / (s.2 : ℝ)

lemma surd_irrational (n : ℕ) (hn : ¬IsSquare n) {s : ℤ × ℤ} (hQ : s.2 ≠ 0) :
    Irrational (surd n s) := by
  have hQR : ((s.2 : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hQ
  have h := ((Palindrome.sqrt_irrational n hn).intCast_add s.1).intCast_div hQ
  simpa [surd, div_eq_iff hQR] using h

/-- `⌊(P + √n)/Q⌋ = ⌊(a₀ + P)/Q⌋` for `Q > 0` — `Palindrome.floor_alpha` with
the orbit hypothesis removed. -/
lemma floor_surd_of_pos (n : ℕ) {s : ℤ × ℤ} (hQ : 0 < s.2) :
    ⌊surd n s⌋ = Palindrome.quo n s.1 s.2 := by
  have hQR : (0 : ℝ) < (s.2 : ℝ) := by exact_mod_cast hQ
  have hdm : s.2 * Palindrome.quo n s.1 s.2 + (a0 n + s.1) % s.2 = a0 n + s.1 := by
    rw [Palindrome.quo]; exact Int.mul_ediv_add_emod _ _
  have hr0 : 0 ≤ (a0 n + s.1) % s.2 := Int.emod_nonneg _ hQ.ne'
  have hr1 : (a0 n + s.1) % s.2 < s.2 := Int.emod_lt_of_pos _ hQ
  have h1 : Palindrome.quo n s.1 s.2 * s.2 ≤ a0 n + s.1 := by nlinarith
  have h2 : a0 n + s.1 + 1 ≤ (Palindrome.quo n s.1 s.2 + 1) * s.2 := by nlinarith
  have h1R : (Palindrome.quo n s.1 s.2 : ℝ) * (s.2 : ℝ) ≤ (a0 n : ℝ) + (s.1 : ℝ) := by
    exact_mod_cast h1
  have h2R : (a0 n : ℝ) + (s.1 : ℝ) + 1
      ≤ ((Palindrome.quo n s.1 s.2 : ℝ) + 1) * (s.2 : ℝ) := by exact_mod_cast h2
  rw [surd, Int.floor_eq_iff, le_div_iff₀ hQR, div_lt_iff₀ hQR]
  exact ⟨by nlinarith [Palindrome.a0_le_sqrt n], by nlinarith [Palindrome.sqrt_lt_a0_succ n]⟩

/-- A surd is never an integer, so `⌈·⌉ = ⌊·⌋ + 1`. -/
lemma fract_surd_ne_zero (n : ℕ) (hn : ¬IsSquare n) {s : ℤ × ℤ} (hQ : s.2 ≠ 0) :
    Int.fract (surd n s) ≠ 0 := by
  intro h
  have hz : ((⌊surd n s⌋ : ℤ) : ℝ) = surd n s := by
    have h2 := Int.floor_add_fract (surd n s)
    rw [h] at h2
    linarith
  exact surd_irrational n hn hQ ⟨((⌊surd n s⌋ : ℤ) : ℚ), by push_cast; exact hz⟩

lemma ceil_eq_floor_succ {x : ℝ} (h : Int.fract x ≠ 0) : ⌈x⌉ = ⌊x⌋ + 1 := by
  have hne : (⌊x⌋ : ℝ) ≠ x := by
    intro he
    rw [Int.fract, ← he] at h
    simp at h
  have h1 : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne (Int.floor_le x) hne
  rw [Int.ceil_eq_iff]
  push_cast
  exact ⟨by linarith, by linarith [Int.lt_floor_add_one x]⟩

/-- **`quo` is the floor of the surd**, for either sign of `Q`. -/
theorem floor_surd (n : ℕ) (hn : ¬IsSquare n) {s : ℤ × ℤ} (hQ : s.2 ≠ 0) :
    ⌊surd n s⌋ = quo n s.1 s.2 := by
  rcases lt_or_gt_of_ne hQ with hneg | hpos
  · have hQ' : (0 : ℤ) < (s.1, -s.2).2 := by simpa using by omega
    have hQ'ne : ((s.1, -s.2) : ℤ × ℤ).2 ≠ 0 := by simpa using by omega
    have hflip : surd n s = -surd n (s.1, -s.2) := by
      have h : ((-s.2 : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
      simp only [surd]
      push_cast
      field_simp
    rw [hflip, Int.floor_neg, ceil_eq_floor_succ (fract_surd_ne_zero n hn hQ'ne),
      floor_surd_of_pos n hQ', quo, if_neg (by omega)]
    show -(Palindrome.quo n s.1 (-s.2) + 1) = -Palindrome.quo n s.1 (-s.2) - 1
    ring
  · rw [floor_surd_of_pos n hpos, quo_of_pos hpos]

/-! ### The step on the surd

The generalisation of `Palindrome.alpha_succ`: `step` really is one step of the
continued-fraction algorithm, for either sign of `Q`. -/

lemma QQ_step (n : ℕ) {s : ℤ × ℤ} (h : Adm n s) :
    s.2 * (step n s).2 = (n : ℤ) - (step n s).1 ^ 2 := by
  obtain ⟨c, hc⟩ := dvd_sub_sq n h.dvd (quo n s.1 s.2)
  show s.2 * (((n : ℤ) - (quo n s.1 s.2 * s.2 - s.1) ^ 2) / s.2)
    = (n : ℤ) - (quo n s.1 s.2 * s.2 - s.1) ^ 2
  rw [hc, Int.mul_ediv_cancel_left _ h.Q_ne]

lemma surd_step (n : ℕ) (hn : ¬IsSquare n) {s : ℤ × ℤ} (h : Adm n s) :
    surd n (step n s) = (surd n s - (quo n s.1 s.2 : ℝ))⁻¹ := by
  have hQ : ((s.2 : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr h.Q_ne
  have hQ' : (((step n s).2 : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr (adm_step n hn h).Q_ne
  have hsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hP'Z : (step n s).1 = quo n s.1 s.2 * s.2 - s.1 := rfl
  have hP' : ((step n s).1 : ℝ) = (quo n s.1 s.2 : ℝ) * (s.2 : ℝ) - (s.1 : ℝ) := by
    rw [hP'Z]; push_cast; ring
  have hQQ : (s.2 : ℝ) * ((step n s).2 : ℝ) = (n : ℝ) - ((step n s).1 : ℝ) ^ 2 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (QQ_step n h)
  have hne : Real.sqrt n - ((step n s).1 : ℝ) ≠ 0 := by
    intro h0
    exact Palindrome.sqrt_irrational n hn ⟨(((step n s).1 : ℤ) : ℚ), by push_cast; linarith⟩
  have key : surd n s - (quo n s.1 s.2 : ℝ)
      = (Real.sqrt n - ((step n s).1 : ℝ)) / (s.2 : ℝ) := by
    rw [surd, hP']
    field_simp
    ring
  rw [key, inv_div, surd, div_eq_div_iff hQ' hne]
  nlinarith [hsq, hQQ]

/-! ## §2 Pure periodicity once the orbit is reduced

Nothing new is needed here: `Palindrome.step_mapsTo`, `step_injOn` and
`finite_reduced` are already statements about an arbitrary state, and on a
reduced state `step = Palindrome.step` because `Q > 0`. -/

lemma reduced_iterate (n : ℕ) (hn : ¬IsSquare n) {t : ℤ × ℤ} (ht : Reduced n t.1 t.2) (j : ℕ) :
    Reduced n ((Palindrome.step n)^[j] t).1 ((Palindrome.step n)^[j] t).2 := by
  induction j with
  | zero => exact ht
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact Palindrome.step_mapsTo n hn ih

lemma iterate_eq_palindrome (n : ℕ) (hn : ¬IsSquare n) {t : ℤ × ℤ}
    (ht : Reduced n t.1 t.2) (j : ℕ) : (step n)^[j] t = (Palindrome.step n)^[j] t := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        step_of_pos (reduced_iterate n hn ht j).Q_pos]

/-- **Eventual periodicity, given that the orbit reaches a reduced state.**

Once reduced, the orbit is *purely* periodic, by the same pigeonhole as
`Palindrome.purely_periodic`: the reduced set is finite, forward-invariant, and
`step` is injective on it. -/
theorem eventually_periodic_of_reduced (n : ℕ) (hn : ¬IsSquare n) {s₀ : ℤ × ℤ} {m : ℕ}
    (hm : Reduced n ((step n)^[m] s₀).1 ((step n)^[m] s₀).2) :
    ∃ L : ℕ, 0 < L ∧ ∀ k, m ≤ k → (step n)^[k + L] s₀ = (step n)^[k] s₀ := by
  obtain ⟨L, hL, hfix⟩ := Palindrome.exists_iterate_eq_self (Palindrome.finite_reduced n)
    (Palindrome.step_mapsTo n hn) (Palindrome.step_injOn n hn)
    (show (step n)^[m] s₀ ∈ {x : ℤ × ℤ | Reduced n x.1 x.2} from hm)
  refine ⟨L, hL, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, by omega⟩
  have e1 : (step n)^[m + j] s₀ = (Palindrome.step n)^[j] ((step n)^[m] s₀) := by
    rw [show m + j = j + m from by omega, Function.iterate_add_apply,
      iterate_eq_palindrome n hn hm j]
  have e2 : (step n)^[m + j + L] s₀
      = (Palindrome.step n)^[j + L] ((step n)^[m] s₀) := by
    rw [show m + j + L = (j + L) + m from by omega, Function.iterate_add_apply,
      iterate_eq_palindrome n hn hm (j + L)]
  rw [e1, e2, Function.iterate_add_apply, hfix]

/-! ## §3 The preperiod

The one genuinely new theorem: the orbit of *any* admissible state reaches a
reduced one.  For `√n` this was free, because `Palindrome.reduced_state` shows
the state is reduced from index 1 on.

The textbook proof goes through the convergents `pₖ/qₖ`, the bound
`|α - pₖ/qₖ| < 1/qₖ²`, and either the invariance of the discriminant of
`Aₖx² + Bₖx + Cₖ` or the uniqueness of the continued-fraction expansion.  None
of that is needed.  Suppose the orbit is never reduced.  Then `α̅ₖ > 0` for every
`k ≥ 1` — because `α̅ₖ < 0` would force `α̅ₖ₊₁ ∈ (-1,0)`, and that *is* reduced.
Positivity makes `α̅ₖ > aₖ ≥ 1`, so `αₖ` and `α̅ₖ` both exceed `1` from index 1
on, and the identity

    αₖ₊₁ - α̅ₖ₊₁ = (α̅ₖ - αₖ) · αₖ₊₁ α̅ₖ₊₁

then makes the gap `|αₖ - α̅ₖ| = 2√n/|Qₖ|` strictly *increasing*.  So `|Qₖ|` is a
strictly decreasing sequence of positive integers: infinite descent. -/

/-- The conjugate surd `(P - √n)/Q`. -/
noncomputable def conj (n : ℕ) (s : ℤ × ℤ) : ℝ :=
  ((s.1 : ℝ) - Real.sqrt n) / (s.2 : ℝ)

lemma sqrt_pos_of_not_square (n : ℕ) (hn : ¬IsSquare n) : 0 < Real.sqrt n := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn ⟨0, by norm_num⟩
  exact Real.sqrt_pos.mpr (by positivity)

lemma conj_ne_zero (n : ℕ) (hn : ¬IsSquare n) {s : ℤ × ℤ} (hQ : s.2 ≠ 0) :
    conj n s ≠ 0 := by
  have hQR : ((s.2 : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hQ
  rw [conj, div_ne_zero_iff]
  refine ⟨fun h => ?_, hQR⟩
  exact Palindrome.sqrt_irrational n hn ⟨((s.1 : ℤ) : ℚ), by push_cast; linarith⟩

lemma conj_step (n : ℕ) (hn : ¬IsSquare n) {s : ℤ × ℤ} (h : Adm n s) :
    conj n (step n s) = (conj n s - (quo n s.1 s.2 : ℝ))⁻¹ := by
  have hQ : ((s.2 : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr h.Q_ne
  have hQ' : (((step n s).2 : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr (adm_step n hn h).Q_ne
  have hsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hP'Z : (step n s).1 = quo n s.1 s.2 * s.2 - s.1 := rfl
  have hP' : ((step n s).1 : ℝ) = (quo n s.1 s.2 : ℝ) * (s.2 : ℝ) - (s.1 : ℝ) := by
    rw [hP'Z]; push_cast; ring
  have hQQ : (s.2 : ℝ) * ((step n s).2 : ℝ) = (n : ℝ) - ((step n s).1 : ℝ) ^ 2 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (QQ_step n h)
  have hne : Real.sqrt n + ((step n s).1 : ℝ) ≠ 0 := by
    intro h0
    exact Palindrome.sqrt_irrational n hn ⟨((-(step n s).1 : ℤ) : ℚ), by push_cast; linarith⟩
  have key : conj n s - (quo n s.1 s.2 : ℝ)
      = -(Real.sqrt n + ((step n s).1 : ℝ)) / (s.2 : ℝ) := by
    rw [conj, hP']
    field_simp
    ring
  rw [key, inv_div, conj, div_eq_div_iff hQ' (by intro h0; exact hne (by linarith))]
  nlinarith [hsq, hQQ]

lemma surd_sub_conj (n : ℕ) (s : ℤ × ℤ) :
    surd n s - conj n s = 2 * Real.sqrt n / (s.2 : ℝ) := by
  rw [surd, conj, div_sub_div_same]
  ring_nf

lemma abs_surd_sub_conj (n : ℕ) (s : ℤ × ℤ) :
    |surd n s - conj n s| = 2 * Real.sqrt n / |(s.2 : ℝ)| := by
  rw [surd_sub_conj, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.sqrt n)]

lemma one_lt_surd_step (n : ℕ) (hn : ¬IsSquare n) {s : ℤ × ℤ} (h : Adm n s) :
    1 < surd n (step n s) := by
  have hfr := fract_surd_ne_zero n hn h.Q_ne
  have h0 : 0 < Int.fract (surd n s) :=
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hfr)
  have h1 : Int.fract (surd n s) < 1 := Int.fract_lt_one _
  have heq : surd n s - (quo n s.1 s.2 : ℝ) = Int.fract (surd n s) := by
    rw [Int.fract, floor_surd n hn h.Q_ne]
  rw [surd_step n hn h, heq]
  have h2 : Int.fract (surd n s) * (Int.fract (surd n s))⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt h0)
  nlinarith [h2]

lemma one_le_quo_of_one_lt (n : ℕ) (hn : ¬IsSquare n) {s : ℤ × ℤ} (hQ : s.2 ≠ 0)
    (h : 1 < surd n s) : 1 ≤ quo n s.1 s.2 := by
  rw [← floor_surd n hn hQ, Int.le_floor]
  push_cast
  linarith

lemma inv_neg_of_neg' {x : ℝ} (h : x < 0) : x⁻¹ < 0 := by
  have h1 : x * x⁻¹ = 1 := mul_inv_cancel₀ (ne_of_lt h)
  nlinarith [h1]

/-- The real conditions `α > 1` and `-1 < α̅ < 0` are `Palindrome.Reduced`. -/
lemma reduced_of_conj_neg (n : ℕ) (hn : ¬IsSquare n) {s : ℤ × ℤ} (h : Adm n s)
    (h1 : 1 < surd n s) (h2 : -1 < conj n s) (h3 : conj n s < 0) :
    Reduced n s.1 s.2 := by
  have hs0 := sqrt_pos_of_not_square n hn
  have hlo := Palindrome.a0_le_sqrt n
  have hhi := Palindrome.sqrt_lt_a0_succ n
  have hQpos : (0 : ℤ) < s.2 := by
    by_contra hcon
    have hQneg : ((s.2 : ℝ)) < 0 := by
      have hz : s.2 < 0 := by have := h.Q_ne; omega
      exact_mod_cast hz
    have hp : 0 < surd n s := by linarith
    rw [surd, div_pos_iff] at hp
    have hnum : (s.1 : ℝ) + Real.sqrt n < 0 := by
      rcases hp with ⟨_, h2'⟩ | ⟨h1', _⟩
      · linarith
      · exact h1'
    have hcpos : 0 < conj n s := by
      rw [conj, div_pos_iff]
      exact Or.inr ⟨by linarith, hQneg⟩
    linarith
  have hQR : (0 : ℝ) < (s.2 : ℝ) := by exact_mod_cast hQpos
  have hB : (s.2 : ℝ) < (s.1 : ℝ) + Real.sqrt n := by
    have := h1; rw [surd] at this; exact (one_lt_div hQR).mp this
  have hA : -(s.2 : ℝ) < (s.1 : ℝ) - Real.sqrt n := by
    have h2' := h2
    rw [conj, neg_lt, ← neg_div] at h2'
    have := (div_lt_one hQR).mp h2'
    linarith
  have hC : (s.1 : ℝ) - Real.sqrt n < 0 := by
    have h3' := h3
    rw [conj, div_neg_iff] at h3'
    rcases h3' with ⟨_, hq⟩ | ⟨hp, _⟩
    · linarith
    · exact hp
  refine ⟨hQpos, ?_, ?_, ?_, h.dvd⟩
  · have hr : (s.1 : ℝ) < (a0 n : ℝ) + 1 := by linarith
    have : s.1 < a0 n + 1 := by exact_mod_cast hr
    omega
  · have hr : (a0 n : ℝ) < (s.1 : ℝ) + (s.2 : ℝ) := by linarith
    have : a0 n < s.1 + s.2 := by exact_mod_cast hr
    omega
  · have hr : (s.2 : ℝ) - (s.1 : ℝ) < (a0 n : ℝ) + 1 := by linarith
    have : s.2 - s.1 < a0 n + 1 := by exact_mod_cast hr
    omega

lemma neg_one_lt_inv {x : ℝ} (h : x < -1) : -1 < x⁻¹ := by
  have h1 : x * x⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
  nlinarith [h1]

/-- **The preperiod.**  The orbit of any admissible state reaches a reduced one. -/
theorem exists_reduced (n : ℕ) (hn : ¬IsSquare n) {s₀ : ℤ × ℤ} (h₀ : Adm n s₀) :
    ∃ m : ℕ, Reduced n ((step n)^[m] s₀).1 ((step n)^[m] s₀).2 := by
  by_contra hc
  push Not at hc
  have hadm : ∀ k, Adm n ((step n)^[k] s₀) := fun k => adm_iterate n hn h₀ k
  have hsucc : ∀ k, (step n)^[k + 1] s₀ = step n ((step n)^[k] s₀) :=
    fun k => Function.iterate_succ_apply' _ _ _
  have hsurd1 : ∀ k, 1 < surd n ((step n)^[k + 1] s₀) := by
    intro k; rw [hsucc]; exact one_lt_surd_step n hn (hadm k)
  have hquo1 : ∀ k, 1 ≤ quo n ((step n)^[k + 1] s₀).1 ((step n)^[k + 1] s₀).2 := fun k =>
    one_le_quo_of_one_lt n hn (hadm (k + 1)).Q_ne (hsurd1 k)
  have hcstep : ∀ k, conj n ((step n)^[k + 1] s₀)
      = (conj n ((step n)^[k] s₀) - (quo n ((step n)^[k] s₀).1 ((step n)^[k] s₀).2 : ℝ))⁻¹ := by
    intro k; rw [hsucc]; exact conj_step n hn (hadm k)
  -- the conjugate is positive from index 1 on
  have hpos : ∀ k, 0 < conj n ((step n)^[k + 1] s₀) := by
    intro k
    rcases lt_trichotomy (conj n ((step n)^[k + 1] s₀)) 0 with h | h | h
    · exfalso
      have hq : (1 : ℝ) ≤ (quo n ((step n)^[k + 1] s₀).1 ((step n)^[k + 1] s₀).2 : ℝ) := by
        exact_mod_cast hquo1 k
      have hd : conj n ((step n)^[k + 1] s₀)
          - (quo n ((step n)^[k + 1] s₀).1 ((step n)^[k + 1] s₀).2 : ℝ) < -1 := by linarith
      refine hc (k + 1 + 1) (reduced_of_conj_neg n hn (hadm (k + 1 + 1)) (hsurd1 (k + 1)) ?_ ?_)
      · rw [hcstep (k + 1)]; exact neg_one_lt_inv hd
      · rw [hcstep (k + 1)]; exact inv_neg_of_neg' (by linarith)
    · exact absurd h (conj_ne_zero n hn (hadm (k + 1)).Q_ne)
    · exact h
  -- hence both the surd and its conjugate exceed 1 from index 1 on
  have hconj1 : ∀ k, 1 < conj n ((step n)^[k + 1] s₀) := by
    intro k
    have h := hpos (k + 1)
    rw [hcstep (k + 1)] at h
    have hq : (1 : ℝ) ≤ (quo n ((step n)^[k + 1] s₀).1 ((step n)^[k + 1] s₀).2 : ℝ) := by
      exact_mod_cast hquo1 k
    rcases lt_trichotomy (conj n ((step n)^[k + 1] s₀)
        - (quo n ((step n)^[k + 1] s₀).1 ((step n)^[k + 1] s₀).2 : ℝ)) 0 with hd | hd | hd
    · exact absurd h (not_lt.mpr (le_of_lt (inv_neg_of_neg' hd)))
    · rw [hd] at h; simp at h
    · linarith
  -- the gap grows, so |Q| descends
  have hdec : ∀ k, ((step n)^[k + 1 + 1] s₀).2.natAbs < ((step n)^[k + 1] s₀).2.natAbs := by
    intro k
    set u := surd n ((step n)^[k + 1] s₀) with hu
    set v := conj n ((step n)^[k + 1] s₀) with hv
    set a := (quo n ((step n)^[k + 1] s₀).1 ((step n)^[k + 1] s₀).2 : ℝ) with ha
    have hua : u - a = Int.fract u := by
      rw [hu, ha, Int.fract, floor_surd n hn (hadm (k + 1)).Q_ne]
    have hfr := fract_surd_ne_zero n hn (hadm (k + 1)).Q_ne
    have hua0 : 0 < u - a := by
      rw [hua]; exact lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hfr)
    have hq1 : (1 : ℝ) ≤ a := by rw [ha]; exact_mod_cast hquo1 k
    have hva0 : 0 < v - a := by
      have h := hpos (k + 1)
      rw [hcstep (k + 1)] at h
      rcases lt_trichotomy (v - a) 0 with hd | hd | hd
      · exact absurd h (not_lt.mpr (le_of_lt (inv_neg_of_neg' hd)))
      · rw [hv, ha] at hd; rw [hd] at h; simp at h
      · exact hd
    have hu' : surd n ((step n)^[k + 1 + 1] s₀) = (u - a)⁻¹ := by
      rw [hsucc, hu, ha]; exact surd_step n hn (hadm (k + 1))
    have hv' : conj n ((step n)^[k + 1 + 1] s₀) = (v - a)⁻¹ := by
      rw [hsucc, hv, ha]; exact conj_step n hn (hadm (k + 1))
    have hU : 1 < surd n ((step n)^[k + 1 + 1] s₀) := hsurd1 (k + 1)
    have hV : 1 < conj n ((step n)^[k + 1 + 1] s₀) := hconj1 (k + 1)
    have hid : surd n ((step n)^[k + 1 + 1] s₀) - conj n ((step n)^[k + 1 + 1] s₀)
        = (v - u) * (surd n ((step n)^[k + 1 + 1] s₀) * conj n ((step n)^[k + 1 + 1] s₀)) := by
      rw [hu', hv']
      field_simp
      ring
    have hne : (0 : ℝ) < |u - v| := by
      rw [abs_pos, sub_ne_zero, hu, hv]
      intro heq
      have hg0 := abs_surd_sub_conj n ((step n)^[k + 1] s₀)
      rw [heq, sub_self, abs_zero, eq_comm, div_eq_zero_iff] at hg0
      have hs0 := sqrt_pos_of_not_square n hn
      have hQ : (0 : ℝ) < |((((step n)^[k + 1] s₀).2 : ℤ) : ℝ)| := by
        rw [abs_pos]; exact Int.cast_ne_zero.mpr (hadm (k + 1)).Q_ne
      rcases hg0 with h' | h'
      · linarith
      · linarith
    have hUV : (1 : ℝ) < surd n ((step n)^[k + 1 + 1] s₀)
        * conj n ((step n)^[k + 1 + 1] s₀) := by nlinarith [hU, hV]
    have hgap : |u - v| < |surd n ((step n)^[k + 1 + 1] s₀)
        - conj n ((step n)^[k + 1 + 1] s₀)| := by
      rw [hid, abs_mul, abs_sub_comm v u,
        abs_of_pos (by linarith : (0:ℝ) < surd n ((step n)^[k + 1 + 1] s₀)
          * conj n ((step n)^[k + 1 + 1] s₀))]
      exact (lt_mul_iff_one_lt_right hne).mpr hUV
    rw [hu, hv] at hgap
    rw [abs_surd_sub_conj, abs_surd_sub_conj] at hgap
    have hs0 := sqrt_pos_of_not_square n hn
    have hA : (0 : ℝ) < |((((step n)^[k + 1] s₀).2 : ℤ) : ℝ)| := by
      rw [abs_pos]; exact Int.cast_ne_zero.mpr (hadm (k + 1)).Q_ne
    have hB : (0 : ℝ) < |((((step n)^[k + 1 + 1] s₀).2 : ℤ) : ℝ)| := by
      rw [abs_pos]; exact Int.cast_ne_zero.mpr (hadm (k + 1 + 1)).Q_ne
    have hlt : |((((step n)^[k + 1 + 1] s₀).2 : ℤ) : ℝ)|
        < |((((step n)^[k + 1] s₀).2 : ℤ) : ℝ)| := by
      have e1 : 2 * Real.sqrt n / |((((step n)^[k + 1] s₀).2 : ℤ) : ℝ)|
          * |((((step n)^[k + 1] s₀).2 : ℤ) : ℝ)| = 2 * Real.sqrt n :=
        div_mul_cancel₀ _ (ne_of_gt hA)
      have e2 : 2 * Real.sqrt n / |((((step n)^[k + 1 + 1] s₀).2 : ℤ) : ℝ)|
          * |((((step n)^[k + 1 + 1] s₀).2 : ℤ) : ℝ)| = 2 * Real.sqrt n :=
        div_mul_cancel₀ _ (ne_of_gt hB)
      have hX : (0 : ℝ) < 2 * Real.sqrt n / |((((step n)^[k + 1] s₀).2 : ℤ) : ℝ)| :=
        div_pos (by linarith) hA
      nlinarith [hgap, e1, e2, hX, hA, hB]
    have hcast : ∀ z : ℤ, |((z : ℤ) : ℝ)| = (z.natAbs : ℝ) := by
      intro z; rw [← Int.cast_abs]; exact (Nat.cast_natAbs (α := ℝ) z).symm
    rw [hcast, hcast] at hlt
    exact_mod_cast hlt
  -- infinite descent
  have hbound : ∀ j, ((step n)^[j + 1] s₀).2.natAbs + j
      ≤ ((step n)^[0 + 1] s₀).2.natAbs := by
    intro j
    induction j with
    | zero => omega
    | succ j ih => have := hdec j; omega
  have hge : 1 ≤ ((step n)^[((step n)^[0 + 1] s₀).2.natAbs + 1] s₀).2.natAbs := by
    have := (hadm (((step n)^[0 + 1] s₀).2.natAbs + 1)).Q_ne
    omega
  have := hbound ((step n)^[0 + 1] s₀).2.natAbs
  omega

/-- **Lagrange, 1770.**  The continued fraction of every quadratic irrational
`(P + √n)/Q` is eventually periodic. -/
theorem eventually_periodic (n : ℕ) (hn : ¬IsSquare n) {s₀ : ℤ × ℤ} (h₀ : Adm n s₀) :
    ∃ m L : ℕ, 0 < L ∧ ∀ k, m ≤ k → (step n)^[k + L] s₀ = (step n)^[k] s₀ := by
  obtain ⟨m, hm⟩ := exists_reduced n hn h₀
  obtain ⟨L, hL, hper⟩ := eventually_periodic_of_reduced n hn hm
  exact ⟨m, L, hL, hper⟩

/-! ## §4 Two instances

`eventually_periodic` is stated for an abstract admissible state, so it needs
witnesses or it could be vacuous. -/

lemma adm_sqrt (n : ℕ) : Adm n (0, 1) := ⟨one_ne_zero, one_dvd _⟩

/-- Started at `(0, 1)`, the general recurrence *is* the `√n` recurrence of
`Palindrome.lean` — the `Q`s there are all positive, so `step` never takes its
negative branch. -/
lemma iterate_eq_state (n : ℕ) (hn : ¬IsSquare n) (k : ℕ) :
    (step n)^[k] (0, 1) = Palindrome.state n k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Palindrome.state_succ,
        step_of_pos (Palindrome.Q_pos_all n hn k)]

/-- The `√n` case.  `Palindrome.purely_periodic` is sharper — there the
preperiod is `1` — so this is a consistency check, not a new result. -/
theorem eventually_periodic_sqrt (n : ℕ) (hn : ¬IsSquare n) :
    ∃ m L : ℕ, 0 < L ∧ ∀ k, m ≤ k → Palindrome.state n (k + L) = Palindrome.state n k := by
  obtain ⟨m, L, hL, hper⟩ := eventually_periodic n hn (adm_sqrt n)
  refine ⟨m, L, hL, fun k hk => ?_⟩
  rw [← iterate_eq_state n hn, ← iterate_eq_state n hn]
  exact hper k hk

lemma not_isSquare_five : ¬ IsSquare 5 := by
  rintro ⟨r, hr⟩
  rcases (by omega : r ≤ 2 ∨ 3 ≤ r) with h | h
  · interval_cases r <;> omega
  · nlinarith

/-- A state that is **not** `√n`: the golden ratio `φ = (1 + √5)/2`, where
`Q = 2` and `2 ∣ 5 - 1²`.  This is the case `Palindrome.lean` cannot reach. -/
theorem eventually_periodic_golden :
    ∃ m L : ℕ, 0 < L ∧ ∀ k, m ≤ k → (step 5)^[k + L] (1, 2) = (step 5)^[k] (1, 2) :=
  eventually_periodic 5 not_isSquare_five ⟨by norm_num, by norm_num⟩

#print axioms floor_surd
#print axioms surd_step
#print axioms exists_reduced
#print axioms eventually_periodic
#print axioms eventually_periodic_sqrt
#print axioms eventually_periodic_golden

end Quadratic
