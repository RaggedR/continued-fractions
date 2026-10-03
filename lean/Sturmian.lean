/-
# Sturmian sequences of √n

Formalisation of `../all-the-proofs.tex`.  Phase 0: the two codings, and the
proof that they are the floor and ceiling formulas of Morse and Hedlund.

Companion to `Palindrome.lean`, which proves Legendre's theorem for √n.  The
two files meet at `Palindrome.alpha n k`, the k-th complete quotient: its
fractional part is the k-th tail of the continued fraction, which is the slope
at level k of the tower of derived sequences.
-/
import Mathlib

namespace Sturmian

open Int

variable {α x y : ℝ}

/-! ## §1 Codings -/

/-- The lower coding of `x`: letter `1` when the orbit point lies in `[1-α, 1)`. -/
noncomputable def code (α x : ℝ) (k : ℕ) : ℕ :=
  if 1 - α ≤ Int.fract (x + k * α) then 1 else 0

/-- The upper coding of `x`: letter `1` when the orbit point lies in `(1-α, 1]`,
with `1` read as `0` on the circle. -/
noncomputable def codeUp (α x : ℝ) (k : ℕ) : ℕ :=
  if 1 - α < Int.fract (x + k * α) ∨ Int.fract (x + k * α) = 0 then 1 else 0

/-! ### The orbit -/

/-- Reducing the base point modulo 1 does not move the orbit. -/
lemma fract_add_left (a b : ℝ) : Int.fract (a + b) = Int.fract (Int.fract a + b) := by
  have h : a + b = (⌊a⌋ : ℝ) + (Int.fract a + b) := by
    have := Int.floor_add_fract a; linarith
  rw [h, Int.fract_intCast_add]

lemma fract_orbit_succ (α x : ℝ) (k : ℕ) :
    Int.fract (x + ((k + 1 : ℕ) : ℝ) * α) = Int.fract (Int.fract (x + (k : ℝ) * α) + α) := by
  rw [← fract_add_left]
  congr 1
  push_cast
  ring

lemma fract_orbit_add (α x : ℝ) (k t : ℕ) :
    Int.fract (x + ((k + t : ℕ) : ℝ) * α)
      = Int.fract (Int.fract (x + (k : ℝ) * α) + (t : ℝ) * α) := by
  rw [← fract_add_left]
  congr 1
  push_cast
  ring

/-! ### Lemma 1.1 -/

/-- One step of the floor function, for a step length in `(0,1)`. -/
lemma floor_step (hα0 : 0 < α) (hα1 : α < 1) (y : ℝ) :
    ⌊y + α⌋ - ⌊y⌋ = if 1 - α ≤ Int.fract y then 1 else 0 := by
  have h0 := Int.fract_nonneg y
  have h1 := Int.fract_lt_one y
  have hfy := Int.floor_add_fract y
  have hy : y + α = (⌊y⌋ : ℝ) + (Int.fract y + α) := by linarith
  rw [hy, Int.floor_intCast_add]
  split_ifs with h
  · have hone : ⌊Int.fract y + α⌋ = 1 := by
      rw [Int.floor_eq_iff]
      constructor <;> push_cast <;> linarith
    omega
  · have hzero : ⌊Int.fract y + α⌋ = 0 := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith [not_le.mp h]
    omega

/-- One step of the ceiling function, for a step length in `(0,1)`. -/
lemma ceil_step (hα0 : 0 < α) (hα1 : α < 1) (y : ℝ) :
    ⌈y + α⌉ - ⌈y⌉ = if 1 - α < Int.fract y ∨ Int.fract y = 0 then 1 else 0 := by
  have h0 := Int.fract_nonneg y
  have h1 := Int.fract_lt_one y
  have hfy := Int.floor_add_fract y
  have hy : y + α = (⌊y⌋ : ℝ) + (Int.fract y + α) := by linarith
  have hcy : ⌈y⌉ = ⌊y⌋ + ⌈Int.fract y⌉ := by
    conv_lhs => rw [← hfy]
    rw [Int.ceil_intCast_add]
  have hc : ⌈Int.fract y⌉ = if Int.fract y = 0 then 0 else 1 := by
    split_ifs with hz
    · simp [hz]
    · have hpos : 0 < Int.fract y := lt_of_le_of_ne h0 (Ne.symm hz)
      rw [Int.ceil_eq_iff]
      constructor <;> push_cast <;> linarith
  have hca : ⌈Int.fract y + α⌉ = if 1 - α < Int.fract y then 2 else 1 := by
    split_ifs with h
    · rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
    · rw [Int.ceil_eq_iff]; push_cast
      constructor <;> linarith [not_lt.mp h]
  rw [hy, Int.ceil_intCast_add, hcy, hc, hca]
  by_cases hz : Int.fract y = 0
  · simp [hz]
    linarith
  · by_cases h : 1 - α < Int.fract y <;> simp [hz, h]

theorem code_eq_sub_floor (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) :
    (code α x k : ℤ) = ⌊((k : ℝ) + 1) * α + x⌋ - ⌊(k : ℝ) * α + x⌋ := by
  have h : ((k : ℝ) + 1) * α + x = ((k : ℝ) * α + x) + α := by ring
  have hcomm : Int.fract ((k : ℝ) * α + x) = Int.fract (x + (k : ℝ) * α) := by
    rw [add_comm]
  rw [h, floor_step hα0 hα1, hcomm]
  unfold code
  split_ifs <;> simp

theorem codeUp_eq_sub_ceil (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) :
    (codeUp α x k : ℤ) = ⌈((k : ℝ) + 1) * α + x⌉ - ⌈(k : ℝ) * α + x⌉ := by
  have h : ((k : ℝ) + 1) * α + x = ((k : ℝ) * α + x) + α := by ring
  have hcomm : Int.fract ((k : ℝ) * α + x) = Int.fract (x + (k : ℝ) * α) := by
    rw [add_comm]
  rw [h, ceil_step hα0 hα1, hcomm]
  unfold codeUp
  split_ifs <;> simp

/-! ### Lemma 1.3 — when the two codings agree -/

theorem code_eq_codeUp (h : ∀ k : ℕ, Int.fract (x + (k : ℝ) * α) ≠ 0) :
    code α x = codeUp α x := by
  funext k
  have hne : Int.fract (x + (k : ℝ) * α) ≠ 1 - α := by
    intro hk
    have h2 := h (k + 1)
    rw [fract_orbit_succ, hk] at h2
    simp at h2
  unfold code codeUp
  rcases lt_trichotomy (1 - α) (Int.fract (x + (k : ℝ) * α)) with hlt | heq | hgt
  · simp [le_of_lt hlt, hlt]
  · exact absurd heq.symm hne
  · simp [not_le.mpr hgt, not_lt.mpr (le_of_lt hgt), h k]

/-! ### Lemma 1.4 — counting the ones -/

theorem sum_code (hα0 : 0 < α) (hα1 : α < 1) (hx0 : 0 ≤ x) (hx1 : x < 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, (code α x k : ℤ) = ⌊(N : ℝ) * α + x⌋ := by
  have key : ∀ k ∈ Finset.range N, (code α x k : ℤ)
      = (fun j : ℕ => ⌊(j : ℝ) * α + x⌋) (k + 1) - (fun j : ℕ => ⌊(j : ℝ) * α + x⌋) k := by
    intro k _
    simpa using code_eq_sub_floor (x := x) hα0 hα1 k
  rw [Finset.sum_congr rfl key, Finset.sum_range_sub (fun j : ℕ => ⌊(j : ℝ) * α + x⌋) N]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [Int.floor_eq_zero_iff.mpr (Set.mem_Ico.mpr ⟨hx0, hx1⟩), sub_zero]

/-! ### Lemma 1.5 — the shift -/

theorem code_succ (α x : ℝ) (k : ℕ) :
    code α x (k + 1) = code α (Int.fract (x + α)) k := by
  have h : Int.fract (x + ((k : ℝ) + 1) * α) = Int.fract (Int.fract (x + α) + (k : ℝ) * α) := by
    rw [← fract_add_left]
    congr 1
    ring
  unfold code
  push_cast
  rw [h]

theorem codeUp_succ (α x : ℝ) (k : ℕ) :
    codeUp α x (k + 1) = codeUp α (Int.fract (x + α)) k := by
  have h : Int.fract (x + ((k : ℝ) + 1) * α) = Int.fract (Int.fract (x + α) + (k : ℝ) * α) := by
    rw [← fract_add_left]
    congr 1
    ring
  unfold codeUp
  push_cast
  rw [h]

/-! ## §2 The orbit is dense -/

/-- A nonzero multiple of an irrational has nonzero fractional part. -/
lemma fract_nat_mul_ne_zero (hα : Irrational α) {q : ℕ} (hq : q ≠ 0) :
    Int.fract ((q : ℝ) * α) ≠ 0 := by
  intro h
  have hirr : Irrational ((q : ℝ) * α) := hα.natCast_mul hq
  exact hirr.ne_int ⌊(q : ℝ) * α⌋ (by rw [Int.fract] at h; linarith)

/-- Dirichlet, by pigeonhole: some positive multiple of `α` is within `ε` of an integer.
Irrationality is not needed; it enters only to make the gap nonzero. -/
lemma exists_fract_near_int (α : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, 1 ≤ q ∧ (Int.fract ((q : ℝ) * α) < ε ∨ 1 - ε < Int.fract ((q : ℝ) * α)) := by
  obtain ⟨N, hN0, hN⟩ : ∃ N : ℕ, 0 < N ∧ (1 : ℝ) / N < ε := by
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N + 1, Nat.succ_pos N, ?_⟩
    have h1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have h2 : 1 / ε < (N : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ hε] at h2
    push_cast
    rw [div_lt_iff₀ h1]
    linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  set f : ℕ → ℕ := fun i => ⌊(N : ℝ) * Int.fract ((i : ℝ) * α)⌋.toNat with hf
  have hmaps : ∀ i ∈ Finset.range (N + 1), f i ∈ Finset.range N := by
    intro i _
    simp only [hf, Finset.mem_range]
    have h1 : (N : ℝ) * Int.fract ((i : ℝ) * α) < N := by
      nlinarith [Int.fract_lt_one ((i : ℝ) * α), Int.fract_nonneg ((i : ℝ) * α)]
    have hlt : ⌊(N : ℝ) * Int.fract ((i : ℝ) * α)⌋ < (N : ℤ) := by
      rw [Int.floor_lt]; exact_mod_cast h1
    omega
  have hcard : (Finset.range N).card < (Finset.range (N + 1)).card := by simp
  obtain ⟨i, -, j, -, hij, hfij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have key : ∀ k : ℕ, (f k : ℝ) ≤ (N : ℝ) * Int.fract ((k : ℝ) * α) ∧
      (N : ℝ) * Int.fract ((k : ℝ) * α) < (f k : ℝ) + 1 := by
    intro k
    have h0 : 0 ≤ (N : ℝ) * Int.fract ((k : ℝ) * α) :=
      mul_nonneg (le_of_lt hNR) (Int.fract_nonneg _)
    have hnn : (0 : ℤ) ≤ ⌊(N : ℝ) * Int.fract ((k : ℝ) * α)⌋ := Int.floor_nonneg.mpr h0
    have hcast : ((f k : ℕ) : ℝ) = (⌊(N : ℝ) * Int.fract ((k : ℝ) * α)⌋ : ℝ) := by
      simp only [hf]
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hnn)
    rw [hcast]
    exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
  obtain ⟨hi1, hi2⟩ := key i
  obtain ⟨hj1, hj2⟩ := key j
  rw [hfij] at hi1 hi2
  have hinv : (1 : ℝ) / N * N = 1 := div_mul_cancel₀ 1 (ne_of_gt hNR)
  have hN1 : (1 : ℝ) / N ≤ 1 := by rw [div_le_one hNR]; exact_mod_cast hN0
  have hb1 : Int.fract ((i : ℝ) * α) - Int.fract ((j : ℝ) * α) < 1 / N := by nlinarith
  have hb2 : Int.fract ((j : ℝ) * α) - Int.fract ((i : ℝ) * α) < 1 / N := by nlinarith
  -- in either order the difference is a fractional part of a positive multiple
  have main : ∀ u v : ℕ, v < u →
      Int.fract (((u - v : ℕ) : ℝ) * α)
        = Int.fract (Int.fract ((u : ℝ) * α) - Int.fract ((v : ℝ) * α)) := by
    intro u v huv
    refine Int.fract_eq_fract.mpr ⟨⌊(u : ℝ) * α⌋ - ⌊(v : ℝ) * α⌋, ?_⟩
    have hc : ((u - v : ℕ) : ℝ) = (u : ℝ) - (v : ℝ) := by
      have : v ≤ u := le_of_lt huv
      push_cast [this]; ring
    rw [hc, Int.fract, Int.fract]; push_cast; ring
  have split : ∀ t : ℝ, -(1 / (N : ℝ)) < t → t < 1 / N →
      Int.fract t < ε ∨ 1 - ε < Int.fract t := by
    intro t htl htu
    by_cases hts : 0 ≤ t
    · left
      rw [Int.fract_eq_self.mpr ⟨hts, by linarith⟩]
      linarith
    · right
      rw [not_le] at hts
      have h : Int.fract t = t + 1 := by
        have e : Int.fract t = Int.fract (t + 1) := Int.fract_eq_fract.mpr ⟨-1, by push_cast; ring⟩
        rw [e, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
      rw [h]; linarith
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact ⟨j - i, by omega, by rw [main j i hlt]; exact split _ (by linarith) (by linarith)⟩
  · exact ⟨i - j, by omega, by rw [main i j hlt]; exact split _ (by linarith) (by linarith)⟩

/-! ### The two ladders

Climbing by `δ` lands in `[c, c+δ)` after an explicit number of steps.  No
induction: the step count is a ceiling. -/

lemma exists_ladder_up {δ c y : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hcδ : c + δ ≤ 1)
    (hy1 : y < 1) :
    ∃ k : ℕ, 1 ≤ k ∧ c ≤ Int.fract (y + k * δ) ∧ Int.fract (y + k * δ) < c + δ := by
  have hpos : 0 < (c - y + 1) / δ := div_pos (by linarith) hδ
  refine ⟨⌈(c - y + 1) / δ⌉₊, Nat.ceil_pos.mpr hpos, ?_⟩
  set k := ⌈(c - y + 1) / δ⌉₊ with hk
  have hlow : c - y + 1 ≤ (k : ℝ) * δ := by
    have h := Nat.le_ceil ((c - y + 1) / δ)
    rw [div_le_iff₀ hδ] at h
    linarith
  have hhigh : (k : ℝ) * δ < c - y + 1 + δ := by
    have h := Nat.ceil_lt_add_one hpos.le
    have h2 : (k : ℝ) * δ < ((c - y + 1) / δ + 1) * δ := by
      exact mul_lt_mul_of_pos_right h hδ
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hδ), one_mul] at h2
    linarith
  have hfr : Int.fract (y + (k : ℝ) * δ) = y + (k : ℝ) * δ - 1 := by
    have e : Int.fract (y + (k : ℝ) * δ) = Int.fract (y + (k : ℝ) * δ - 1) :=
      Int.fract_eq_fract.mpr ⟨1, by push_cast; ring⟩
    rw [e, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  rw [hfr]
  constructor <;> linarith

lemma exists_ladder_down {δ c y : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hc : 0 ≤ c)
    (hcδ : c + δ ≤ 1) (hy0 : 0 ≤ y) :
    ∃ k : ℕ, 1 ≤ k ∧ c ≤ Int.fract (y - k * δ) ∧ Int.fract (y - k * δ) < c + δ := by
  have ht1 : (1 : ℝ) ≤ (y + 2 - c) / δ := by rw [le_div_iff₀ hδ]; linarith
  refine ⟨⌊(y + 2 - c) / δ⌋₊, Nat.le_floor (by exact_mod_cast ht1), ?_⟩
  set k := ⌊(y + 2 - c) / δ⌋₊ with hk
  have hhigh : (k : ℝ) * δ ≤ y + 2 - c := by
    have h := Nat.floor_le (by linarith : (0 : ℝ) ≤ (y + 2 - c) / δ)
    rw [le_div_iff₀ hδ] at h
    linarith
  have hlow : y + 2 - c - δ < (k : ℝ) * δ := by
    have h := Nat.lt_floor_add_one ((y + 2 - c) / δ)
    have h2 : (y + 2 - c) / δ * δ < ((k : ℝ) + 1) * δ := mul_lt_mul_of_pos_right h hδ
    rw [div_mul_cancel₀ _ (ne_of_gt hδ), add_mul, one_mul] at h2
    linarith
  have hfr : Int.fract (y - (k : ℝ) * δ) = y - (k : ℝ) * δ + 2 := by
    have e : Int.fract (y - (k : ℝ) * δ) = Int.fract (y - (k : ℝ) * δ + 2) :=
      Int.fract_eq_fract.mpr ⟨-2, by push_cast; ring⟩
    rw [e, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  rw [hfr]
  constructor <;> linarith

/-! ### Lemma 2.2 — the orbit meets every subinterval

`sturmian.tex` and `all-the-proofs.tex` say "dense in `[0,1)`".  `DenseRange`
is the wrong Lean statement: the range lies in `[0,1)`, so it is not dense in
`ℝ`.  The interval form below is the one the later sections consume; the
topological packaging is `Icc_subset_closure_orbit`. -/

theorem exists_fract_mem_Ico (hα : Irrational α) (x : ℝ) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε) (hcε : c + ε ≤ 1) :
    ∃ k : ℕ, 1 ≤ k ∧ c ≤ Int.fract (x + k * α) ∧ Int.fract (x + k * α) < c + ε := by
  obtain ⟨q, hq1, hqd⟩ := exists_fract_near_int α (half_pos hε)
  have hy0 := Int.fract_nonneg x
  have hy1 := Int.fract_lt_one x
  have hq0 : 0 < Int.fract ((q : ℝ) * α) :=
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm (fract_nat_mul_ne_zero hα (by omega)))
  have hqlt : Int.fract ((q : ℝ) * α) < 1 := Int.fract_lt_one _
  rcases hqd with hcase | hcase
  · obtain ⟨k, hk1, h1, h2⟩ :=
      exists_ladder_up (δ := Int.fract ((q : ℝ) * α)) (c := c) (y := Int.fract x)
        hq0 hc (by linarith) hy1
    refine ⟨k * q, Nat.one_le_iff_ne_zero.mpr (by positivity), ?_, ?_⟩ <;>
    · have htrans : Int.fract (x + ((k * q : ℕ) : ℝ) * α)
          = Int.fract (Int.fract x + (k : ℝ) * Int.fract ((q : ℝ) * α)) := by
        rw [Int.fract_eq_fract]
        refine ⟨⌊x⌋ + k * ⌊(q : ℝ) * α⌋, ?_⟩
        simp only [Int.fract]
        push_cast
        ring
      rw [htrans]
      linarith
  · obtain ⟨k, hk1, h1, h2⟩ :=
      exists_ladder_down (δ := 1 - Int.fract ((q : ℝ) * α)) (c := c) (y := Int.fract x)
        (by linarith) (by linarith) hc (by linarith) hy0
    refine ⟨k * q, Nat.one_le_iff_ne_zero.mpr (by positivity), ?_, ?_⟩ <;>
    · have htrans : Int.fract (x + ((k * q : ℕ) : ℝ) * α)
          = Int.fract (Int.fract x - (k : ℝ) * (1 - Int.fract ((q : ℝ) * α))) := by
        rw [Int.fract_eq_fract]
        refine ⟨⌊x⌋ + k + k * ⌊(q : ℝ) * α⌋, ?_⟩
        simp only [Int.fract]
        push_cast
        ring
      rw [htrans]
      linarith

theorem exists_fract_mem_Ioo (hα : Irrational α) (x : ℝ) {c d : ℝ}
    (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ 1) :
    ∃ k : ℕ, 1 ≤ k ∧ c < Int.fract (x + k * α) ∧ Int.fract (x + k * α) < d := by
  obtain ⟨k, hk1, h1, h2⟩ :=
    exists_fract_mem_Ico hα x (c := c + (d - c) / 3) (ε := (d - c) / 3)
      (by linarith) (by linarith) (by linarith)
  exact ⟨k, hk1, by linarith, by linarith⟩

theorem Icc_subset_closure_orbit (hα : Irrational α) (x : ℝ) :
    Set.Icc (0 : ℝ) 1 ⊆ closure (Set.range fun k : ℕ => Int.fract (x + k * α)) := by
  rintro z ⟨hz0, hz1⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hc : (0 : ℝ) ≤ max 0 (z - ε / 2) := le_max_left _ _
  have hd : min 1 (z + ε / 2) ≤ 1 := min_le_left _ _
  have hcd : max 0 (z - ε / 2) < min 1 (z + ε / 2) :=
    max_lt (lt_min (by norm_num) (by linarith)) (lt_min (by linarith) (by linarith))
  obtain ⟨k, -, h1, h2⟩ := exists_fract_mem_Ioo hα x hc hcd hd
  refine ⟨_, Set.mem_range_self k, ?_⟩
  have e1 : z - ε / 2 ≤ max 0 (z - ε / 2) := le_max_right _ _
  have e2 : min 1 (z + ε / 2) ≤ z + ε / 2 := min_le_right _ _
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ## §3 Complexity -/

section Complexity

variable {t s : ℝ}

/-- The `m` cut points `{-jα}`, `1 ≤ j ≤ m`, of Theorem 3.1. -/
noncomputable def cuts (α : ℝ) (m : ℕ) : Finset ℝ :=
  (Finset.Icc 1 m).image (fun j : ℕ => Int.fract (-((j : ℝ) * α)))

/-- The cell of `t`: how many cut points lie at or below it. -/
noncomputable def cell (α : ℝ) (m : ℕ) (t : ℝ) : ℕ :=
  ((cuts α m).filter (fun p => p ≤ t)).card

lemma mem_cuts_iff (α : ℝ) (m : ℕ) (p : ℝ) :
    p ∈ cuts α m ↔ ∃ j : ℕ, 1 ≤ j ∧ j ≤ m ∧ Int.fract (-((j : ℝ) * α)) = p := by
  simp only [cuts, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨j, ⟨h1, h2⟩, h3⟩; exact ⟨j, h1, h2, h3⟩
  · rintro ⟨j, h1, h2, h3⟩; exact ⟨j, ⟨h1, h2⟩, h3⟩

lemma mem_cuts (hj1 : 1 ≤ j) (hj : j ≤ m) : Int.fract (-((j : ℝ) * α)) ∈ cuts α m :=
  (mem_cuts_iff α m _).mpr ⟨j, hj1, hj, rfl⟩

/-! ### The cut points are distinct and lie in `(0,1)` -/

lemma fract_neg_nat_mul (hα : Irrational α) {j : ℕ} (hj : 1 ≤ j) :
    Int.fract (-((j : ℝ) * α)) = 1 - Int.fract ((j : ℝ) * α) :=
  Int.fract_neg (fract_nat_mul_ne_zero hα (by omega))

lemma cut_ne_of_lt (hα : Irrational α) {i j : ℕ} (hlt : i < j) :
    Int.fract (-((i : ℝ) * α)) ≠ Int.fract (-((j : ℝ) * α)) := by
  intro h
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp h
  have hcast : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) := by
    rw [Nat.cast_sub hlt.le]
  have hd : ((j - i : ℕ) : ℝ) * α = (z : ℝ) := by
    rw [hcast, sub_mul]; linarith
  have hne := fract_nat_mul_ne_zero hα (q := j - i) (by omega)
  rw [hd, Int.fract_intCast] at hne
  exact hne rfl

lemma cut_inj (hα : Irrational α) {i j : ℕ}
    (h : Int.fract (-((i : ℝ) * α)) = Int.fract (-((j : ℝ) * α))) : i = j := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd h (cut_ne_of_lt hα hlt)
  · exact heq
  · exact absurd h.symm (cut_ne_of_lt hα hgt)

lemma cuts_pos (hα : Irrational α) {m : ℕ} {p : ℝ} (hp : p ∈ cuts α m) : 0 < p ∧ p < 1 := by
  obtain ⟨j, hj1, _, rfl⟩ := (mem_cuts_iff α m p).mp hp
  rw [fract_neg_nat_mul hα hj1]
  have hne := fract_nat_mul_ne_zero hα (q := j) (by omega)
  have h0 : 0 < Int.fract ((j : ℝ) * α) :=
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hne)
  have h1 := Int.fract_lt_one ((j : ℝ) * α)
  exact ⟨by linarith, by linarith⟩

lemma card_cuts (hα : Irrational α) (m : ℕ) : (cuts α m).card = m := by
  rw [cuts, Finset.card_image_of_injOn, Nat.card_Icc]
  · omega
  · intro i _ j _ h
    exact cut_inj hα h

/-! ### `cell` is monotone, and strictly monotone on the cut points -/

lemma cuts_filter_subset {m : ℕ} (hts : t ≤ s) :
    (cuts α m).filter (fun p => p ≤ t) ⊆ (cuts α m).filter (fun p => p ≤ s) := by
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, le_trans hp.2 hts⟩

lemma cell_mono {m : ℕ} (hts : t ≤ s) : cell α m t ≤ cell α m s :=
  Finset.card_le_card (cuts_filter_subset hts)

lemma filter_eq_of_cell_eq {m : ℕ} (h : cell α m t = cell α m s) :
    (cuts α m).filter (fun p => p ≤ t) = (cuts α m).filter (fun p => p ≤ s) := by
  rcases le_total t s with hts | hst
  · exact Finset.eq_of_subset_of_card_le (cuts_filter_subset hts) h.ge
  · exact (Finset.eq_of_subset_of_card_le (cuts_filter_subset hst) h.le).symm

lemma one_le_cell_of_mem {m : ℕ} {p : ℝ} (hp : p ∈ cuts α m) : 1 ≤ cell α m p :=
  Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, le_refl p⟩⟩

lemma cell_le (hα : Irrational α) (m : ℕ) (t : ℝ) : cell α m t ≤ m := by
  have h := Finset.card_filter_le (cuts α m) (fun p => p ≤ t)
  rwa [card_cuts hα m] at h

lemma cell_lt_cell {m : ℕ} {p q : ℝ} (hq : q ∈ cuts α m) (hpq : p < q) :
    cell α m p < cell α m q := by
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset (cuts_filter_subset hpq.le)).mpr ?_)
  refine ⟨q, Finset.mem_filter.mpr ⟨hq, le_refl q⟩, ?_⟩
  intro hmem
  exact absurd (Finset.mem_filter.mp hmem).2 (not_le.mpr hpq)

lemma le_of_cell_le {m : ℕ} {p q : ℝ} (hp : p ∈ cuts α m)
    (h : cell α m p ≤ cell α m q) : p ≤ q := by
  by_contra hc
  have := cell_lt_cell hp (not_le.mp hc)
  omega

lemma cell_injOn (α : ℝ) (m : ℕ) : Set.InjOn (cell α m) ↑(cuts α m) := by
  intro p hp q hq h
  rw [Finset.mem_coe] at hp hq
  rcases lt_trichotomy p q with hlt | heq | hgt
  · have := cell_lt_cell hq hlt; omega
  · exact heq
  · have := cell_lt_cell hp hgt; omega

/-- `cell` maps the cut points bijectively onto `{1,…,m}`: every rank is attained. -/
lemma exists_cut_cell (hα : Irrational α) {m r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ m) :
    ∃ p ∈ cuts α m, cell α m p = r := by
  have hsub : (cuts α m).image (cell α m) ⊆ Finset.Icc 1 m := by
    intro r' hr'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr'
    exact Finset.mem_Icc.mpr ⟨one_le_cell_of_mem hp, cell_le hα m p⟩
  have hcard : (Finset.Icc 1 m).card ≤ ((cuts α m).image (cell α m)).card := by
    rw [Finset.card_image_of_injOn (cell_injOn α m), card_cuts hα, Nat.card_Icc]
    omega
  have himg := Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : r ∈ (cuts α m).image (cell α m) := by
    rw [himg]; exact Finset.mem_Icc.mpr ⟨hr1, hr⟩
  exact Finset.mem_image.mp hmem

/-! ### The floor formula -/

lemma floor_nat_mul_add (hα : Irrational α) (ht0 : 0 ≤ t) (ht1 : t < 1) {j : ℕ} (hj : 1 ≤ j) :
    ⌊(j : ℝ) * α + t⌋ = ⌊(j : ℝ) * α⌋ + if Int.fract (-((j : ℝ) * α)) ≤ t then 1 else 0 := by
  rw [fract_neg_nat_mul hα hj]
  have hf0 := Int.fract_nonneg ((j : ℝ) * α)
  have hf1 := Int.fract_lt_one ((j : ℝ) * α)
  have hsplit : (j : ℝ) * α + t = (Int.fract ((j : ℝ) * α) + t) + (⌊(j : ℝ) * α⌋ : ℝ) := by
    have := Int.floor_add_fract ((j : ℝ) * α); linarith
  rw [hsplit, Int.floor_add_intCast]
  by_cases h : 1 - Int.fract ((j : ℝ) * α) ≤ t
  · rw [if_pos h]
    have hv : ⌊Int.fract ((j : ℝ) * α) + t⌋ = 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    omega
  · rw [if_neg h]
    have h' := not_le.mp h
    have hv : ⌊Int.fract ((j : ℝ) * α) + t⌋ = 0 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    omega

/-! ### A word of length `m` determines, and is determined by, the cell -/

lemma code_eq_iff_cell_eq (hα : Irrational α) (hα0 : 0 < α) (hα1 : α < 1)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hs0 : 0 ≤ s) (hs1 : s < 1) (m : ℕ) :
    (∀ i : ℕ, i < m → code α t i = code α s i) ↔ cell α m t = cell α m s := by
  constructor
  · intro hw
    have hfl : ∀ j : ℕ, j ≤ m → ⌊(j : ℝ) * α + t⌋ = ⌊(j : ℝ) * α + s⌋ := by
      intro j hj
      rw [← sum_code hα0 hα1 ht0 ht1, ← sum_code hα0 hα1 hs0 hs1]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hw i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj)]
    unfold cell
    congr 1
    ext p
    rw [Finset.mem_filter, Finset.mem_filter]
    refine and_congr_right fun hp => ?_
    obtain ⟨j, hj1, hj, rfl⟩ := (mem_cuts_iff α m p).mp hp
    have h3 := hfl j hj
    rw [floor_nat_mul_add hα ht0 ht1 hj1, floor_nat_mul_add hα hs0 hs1 hj1] at h3
    by_cases hp' : Int.fract (-((j : ℝ) * α)) ≤ t
    · by_cases hq : Int.fract (-((j : ℝ) * α)) ≤ s
      · exact iff_of_true hp' hq
      · rw [if_pos hp', if_neg hq] at h3; omega
    · by_cases hq : Int.fract (-((j : ℝ) * α)) ≤ s
      · rw [if_neg hp', if_pos hq] at h3; omega
      · exact iff_of_false hp' hq
  · intro hc i hi
    have hcmp : ∀ j : ℕ, 1 ≤ j → j ≤ m →
        (Int.fract (-((j : ℝ) * α)) ≤ t ↔ Int.fract (-((j : ℝ) * α)) ≤ s) := by
      intro j hj1 hj
      have key := Finset.ext_iff.mp (filter_eq_of_cell_eq hc) (Int.fract (-((j : ℝ) * α)))
      rw [Finset.mem_filter, Finset.mem_filter] at key
      have hm := mem_cuts (α := α) (j := j) (m := m) hj1 hj
      constructor
      · intro h; exact (key.mp ⟨hm, h⟩).2
      · intro h; exact (key.mpr ⟨hm, h⟩).2
    have hfl : ∀ j : ℕ, j ≤ m → ⌊(j : ℝ) * α + t⌋ = ⌊(j : ℝ) * α + s⌋ := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hj1
      · simp only [Nat.cast_zero, zero_mul, zero_add]
        rw [Int.floor_eq_zero_iff.mpr (Set.mem_Ico.mpr ⟨ht0, ht1⟩),
            Int.floor_eq_zero_iff.mpr (Set.mem_Ico.mpr ⟨hs0, hs1⟩)]
      · rw [floor_nat_mul_add hα ht0 ht1 hj1, floor_nat_mul_add hα hs0 hs1 hj1,
            if_congr (hcmp j hj1 hj) rfl rfl]
    have e1 := code_eq_sub_floor (α := α) (x := t) hα0 hα1 i
    have e2 := code_eq_sub_floor (α := α) (x := s) hα0 hα1 i
    have f1 := hfl i hi.le
    have f2 := hfl (i + 1) (by omega)
    push_cast at f2
    have key : (code α t i : ℤ) = (code α s i : ℤ) := by rw [e1, e2, f1, f2]
    exact Nat.cast_injective key

/-! ### The factors -/

/-- The factor of length `m` at position `k`. -/
noncomputable def factor (α x : ℝ) (m k : ℕ) : Fin m → ℕ := fun j => code α x (k + j)

lemma factor_apply (α x : ℝ) (m k : ℕ) (j : Fin m) :
    factor α x m k j = code α (Int.fract (x + (k : ℝ) * α)) (j : ℕ) := by
  unfold factor code
  rw [fract_orbit_add]

lemma factor_eq_iff (hα : Irrational α) (hα0 : 0 < α) (hα1 : α < 1) (x : ℝ) (m k l : ℕ) :
    factor α x m k = factor α x m l ↔
      cell α m (Int.fract (x + (k : ℝ) * α)) = cell α m (Int.fract (x + (l : ℝ) * α)) := by
  rw [← code_eq_iff_cell_eq hα hα0 hα1 (Int.fract_nonneg _) (Int.fract_lt_one _)
        (Int.fract_nonneg _) (Int.fract_lt_one _) m]
  constructor
  · intro h i hi
    have hj := congrFun h ⟨i, hi⟩
    rwa [factor_apply, factor_apply] at hj
  · intro h
    funext j
    rw [factor_apply, factor_apply]
    exact h j j.isLt

/-! ### Every cell is hit -/

lemma exists_cell (hα : Irrational α) (x : ℝ) {m r : ℕ} (hr : r ≤ m) :
    ∃ k : ℕ, cell α m (Int.fract (x + (k : ℝ) * α)) = r := by
  obtain ⟨c, hcmem, hclow⟩ : ∃ c : ℝ, (c = 0 ∨ c ∈ cuts α m) ∧
      ∀ p ∈ cuts α m, (p ≤ c ↔ cell α m p ≤ r) := by
    rcases Nat.eq_zero_or_pos r with rfl | hr1
    · refine ⟨0, Or.inl rfl, fun p hp => ?_⟩
      refine iff_of_false (not_le.mpr (cuts_pos hα hp).1) ?_
      have := one_le_cell_of_mem hp; omega
    · obtain ⟨c, hcmem, hcell⟩ := exists_cut_cell hα hr1 hr
      refine ⟨c, Or.inr hcmem, fun p hp => ?_⟩
      constructor
      · intro hle; have := cell_mono (α := α) (m := m) hle; omega
      · intro hle; exact le_of_cell_le hp (by omega)
  obtain ⟨d, hdmem, hdhigh⟩ : ∃ d : ℝ, (d = 1 ∨ d ∈ cuts α m) ∧
      ∀ p ∈ cuts α m, (p < d ↔ cell α m p ≤ r) := by
    rcases eq_or_lt_of_le hr with rfl | hrm
    · exact ⟨1, Or.inl rfl, fun p hp => iff_of_true (cuts_pos hα hp).2 (cell_le hα _ p)⟩
    · obtain ⟨d, hdmem, hcell⟩ := exists_cut_cell hα (by omega : 1 ≤ r + 1) (by omega : r + 1 ≤ m)
      refine ⟨d, Or.inr hdmem, fun p hp => ?_⟩
      constructor
      · intro hlt; have := cell_lt_cell hdmem hlt; omega
      · intro hle
        rcases lt_trichotomy p d with h | h | h
        · exact h
        · rw [h] at hle; omega
        · have := cell_lt_cell hp h; omega
  have hc0 : 0 ≤ c := by
    rcases hcmem with rfl | h
    · exact le_refl 0
    · exact (cuts_pos hα h).1.le
  have hd1 : d ≤ 1 := by
    rcases hdmem with rfl | h
    · exact le_refl 1
    · exact (cuts_pos hα h).2.le
  have hcd : c < d := by
    rcases hcmem with rfl | hc
    · rcases hdmem with rfl | hd
      · norm_num
      · exact (cuts_pos hα hd).1
    · rcases hdmem with rfl | hd
      · exact (cuts_pos hα hc).2
      · exact (hdhigh c hc).mpr ((hclow c hc).mp (le_refl c))
  have hconst : ∀ u : ℝ, c ≤ u → u < d → cell α m u = r := by
    intro u h1 h2
    have hfilter : (cuts α m).filter (fun p => p ≤ u)
        = (cuts α m).filter (fun p => cell α m p ≤ r) := by
      ext p
      rw [Finset.mem_filter, Finset.mem_filter]
      refine and_congr_right fun hp => ?_
      constructor
      · intro hle; exact (hdhigh p hp).mp (lt_of_le_of_lt hle h2)
      · intro hle; exact le_trans ((hclow p hp).mpr hle) h1
    have himg : ((cuts α m).filter (fun p => cell α m p ≤ r)).image (cell α m)
        = Finset.Icc 1 r := by
      ext q
      rw [Finset.mem_image, Finset.mem_Icc]
      constructor
      · rintro ⟨p, hp, rfl⟩
        rw [Finset.mem_filter] at hp
        exact ⟨one_le_cell_of_mem hp.1, hp.2⟩
      · rintro ⟨hq1, hqr⟩
        obtain ⟨p, hp, hcell⟩ := exists_cut_cell hα hq1 (le_trans hqr hr)
        exact ⟨p, Finset.mem_filter.mpr ⟨hp, by omega⟩, hcell⟩
    have hinj : Set.InjOn (cell α m) ↑((cuts α m).filter (fun p => cell α m p ≤ r)) := by
      refine (cell_injOn α m).mono ?_
      intro p hp
      rw [Finset.mem_coe, Finset.mem_filter] at hp
      exact Finset.mem_coe.mpr hp.1
    calc cell α m u = ((cuts α m).filter (fun p => cell α m p ≤ r)).card := by
          rw [cell, hfilter]
      _ = (((cuts α m).filter (fun p => cell α m p ≤ r)).image (cell α m)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ = (Finset.Icc 1 r).card := by rw [himg]
      _ = r := by rw [Nat.card_Icc]; omega
  obtain ⟨k, -, h1, h2⟩ :=
    exists_fract_mem_Ico hα x (c := c) (ε := d - c) hc0 (by linarith) (by linarith)
  exact ⟨k, hconst _ h1 (by linarith)⟩

/-! ### Theorem 3.1 -/

/-- **Theorem 3.1.**  A lower coding of an irrational slope has exactly `m + 1`
factors of length `m`: it is Sturmian. -/
theorem complexity (hα : Irrational α) (hα0 : 0 < α) (hα1 : α < 1) (x : ℝ) (m : ℕ) :
    {w : Fin m → ℕ | ∃ k : ℕ, w = factor α x m k}.ncard = m + 1 := by
  have H : ∀ r : ℕ, r ≤ m → ∃ k : ℕ, cell α m (Int.fract (x + (k : ℝ) * α)) = r :=
    fun r hr => exists_cell hα x hr
  choose! K hK using H
  have hinj : Set.InjOn (fun r => factor α x m (K r)) (Set.Iic m) := by
    intro r hr r' hr' h
    rw [factor_eq_iff hα hα0 hα1, hK r hr, hK r' hr'] at h
    exact h
  have hS : {w : Fin m → ℕ | ∃ k : ℕ, w = factor α x m k}
      = (fun r => factor α x m (K r)) '' (Set.Iic m) := by
    ext w
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨cell α m (Int.fract (x + (k : ℝ) * α)), cell_le hα m _, ?_⟩
      rw [factor_eq_iff hα hα0 hα1, hK _ (cell_le hα m _)]
    · rintro ⟨r, hr, rfl⟩
      exact ⟨K r, rfl⟩
  rw [hS, Set.InjOn.ncard_image hinj,
      show (Set.Iic m : Set ℕ) = ↑(Finset.Iic m) by ext; simp,
      Set.ncard_coe_finset, Nat.card_Iic]

/-! ### Corollary 3.2 — the upper coding

The tex proves this by rerunning §3 with `⌈·⌉` for `⌊·⌋`.  That is unnecessary:
`codeUp α x` is the *bitwise complement* of `code (1-α) (-x)`, and
complementation is a bijection on words, so the count is inherited from
Theorem 3.1.  The arc `(1-α,1) ∪ {0}` of the upper coding has complement
`(0,1-α]` in `[0,1)`, and the reflection `v ↦ 1 - v` carries that onto
`[α,1) = [1-(1-α),1)`, the lower arc of slope `1-α`. -/

lemma fract_neg_eq (y : ℝ) :
    Int.fract (-y) = if Int.fract y = 0 then 0 else 1 - Int.fract y := by
  by_cases h : Int.fract y = 0
  · rw [if_pos h]
    have hy : -y = ((-⌊y⌋ : ℤ) : ℝ) := by
      have h2 := Int.floor_add_fract y
      rw [h] at h2
      push_cast
      linarith
    rw [hy, Int.fract_intCast]
  · rw [if_neg h, Int.fract_neg h]

/-- **The upper coding is the complement of a lower coding of the reflected
slope.** -/
theorem codeUp_add_code_reflect (hα0 : 0 < α) (x : ℝ) (k : ℕ) :
    codeUp α x k + code (1 - α) (-x) k = 1 := by
  have hshift : Int.fract (-x + (k : ℝ) * (1 - α)) = Int.fract (-(x + (k : ℝ) * α)) := by
    rw [Int.fract_eq_fract]
    exact ⟨k, by push_cast; ring⟩
  have hv0 := Int.fract_nonneg (x + (k : ℝ) * α)
  have hv1 := Int.fract_lt_one (x + (k : ℝ) * α)
  unfold code codeUp
  rw [hshift, fract_neg_eq]
  by_cases h0 : Int.fract (x + (k : ℝ) * α) = 0
  · rw [if_pos h0, if_pos (Or.inr h0), if_neg (not_le.mpr (by linarith))]
  · rw [if_neg h0]
    by_cases h1 : 1 - α < Int.fract (x + (k : ℝ) * α)
    · rw [if_pos (Or.inl h1), if_neg (not_le.mpr (by linarith))]
    · have h1' := not_lt.mp h1
      rw [if_neg (fun hc => hc.elim (fun hlt => h1 hlt) h0), if_pos (by linarith)]

lemma code_le_one (α x : ℝ) (k : ℕ) : code α x k ≤ 1 := by
  unfold code; split_ifs <;> omega

lemma codeUp_le_one (α x : ℝ) (k : ℕ) : codeUp α x k ≤ 1 := by
  unfold codeUp; split_ifs <;> omega

/-! ### The factor set of an arbitrary sequence -/

/-- The factors of length `m` of a sequence. -/
def factors (ℓ : ℕ → ℕ) (m : ℕ) : Set (Fin m → ℕ) :=
  {w | ∃ k : ℕ, w = fun j : Fin m => ℓ (k + (j : ℕ))}

lemma factors_code (α x : ℝ) (m : ℕ) :
    factors (code α x) m = {w : Fin m → ℕ | ∃ k : ℕ, w = factor α x m k} := rfl

/-- **Theorem 3.1**, in the language of `factors`. -/
theorem ncard_factors_code (hα : Irrational α) (hα0 : 0 < α) (hα1 : α < 1) (x : ℝ) (m : ℕ) :
    (factors (code α x) m).ncard = m + 1 := by
  rw [factors_code]; exact complexity hα hα0 hα1 x m

/-- **Corollary 3.2.** -/
theorem ncard_factors_codeUp (hα : Irrational α) (hα0 : 0 < α) (hα1 : α < 1) (x : ℝ) (m : ℕ) :
    (factors (codeUp α x) m).ncard = m + 1 := by
  have hβ : Irrational (1 - α) := by
    have h := Irrational.intCast_sub hα 1
    simpa using h
  have hcompl : ∀ k : ℕ, codeUp α x k = 1 - code (1 - α) (-x) k := by
    intro k
    have h := codeUp_add_code_reflect hα0 x k
    omega
  have himg : factors (codeUp α x) m
      = (fun w : Fin m → ℕ => fun j => 1 - w j) '' factors (code (1 - α) (-x)) m := by
    ext w
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨fun j : Fin m => code (1 - α) (-x) (k + (j : ℕ)), ⟨k, rfl⟩, ?_⟩
      funext j
      simp only [hcompl]
    · rintro ⟨v, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, by funext j; simp only [hcompl]⟩
  have hinj : Set.InjOn (fun w : Fin m → ℕ => fun j => 1 - w j)
      (factors (code (1 - α) (-x)) m) := by
    rintro v ⟨k, rfl⟩ v' ⟨k', rfl⟩ h
    funext j
    have hj := congrFun h j
    simp only at hj
    have h1 := code_le_one (1 - α) (-x) (k + j)
    have h2 := code_le_one (1 - α) (-x) (k' + j)
    omega
  rw [himg, Set.InjOn.ncard_image hinj]
  exact ncard_factors_code hβ (by linarith) (by linarith) (-x) m

/-! ### Sturmian sequences

The first place in this development where the word *Sturmian* is a Lean
definition rather than a namespace. -/

/-- A sequence is *Sturmian* when it has exactly `m + 1` factors of each
length `m ≥ 1`. -/
def IsSturmian (ℓ : ℕ → ℕ) : Prop := ∀ m : ℕ, 1 ≤ m → (factors ℓ m).ncard = m + 1

theorem isSturmian_code (hα : Irrational α) (hα0 : 0 < α) (hα1 : α < 1) (x : ℝ) :
    IsSturmian (code α x) := fun m _ => ncard_factors_code hα hα0 hα1 x m

theorem isSturmian_codeUp (hα : Irrational α) (hα0 : 0 < α) (hα1 : α < 1) (x : ℝ) :
    IsSturmian (codeUp α x) := fun m _ => ncard_factors_codeUp hα hα0 hα1 x m

/-! ### Right-special factors — `../all-the-proofs.tex` §6 `lem:rs`

The first piece of §6.  `rightSpecial` is a set of words rather than a
predicate because what §6 uses is its cardinality. -/

variable {ℓ : ℕ → ℕ}

/-- The factors of length `m` whose extension by the letter `b` is again a
factor. -/
def extBy (ℓ : ℕ → ℕ) (m b : ℕ) : Set (Fin m → ℕ) :=
  {u | Fin.snoc u b ∈ factors ℓ (m + 1)}

/-- A word of length `m` is *right-special* when both `u0` and `u1` are
factors.  The alphabet is `{0,1}`, so those are all the extensions there are. -/
def rightSpecial (ℓ : ℕ → ℕ) (m : ℕ) : Set (Fin m → ℕ) :=
  extBy ℓ m 0 ∩ extBy ℓ m 1

lemma snoc_factor (k m b : ℕ) (hb : ℓ (k + m) = b) :
    Fin.snoc (fun j : Fin m => ℓ (k + (j : ℕ))) b
      = fun j : Fin (m + 1) => ℓ (k + (j : ℕ)) := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · simp [hb]
  · intro i; simp

lemma extBy_subset (m b : ℕ) : extBy ℓ m b ⊆ factors ℓ m := by
  rintro u ⟨k, hk⟩
  refine ⟨k, ?_⟩
  funext j
  have := congrFun hk j.castSucc
  simpa using this

/-- Binary letters confine the factors of length `m` to a finite set of
functions. -/
lemma factors_finite (hb : ∀ k, ℓ k ≤ 1) (m : ℕ) : (factors ℓ m).Finite := by
  have hsub : factors ℓ m ⊆ Set.pi Set.univ (fun _ : Fin m => Set.Iic 1) := by
    rintro w ⟨k, rfl⟩ j -
    exact hb _
  exact Set.Finite.subset (Set.Finite.pi (fun _ => Set.finite_Iic 1)) hsub

/-- The empty word, and nothing else. -/
lemma ncard_factors_zero (ℓ : ℕ → ℕ) : (factors ℓ 0).ncard = 1 := by
  rw [Set.ncard_eq_one]
  refine ⟨fun j => ℓ (j : ℕ), ?_⟩
  ext w
  simp only [Set.mem_singleton_iff, factors, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, rfl⟩; funext j; exact j.elim0
  · rintro rfl; exact ⟨0, by funext j; exact j.elim0⟩

/-- Every factor has a right extension: it occurs at some `k`, and `ℓ (k+m)`
extends it. -/
lemma extBy_union (hb : ∀ k, ℓ k ≤ 1) (m : ℕ) :
    extBy ℓ m 0 ∪ extBy ℓ m 1 = factors ℓ m := by
  apply Set.Subset.antisymm
  · exact Set.union_subset (extBy_subset m 0) (extBy_subset m 1)
  · rintro u ⟨k, rfl⟩
    have hmem : Fin.snoc (fun j : Fin m => ℓ (k + (j : ℕ))) (ℓ (k + m))
        ∈ factors ℓ (m + 1) := ⟨k, snoc_factor k m _ rfl⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hb (k + m)) with h | h
    · rw [h] at hmem; exact Or.inl hmem
    · rw [h] at hmem; exact Or.inr hmem

/-- **`lem:rs`.**  `F_ℓ(m+1) - F_ℓ(m)` is the number of right-special factors
of length `m`. -/
theorem ncard_factors_succ (hb : ∀ k, ℓ k ≤ 1) (m : ℕ) :
    (factors ℓ (m + 1)).ncard
      = (factors ℓ m).ncard + (rightSpecial ℓ m).ncard := by
  have hinj : ∀ b : ℕ,
      Function.Injective (fun u : Fin m → ℕ => (Fin.snoc u b : Fin (m + 1) → ℕ)) := by
    intro b u v h
    have := congrArg Fin.init h
    simpa [Fin.init_snoc] using this
  have hsplit : factors ℓ (m + 1)
      = (fun u : Fin m → ℕ => (Fin.snoc u 0 : Fin (m + 1) → ℕ)) '' extBy ℓ m 0
        ∪ (fun u : Fin m → ℕ => (Fin.snoc u 1 : Fin (m + 1) → ℕ)) '' extBy ℓ m 1 := by
    apply Set.Subset.antisymm
    · intro w hw
      have hsi : (Fin.snoc (Fin.init w) (w (Fin.last m)) : Fin (m + 1) → ℕ) = w :=
        Fin.snoc_init_self w
      have hlast : w (Fin.last m) ≤ 1 := by
        obtain ⟨k, rfl⟩ := hw; exact hb _
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hlast with h | h
      · rw [h] at hsi
        refine Or.inl ⟨Fin.init w, ?_, hsi⟩
        show (Fin.snoc (Fin.init w) 0 : Fin (m + 1) → ℕ) ∈ factors ℓ (m + 1)
        rw [hsi]; exact hw
      · rw [h] at hsi
        refine Or.inr ⟨Fin.init w, ?_, hsi⟩
        show (Fin.snoc (Fin.init w) 1 : Fin (m + 1) → ℕ) ∈ factors ℓ (m + 1)
        rw [hsi]; exact hw
    · refine Set.union_subset ?_ ?_
      · rintro w ⟨u, hu, rfl⟩; exact hu
      · rintro w ⟨u, hu, rfl⟩; exact hu
  have hdisj : Disjoint
      ((fun u : Fin m → ℕ => (Fin.snoc u 0 : Fin (m + 1) → ℕ)) '' extBy ℓ m 0)
      ((fun u : Fin m → ℕ => (Fin.snoc u 1 : Fin (m + 1) → ℕ)) '' extBy ℓ m 1) := by
    rw [Set.disjoint_left]
    rintro w ⟨u, -, rfl⟩ ⟨v, -, hv⟩
    have := congrFun hv (Fin.last m)
    simp [Fin.snoc_last] at this
  have h0 : (extBy ℓ m 0).Finite := (factors_finite hb m).subset (extBy_subset m 0)
  have h1 : (extBy ℓ m 1).Finite := (factors_finite hb m).subset (extBy_subset m 1)
  rw [hsplit, Set.ncard_union_eq hdisj (h0.image _) (h1.image _),
      Set.ncard_image_of_injective _ (hinj 0),
      Set.ncard_image_of_injective _ (hinj 1),
      rightSpecial, ← extBy_union hb m,
      Set.ncard_union_add_ncard_inter _ _ h0 h1]

/-- **`cor:onesp`.**  Complexity `m + 1` is exactly one right-special factor of
each length. -/
theorem isSturmian_iff_ncard_rightSpecial (hb : ∀ k, ℓ k ≤ 1) :
    IsSturmian ℓ ↔ ∀ m : ℕ, (rightSpecial ℓ m).ncard = 1 := by
  have hzero := ncard_factors_zero ℓ
  constructor
  · intro hS m
    have h1 : (factors ℓ m).ncard = m + 1 := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simpa using hzero
      · exact hS m hm
    have h2 : (factors ℓ (m + 1)).ncard = m + 2 := hS (m + 1) (by omega)
    have := ncard_factors_succ hb m
    omega
  · intro hrs
    have key : ∀ m : ℕ, (factors ℓ m).ncard = m + 1 := by
      intro m
      induction m with
      | zero => simpa using hzero
      | succ n ih => rw [ncard_factors_succ hb n, hrs n, ih]
    exact fun m _ => key m

end Complexity

/-! ## §4 The return time

`a` and `β` are supplied rather than computed: `a = ⌊1/α⌋` and `β = {1/α}` is
the only case used, but the proof needs nothing beyond `(a : ℝ) + β = 1/α`. -/

section ReturnTime

variable {a : ℕ} {β u : ℝ}

/-- The arc `[1-α, 1)` in the coordinate `u`. -/
noncomputable def arc (α u : ℝ) : ℝ := 1 - α + α * u

lemma one_le_of_inv (hα0 : 0 < α) (hα1 : α < 1) (hβ : (a : ℝ) + β = 1/α)
    (hβ1 : β < 1) : 1 ≤ a := by
  have h : 1 < 1/α := by rw [lt_div_iff₀ hα0]; linarith
  have : (0 : ℝ) < a := by linarith
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast this.ne')

lemma mul_ge_one_iff (hα0 : 0 < α) (hβ : (a : ℝ) + β = 1/α) (w : ℝ) :
    1 ≤ α * w ↔ (a : ℝ) + β ≤ w := by
  rw [hβ, div_le_iff₀ hα0]
  constructor <;> intro h <;> linarith

/-- The orbit point after `s` steps from the arc, before it returns. -/
lemma fract_arc (hα0 : 0 < α) {s : ℕ} (hs : 1 ≤ s) (hu0 : 0 ≤ u)
    (hlt : α * (u + s - 1) < 1) :
    Int.fract (arc α u + s * α) = α * (u + (s : ℝ) - 1) := by
  have hs' : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hnn : 0 ≤ α * (u + (s : ℝ) - 1) := mul_nonneg hα0.le (by linarith)
  have hx : arc α u + (s : ℝ) * α = ((1 : ℤ) : ℝ) + α * (u + (s : ℝ) - 1) := by
    unfold arc; push_cast; ring
  rw [hx, Int.fract_intCast_add]
  exact Int.fract_eq_self.mpr ⟨hnn, hlt⟩

/-- **Theorem 4.1.**  The first return to the arc takes `a+1` steps from the
lower part of the arc and `a` steps from the upper part. -/
theorem return_time (hα0 : 0 < α) (hα1 : α < 1) (hβ : (a : ℝ) + β = 1/α)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    IsLeast {t : ℕ | 1 ≤ t ∧ 1 - α ≤ Int.fract (arc α u + t * α)}
            (if u < β then a + 1 else a) := by
  have ha := one_le_of_inv hα0 hα1 hβ hβ1
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have key := mul_ge_one_iff (a := a) (β := β) hα0 hβ
  by_cases hu : u < β
  · rw [if_pos hu]
    have hv : α * (u + ((a + 1 : ℕ) : ℝ) - 1) < 1 := by
      rw [← not_le, key]; push_cast; linarith
    constructor
    · refine ⟨by omega, ?_⟩
      rw [fract_arc hα0 (by omega) hu0 hv]
      have : 1 ≤ α * (u + ((a + 1 : ℕ) : ℝ)) := by rw [key]; push_cast; linarith
      nlinarith
    · intro s hs
      by_contra hlt
      push Not at hlt
      have hs1 : 1 ≤ s := hs.1
      have hsR : (s : ℝ) ≤ (a : ℝ) := by
        have : s ≤ a := by omega
        exact_mod_cast this
      have hsR1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
      have hv' : α * (u + (s : ℝ) - 1) < 1 := by
        rw [← not_le, key]; linarith
      have hfail : α * (u + (s : ℝ)) < 1 := by rw [← not_le, key]; linarith
      have := hs.2
      rw [fract_arc hα0 hs1 hu0 hv'] at this
      nlinarith
  · rw [if_neg hu]
    push Not at hu
    have hv : α * (u + (a : ℝ) - 1) < 1 := by
      rw [← not_le, key]; linarith
    constructor
    · refine ⟨ha, ?_⟩
      rw [fract_arc hα0 ha hu0 hv]
      have : 1 ≤ α * (u + (a : ℝ)) := by rw [key]; linarith
      nlinarith
    · intro s hs
      by_contra hlt
      push Not at hlt
      have hs1 : 1 ≤ s := hs.1
      have hsR : (s : ℝ) + 1 ≤ (a : ℝ) := by
        have : s + 1 ≤ a := by omega
        exact_mod_cast this
      have hsR1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
      have hv' : α * (u + (s : ℝ) - 1) < 1 := by
        rw [← not_le, key]; linarith
      have hfail : α * (u + (s : ℝ)) < 1 := by rw [← not_le, key]; linarith
      have := hs.2
      rw [fract_arc hα0 hs1 hu0 hv'] at this
      nlinarith

end ReturnTime

/-! ## §4.1 The positions of the ones -/

section Ones

variable {a : ℕ} {β : ℝ}

/-- The orbit reaches the arc: a coding has a `1`. -/
lemma exists_one (hα0 : 0 < α) (x : ℝ) :
    ∃ k : ℕ, 1 - α ≤ Int.fract (x + (k : ℝ) * α) := by
  set f := Int.fract x with hf
  have hf0 : 0 ≤ f := Int.fract_nonneg x
  have hf1 : f < 1 := Int.fract_lt_one x
  set c : ℝ := (1 - f) / α with hc
  have hcpos : 0 < c := div_pos (by linarith) hα0
  have hceil : 1 ≤ ⌈c⌉₊ := Nat.one_le_ceil_iff.mpr hcpos
  refine ⟨⌈c⌉₊ - 1, ?_⟩
  have hsucc : (⌈c⌉₊ - 1) + 1 = ⌈c⌉₊ := by omega
  have hlt : ((⌈c⌉₊ - 1 : ℕ) : ℝ) < c := by
    rw [← Nat.lt_ceil]; omega
  have hge : c ≤ (((⌈c⌉₊ - 1 : ℕ) : ℝ) + 1) := by
    have := Nat.le_ceil c
    rw [← hsucc] at this
    push_cast at this
    linarith
  have h1 : f + ((⌈c⌉₊ - 1 : ℕ) : ℝ) * α < 1 := by
    rw [hc, lt_div_iff₀ hα0] at hlt; linarith
  have h2 : 1 - α ≤ f + ((⌈c⌉₊ - 1 : ℕ) : ℝ) * α := by
    rw [hc, div_le_iff₀ hα0] at hge; linarith
  have hnn : 0 ≤ f + ((⌈c⌉₊ - 1 : ℕ) : ℝ) * α :=
    add_nonneg hf0 (mul_nonneg (Nat.cast_nonneg _) hα0.le)
  have hval : Int.fract (x + ((⌈c⌉₊ - 1 : ℕ) : ℝ) * α) = f + ((⌈c⌉₊ - 1 : ℕ) : ℝ) * α := by
    rw [fract_add_left, ← hf]
    exact Int.fract_eq_self.mpr ⟨hnn, h1⟩
  rw [hval]
  exact h2

/-- There are infinitely many `1`s. -/
lemma setOf_one_infinite (hα0 : 0 < α) (x : ℝ) :
    {k : ℕ | code α x k = 1}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨k, hk⟩ := exists_one hα0 (Int.fract (x + ((N + 1 : ℕ) : ℝ) * α))
  have hmem : (N + 1 + k) ∈ {k : ℕ | code α x k = 1} := by
    have : Int.fract (x + ((N + 1 + k : ℕ) : ℝ) * α)
        = Int.fract (Int.fract (x + ((N + 1 : ℕ) : ℝ) * α) + (k : ℝ) * α) :=
      fract_orbit_add α x (N + 1) k
    simp only [Set.mem_setOf_eq, code, this]
    rw [if_pos (by rw [← fract_add_left] at hk ⊢; exact hk)]
  have := hN hmem
  omega


/-- The gap between consecutive members of an infinite set, from a least-element
statement.  Shared by the two codings. -/
lemma nth_succ_eq {p : ℕ → Prop} (hp : {k | p k}.Infinite) (i t₀ : ℕ)
    (h : IsLeast {t : ℕ | 1 ≤ t ∧ p (Nat.nth p i + t)} t₀) :
    Nat.nth p (i + 1) = Nat.nth p i + t₀ := by
  obtain ⟨⟨ht1, htmem⟩, hmin⟩ := h
  have hgt : Nat.nth p i < Nat.nth p (i + 1) := Nat.nth_strictMono hp (Nat.lt_succ_self i)
  have hmem : p (Nat.nth p (i + 1)) := Nat.nth_mem_of_infinite hp _
  have hup : Nat.nth p (i + 1) ≤ Nat.nth p i + t₀ := by
    by_contra hc
    push Not at hc
    have := Nat.le_nth_of_lt_nth_succ (p := p) hc htmem
    omega
  have hs : Nat.nth p (i + 1) = Nat.nth p i + (Nat.nth p (i + 1) - Nat.nth p i) := by omega
  have hle := hmin (show (Nat.nth p (i + 1) - Nat.nth p i) ∈
    {t : ℕ | 1 ≤ t ∧ p (Nat.nth p i + t)} from ⟨by omega, by rw [← hs]; exact hmem⟩)
  omega

/-- The position of the `i`-th `1`. -/
noncomputable def ones (α x : ℝ) (i : ℕ) : ℕ := Nat.nth (fun k => code α x k = 1) i

lemma code_ones (hα0 : 0 < α) (x : ℝ) (i : ℕ) : code α x (ones α x i) = 1 :=
  Nat.nth_mem_of_infinite (setOf_one_infinite hα0 x) i

lemma ones_lt_succ (hα0 : 0 < α) (x : ℝ) (i : ℕ) :
    ones α x i < ones α x (i + 1) :=
  Nat.nth_strictMono (setOf_one_infinite hα0 x) (Nat.lt_succ_self i)

/-- Nothing between consecutive `1`s is a `1`. -/
lemma ones_succ_le (x : ℝ) {i m : ℕ}
    (hm : code α x m = 1) (hlt : ones α x i < m) : ones α x (i + 1) ≤ m := by
  by_contra h
  push Not at h
  have := Nat.le_nth_of_lt_nth_succ (p := fun k => code α x k = 1) h hm
  simp only [ones] at hlt
  omega

end Ones

/-! ## §4.2 Gaps and the derived sequence -/

section Derived

variable {a : ℕ} {β : ℝ}

lemma le_fract_of_code_one {k : ℕ} (h : code α x k = 1) :
    1 - α ≤ Int.fract (x + (k : ℝ) * α) := by
  by_contra hc
  rw [code, if_neg hc] at h
  exact absurd h (by norm_num)

/-- The coordinate of the `i`-th `1` inside the arc. -/
noncomputable def coord (α x : ℝ) (i : ℕ) : ℝ :=
  (Int.fract (x + (ones α x i : ℝ) * α) - (1 - α)) / α

lemma fract_ones (hα0 : 0 < α) (x : ℝ) (i : ℕ) :
    Int.fract (x + (ones α x i : ℝ) * α) = arc α (coord α x i) := by
  unfold arc coord
  field_simp
  ring

lemma coord_nonneg (hα0 : 0 < α) (x : ℝ) (i : ℕ) : 0 ≤ coord α x i := by
  have h := le_fract_of_code_one (code_ones hα0 x i)
  unfold coord
  exact div_nonneg (by linarith) hα0.le

lemma coord_lt_one (hα0 : 0 < α) (x : ℝ) (i : ℕ) : coord α x i < 1 := by
  have h := Int.fract_lt_one (x + (ones α x i : ℝ) * α)
  unfold coord
  rw [div_lt_one hα0]
  linarith

lemma code_add_iff (hα0 : 0 < α) (x : ℝ) (i t : ℕ) :
    code α x (ones α x i + t) = 1
      ↔ 1 - α ≤ Int.fract (arc α (coord α x i) + (t : ℝ) * α) := by
  rw [code, fract_orbit_add, fract_ones hα0]
  constructor
  · intro h
    by_contra hc
    rw [if_neg hc] at h
    exact absurd h (by norm_num)
  · intro h
    rw [if_pos h]

/-- **Corollary 4.2.**  Consecutive `1`s are `a` or `a+1` apart. -/
theorem ones_succ_eq (hα0 : 0 < α) (hα1 : α < 1) (hβ : (a : ℝ) + β = 1/α)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (x : ℝ) (i : ℕ) :
    ones α x (i + 1) = ones α x i + (if coord α x i < β then a + 1 else a) := by
  refine nth_succ_eq (setOf_one_infinite hα0 x) i _ ?_
  obtain ⟨⟨ht1, htmem⟩, hmin⟩ :=
    return_time hα0 hα1 hβ hβ0 hβ1 (coord_nonneg hα0 x i) (coord_lt_one hα0 x i)
  constructor
  · exact ⟨ht1, (code_add_iff hα0 x i _).mpr htmem⟩
  · intro t ht
    exact hmin ⟨ht.1, (code_add_iff hα0 x i t).mp ht.2⟩

/-- The derived sequence: `1` when the gap is `a+1`, `0` when it is `a`. -/
noncomputable def derived (α x : ℝ) (a : ℕ) (i : ℕ) : ℕ :=
  ones α x (i + 1) - ones α x i - a

/-- **The derived letter reads the coordinate.**  This is the bridge to §5. -/
theorem derived_eq (hα0 : 0 < α) (hα1 : α < 1) (hβ : (a : ℝ) + β = 1/α)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (x : ℝ) (i : ℕ) :
    derived α x a i = if coord α x i < β then 1 else 0 := by
  unfold derived
  rw [ones_succ_eq hα0 hα1 hβ hβ0 hβ1 x i]
  split_ifs <;> omega

/-! ### The block decomposition — `../all-the-proofs.tex` Lemma 4.3

Positionally: block `i` starts at `ones α x i`, has length `a + ℓ'ᵢ`, opens with
a `1`, and is otherwise `0`.  With `ones α x 0 = k₀` that is
`ℓ = 0^{k₀} · τ_a(ℓ')`. -/

/-- Block `i` has length `a + ℓ'ᵢ`. -/
theorem block_length (hα0 : 0 < α) (hα1 : α < 1) (hβ : (a : ℝ) + β = 1 / α)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (x : ℝ) (i : ℕ) :
    ones α x (i + 1) = ones α x i + (a + derived α x a i) := by
  have h := ones_succ_eq hα0 hα1 hβ hβ0 hβ1 x i
  have hd := derived_eq hα0 hα1 hβ hβ0 hβ1 x i
  rw [hd]
  split_ifs at h ⊢ <;> omega

/-- Inside a block there are only zeros. -/
theorem block_zero (x : ℝ) (i j : ℕ) (hj0 : 0 < j)
    (hj : ones α x i + j < ones α x (i + 1)) : code α x (ones α x i + j) = 0 := by
  have h1 : code α x (ones α x i + j) ≤ 1 := code_le_one α x _
  by_contra hc
  have he : code α x (ones α x i + j) = 1 := by omega
  have := ones_succ_le (i := i) x he (by omega)
  omega

end Derived

/-! ## §5 The derivation theorem -/

section Derivation

variable {a : ℕ} {β u : ℝ}

/-- The second half of Theorem 4.1: the first return rotates the coordinate by `1 - β`. -/
lemma coord_step (hα0 : 0 < α) (hα1 : α < 1) (hβ : (a : ℝ) + β = 1/α)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (Int.fract (arc α u + ((if u < β then a + 1 else a : ℕ) : ℝ) * α) - (1 - α)) / α
      = Int.fract (u + 1 - β) := by
  have ha := one_le_of_inv hα0 hα1 hβ hβ1
  have key := mul_ge_one_iff (a := a) (β := β) hα0 hβ
  have hmul : α * ((a : ℝ) + β) = 1 := by rw [hβ]; field_simp
  by_cases hu : u < β
  · rw [if_pos hu]
    have hv : α * (u + ((a + 1 : ℕ) : ℝ) - 1) < 1 := by
      rw [← not_le, key]; push_cast; linarith
    rw [fract_arc hα0 (by omega) hu0 hv,
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    rw [div_eq_iff hα0.ne']
    push_cast
    linear_combination hmul
  · push Not at hu
    rw [if_neg (by linarith)]
    have hv : α * (u + ((a : ℕ) : ℝ) - 1) < 1 := by
      rw [← not_le, key]; linarith
    have hfr : Int.fract (u + 1 - β) = u - β := by
      have : u + 1 - β = (u - β) + 1 := by ring
      rw [this, Int.fract_add_one]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [fract_arc hα0 ha hu0 hv, hfr, div_eq_iff hα0.ne']
    linear_combination hmul

/-- The coordinates of the `1`s rotate by `1 - β`. -/
theorem coord_succ (hα0 : 0 < α) (hα1 : α < 1) (hβ : (a : ℝ) + β = 1/α)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (x : ℝ) (i : ℕ) :
    coord α x (i + 1) = Int.fract (coord α x i + 1 - β) := by
  have h := ones_succ_eq hα0 hα1 hβ hβ0 hβ1 x i
  have hfr : Int.fract (x + (ones α x (i + 1) : ℝ) * α)
      = Int.fract (arc α (coord α x i)
          + ((if coord α x i < β then a + 1 else a : ℕ) : ℝ) * α) := by
    rw [h, fract_orbit_add, fract_ones hα0]
  calc coord α x (i + 1)
      = (Int.fract (x + (ones α x (i + 1) : ℝ) * α) - (1 - α)) / α := rfl
    _ = _ := by rw [hfr]; exact coord_step hα0 hα1 hβ hβ0 hβ1
                  (coord_nonneg hα0 x i) (coord_lt_one hα0 x i)

/-- The reflected coordinate, which rotates by `β`. -/
noncomputable def refl (α x : ℝ) (i : ℕ) : ℝ := Int.fract (-(coord α x i))

theorem refl_succ (hα0 : 0 < α) (hα1 : α < 1) (hβ : (a : ℝ) + β = 1/α)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (x : ℝ) (i : ℕ) :
    refl α x (i + 1) = Int.fract (refl α x i + β) := by
  unfold refl
  have h1 : Int.fract (-(Int.fract (coord α x i + 1 - β)))
      = Int.fract (-(coord α x i) + β) := by
    rw [Int.fract_eq_fract]
    refine ⟨⌊coord α x i + 1 - β⌋ - 1, ?_⟩
    rw [Int.fract]
    push_cast
    ring
  have h2 : Int.fract (Int.fract (-(coord α x i)) + β) = Int.fract (-(coord α x i) + β) :=
    (fract_add_left (-(coord α x i)) β).symm
  rw [coord_succ hα0 hα1 hβ hβ0 hβ1 x i, h1, h2]

theorem refl_eq (hα0 : 0 < α) (hα1 : α < 1) (hβ : (a : ℝ) + β = 1/α)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (x : ℝ) : ∀ i : ℕ,
    refl α x i = Int.fract (refl α x 0 + (i : ℝ) * β)
  | 0 => by simp [refl]
  | (i + 1) => by
      rw [refl_succ hα0 hα1 hβ hβ0 hβ1 x i, refl_eq hα0 hα1 hβ hβ0 hβ1 x i,
        ← fract_add_left]
      congr 1
      push_cast
      ring

/-- **Theorem 5.1.**  Deriving a lower coding gives an upper coding of slope `β`. -/
theorem derive_code (hα0 : 0 < α) (hα1 : α < 1) (hβ : (a : ℝ) + β = 1/α)
    (hβ0 : 0 < β) (hβ1 : β < 1) (x : ℝ) :
    derived α x a = codeUp β (refl α x 0) := by
  funext i
  rw [derived_eq hα0 hα1 hβ hβ0.le hβ1 x i]
  unfold codeUp
  rw [← refl_eq hα0 hα1 hβ hβ0.le hβ1 x i]
  have hu0 := coord_nonneg hα0 x i
  have hu1 := coord_lt_one hα0 x i
  have hiff : coord α x i < β ↔ (1 - β < refl α x i ∨ refl α x i = 0) := by
    unfold refl
    rcases eq_or_lt_of_le hu0 with h | h
    · rw [← h]
      simp only [neg_zero, Int.fract_zero, or_true, iff_true]
      exact hβ0
    · have hval : Int.fract (-(coord α x i)) = 1 - coord α x i := by
        rw [show -(coord α x i) = (1 - coord α x i) + ((-1 : ℤ) : ℝ) by push_cast; ring,
          Int.fract_add_intCast]
        exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      rw [hval]
      constructor
      · intro h1; exact Or.inl (by linarith)
      · rintro (h1 | h1) <;> linarith
  by_cases hc : coord α x i < β
  · rw [if_pos hc, if_pos (hiff.mp hc)]
  · rw [if_neg hc, if_neg (fun h => hc (hiff.mpr h))]

end Derivation

/-! ## §5.2 The upper arc

Deriving an upper coding gives a *lower* coding.  The arc is `(1-α, 1]`, so the
coordinate runs over `(0,1]` and the value `1` is the orbit point `0` — the one
place where the two codings differ, and the reason this is not a corollary of
§5.1. -/

section Upper

variable {a : ℕ} {β u : ℝ}

lemma mul_gt_one_iff (hα0 : 0 < α) (hβ : (a : ℝ) + β = 1/α) (w : ℝ) :
    1 < α * w ↔ (a : ℝ) + β < w := by
  rw [hβ, div_lt_iff₀ hα0]
  constructor <;> intro h <;> linarith

/-- The upper letter rule on the first lap. -/
lemma letterUp_iff (hα0 : 0 < α) {s : ℕ} (hs : 1 ≤ s) (hu0 : 0 < u)
    (hle : α * (u + (s : ℝ) - 1) ≤ 1) :
    (1 - α < Int.fract (arc α u + (s : ℝ) * α) ∨ Int.fract (arc α u + (s : ℝ) * α) = 0)
      ↔ 1 < α * (u + (s : ℝ)) := by
  have hs' : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hpos : 0 < α * (u + (s : ℝ) - 1) := mul_pos hα0 (by linarith)
  rcases lt_or_eq_of_le hle with hlt | heq
  · rw [fract_arc hα0 hs hu0.le hlt]
    constructor
    · rintro (h | h)
      · nlinarith
      · linarith
    · intro h; left; nlinarith
  · have hz : Int.fract (arc α u + (s : ℝ) * α) = 0 := by
      have hval : arc α u + (s : ℝ) * α = ((2 : ℤ) : ℝ) := by
        unfold arc; push_cast; linear_combination heq
      rw [hval, Int.fract_intCast]
    rw [hz]
    constructor
    · intro _; nlinarith
    · intro _; right; rfl

/-- **Theorem 4.1 for the upper arc.** -/
theorem return_timeUp (hα0 : 0 < α) (hα1 : α < 1) (hβ : (a : ℝ) + β = 1/α)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    IsLeast {t : ℕ | 1 ≤ t ∧ (1 - α < Int.fract (arc α u + (t : ℝ) * α)
                              ∨ Int.fract (arc α u + (t : ℝ) * α) = 0)}
            (if u ≤ β then a + 1 else a) := by
  have ha := one_le_of_inv hα0 hα1 hβ hβ1
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have key := mul_gt_one_iff (a := a) (β := β) hα0 hβ
  by_cases hu : u ≤ β
  · rw [if_pos hu]
    have hle : α * (u + ((a + 1 : ℕ) : ℝ) - 1) ≤ 1 := by
      rw [← not_lt, key]; push_cast; linarith
    constructor
    · refine ⟨by omega, ?_⟩
      rw [letterUp_iff hα0 (by omega) hu0 hle, key]
      push_cast; linarith
    · intro s hs
      by_contra hlt
      push Not at hlt
      have hs1 : 1 ≤ s := hs.1
      have hsR : (s : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show s ≤ a by omega)
      have hsR1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
      have hle' : α * (u + (s : ℝ) - 1) ≤ 1 := by rw [← not_lt, key]; linarith
      have hc := (letterUp_iff hα0 hs1 hu0 hle').mp hs.2
      rw [key] at hc
      linarith
  · rw [if_neg hu]
    push Not at hu
    have hle : α * (u + ((a : ℕ) : ℝ) - 1) ≤ 1 := by
      rw [← not_lt, key]; linarith
    constructor
    · refine ⟨ha, ?_⟩
      rw [letterUp_iff hα0 ha hu0 hle, key]
      linarith
    · intro s hs
      by_contra hlt
      push Not at hlt
      have hs1 : 1 ≤ s := hs.1
      have hsR : (s : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast (show s + 1 ≤ a by omega)
      have hsR1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
      have hle' : α * (u + (s : ℝ) - 1) ≤ 1 := by rw [← not_lt, key]; linarith
      have hc := (letterUp_iff hα0 hs1 hu0 hle').mp hs.2
      rw [key] at hc
      linarith

/-! ### The positions of the ones of an upper coding -/

lemma le_fract_of_codeUp_one {k : ℕ} (h : codeUp α x k = 1) :
    1 - α < Int.fract (x + (k : ℝ) * α) ∨ Int.fract (x + (k : ℝ) * α) = 0 := by
  by_contra hc
  rw [codeUp, if_neg hc] at h
  exact absurd h (by norm_num)

lemma exists_oneUp (hα0 : 0 < α) (x : ℝ) :
    ∃ k : ℕ, (1 - α < Int.fract (x + (k : ℝ) * α) ∨ Int.fract (x + (k : ℝ) * α) = 0) := by
  obtain ⟨k, hk⟩ := exists_one hα0 x
  rcases lt_or_eq_of_le hk with h | h
  · exact ⟨k, Or.inl h⟩
  · refine ⟨k + 1, Or.inr ?_⟩
    rw [fract_orbit_succ, ← h]
    simp

lemma setOf_oneUp_infinite (hα0 : 0 < α) (x : ℝ) : {k : ℕ | codeUp α x k = 1}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨k, hk⟩ := exists_oneUp hα0 (Int.fract (x + ((N + 1 : ℕ) : ℝ) * α))
  have hmem : (N + 1 + k) ∈ {k : ℕ | codeUp α x k = 1} := by
    have hf : Int.fract (x + ((N + 1 + k : ℕ) : ℝ) * α)
        = Int.fract (Int.fract (x + ((N + 1 : ℕ) : ℝ) * α) + (k : ℝ) * α) :=
      fract_orbit_add α x (N + 1) k
    simp only [Set.mem_setOf_eq, codeUp, hf]
    rw [if_pos (by rw [← fract_add_left] at hk ⊢; exact hk)]
  have := hN hmem
  omega

/-- The position of the `i`-th `1` of an upper coding. -/
noncomputable def onesUp (α x : ℝ) (i : ℕ) : ℕ := Nat.nth (fun k => codeUp α x k = 1) i

lemma codeUp_onesUp (hα0 : 0 < α) (x : ℝ) (i : ℕ) : codeUp α x (onesUp α x i) = 1 :=
  Nat.nth_mem_of_infinite (setOf_oneUp_infinite hα0 x) i

/-- The coordinate on the upper arc, with `1` denoting the orbit point `0`. -/
noncomputable def coordUp (α x : ℝ) (i : ℕ) : ℝ :=
  if Int.fract (x + (onesUp α x i : ℝ) * α) = 0 then 1
  else (Int.fract (x + (onesUp α x i : ℝ) * α) - (1 - α)) / α

lemma coordUp_pos (hα0 : 0 < α) (x : ℝ) (i : ℕ) : 0 < coordUp α x i := by
  unfold coordUp
  split_ifs with h
  · norm_num
  · rcases le_fract_of_codeUp_one (codeUp_onesUp hα0 x i) with h1 | h1
    · exact div_pos (by linarith) hα0
    · exact absurd h1 h

lemma coordUp_le_one (hα0 : 0 < α) (x : ℝ) (i : ℕ) : coordUp α x i ≤ 1 := by
  unfold coordUp
  split_ifs with h
  · exact le_refl 1
  · have := Int.fract_lt_one (x + (onesUp α x i : ℝ) * α)
    rw [div_le_one hα0]
    linarith

lemma fract_onesUp (hα0 : 0 < α) (x : ℝ) (i : ℕ) :
    Int.fract (x + (onesUp α x i : ℝ) * α) = Int.fract (arc α (coordUp α x i)) := by
  unfold coordUp
  split_ifs with h
  · rw [h, show arc α 1 = 1 by unfold arc; ring]
    simp
  · have h0 := Int.fract_nonneg (x + (onesUp α x i : ℝ) * α)
    have h1 := Int.fract_lt_one (x + (onesUp α x i : ℝ) * α)
    have : arc α ((Int.fract (x + (onesUp α x i : ℝ) * α) - (1 - α)) / α)
        = Int.fract (x + (onesUp α x i : ℝ) * α) := by
      unfold arc; field_simp; ring
    rw [this, Int.fract_eq_self.mpr ⟨h0, h1⟩]

lemma codeUp_add_iff (hα0 : 0 < α) (x : ℝ) (i t : ℕ) :
    codeUp α x (onesUp α x i + t) = 1
      ↔ (1 - α < Int.fract (arc α (coordUp α x i) + (t : ℝ) * α)
          ∨ Int.fract (arc α (coordUp α x i) + (t : ℝ) * α) = 0) := by
  rw [codeUp, fract_orbit_add, fract_onesUp hα0, ← fract_add_left]
  constructor
  · intro h
    by_contra hc
    rw [if_neg hc] at h
    exact absurd h (by norm_num)
  · intro h
    rw [if_pos h]

theorem onesUp_succ_eq (hα0 : 0 < α) (hα1 : α < 1) (hβ : (a : ℝ) + β = 1/α)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (x : ℝ) (i : ℕ) :
    onesUp α x (i + 1) = onesUp α x i + (if coordUp α x i ≤ β then a + 1 else a) := by
  refine nth_succ_eq (setOf_oneUp_infinite hα0 x) i _ ?_
  obtain ⟨⟨ht1, htmem⟩, hmin⟩ :=
    return_timeUp hα0 hα1 hβ hβ0 hβ1 (coordUp_pos hα0 x i) (coordUp_le_one hα0 x i)
  exact ⟨⟨ht1, (codeUp_add_iff hα0 x i _).mpr htmem⟩,
    fun t ht => hmin ⟨ht.1, (codeUp_add_iff hα0 x i t).mp ht.2⟩⟩

/-- The derived sequence of an upper coding. -/
noncomputable def derivedUp (α x : ℝ) (a : ℕ) (i : ℕ) : ℕ :=
  onesUp α x (i + 1) - onesUp α x i - a

theorem derivedUp_eq (hα0 : 0 < α) (hα1 : α < 1) (hβ : (a : ℝ) + β = 1/α)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (x : ℝ) (i : ℕ) :
    derivedUp α x a i = if coordUp α x i ≤ β then 1 else 0 := by
  unfold derivedUp
  rw [onesUp_succ_eq hα0 hα1 hβ hβ0 hβ1 x i]
  split_ifs <;> omega

/-! ### The reflected coordinate -/

theorem coordUp_succ (hα0 : 0 < α) (hα1 : α < 1) (hβ : (a : ℝ) + β = 1/α)
    (hβ0 : 0 < β) (hβ1 : β < 1) (x : ℝ) (i : ℕ) :
    coordUp α x (i + 1)
      = if coordUp α x i ≤ β then coordUp α x i + 1 - β else coordUp α x i - β := by
  have hu0 := coordUp_pos hα0 x i
  have hu1 := coordUp_le_one hα0 x i
  have ha := one_le_of_inv hα0 hα1 hβ hβ1
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have key := mul_gt_one_iff (a := a) (β := β) hα0 hβ
  have keyle := mul_ge_one_iff (a := a) (β := β) hα0 hβ
  have hmul : α * ((a : ℝ) + β) = 1 := by rw [hβ]; field_simp
  have hpos := onesUp_succ_eq hα0 hα1 hβ hβ0.le hβ1 x i
  have hfr : Int.fract (x + (onesUp α x (i + 1) : ℝ) * α)
      = Int.fract (arc α (coordUp α x i)
          + ((if coordUp α x i ≤ β then a + 1 else a : ℕ) : ℝ) * α) := by
    rw [hpos, fract_orbit_add, fract_onesUp hα0, ← fract_add_left]
  show (if Int.fract (x + (onesUp α x (i + 1) : ℝ) * α) = 0 then 1
        else (Int.fract (x + (onesUp α x (i + 1) : ℝ) * α) - (1 - α)) / α) = _
  rw [hfr]
  by_cases hu : coordUp α x i ≤ β
  · simp only [if_pos hu]
    have hle : α * (coordUp α x i + ((a + 1 : ℕ) : ℝ) - 1) ≤ 1 := by
      rw [← not_lt, key]; push_cast; linarith
    rcases eq_or_lt_of_le hle with heq | hlt
    · have hval : arc α (coordUp α x i) + ((a + 1 : ℕ) : ℝ) * α = ((2 : ℤ) : ℝ) := by
        unfold arc; push_cast; push_cast at heq; linear_combination heq
      rw [hval, Int.fract_intCast, if_pos rfl]
      have hz : α * (coordUp α x i - β) = 0 := by push_cast at heq; linear_combination heq - hmul
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h hα0.ne'
      · linarith
    · have hv := fract_arc hα0 (show 1 ≤ a + 1 by omega) hu0.le hlt
      have hgt : 0 < α * (coordUp α x i + ((a + 1 : ℕ) : ℝ) - 1) := by
        refine mul_pos hα0 ?_; push_cast; linarith
      rw [hv, if_neg (ne_of_gt hgt), div_eq_iff hα0.ne']
      push_cast
      linear_combination hmul
  · simp only [if_neg hu]
    push Not at hu
    have hlt : α * (coordUp α x i + ((a : ℕ) : ℝ) - 1) < 1 := by
      rw [← not_le, keyle]; push Not; linarith
    have hv := fract_arc hα0 ha hu0.le hlt
    have hgt : 0 < α * (coordUp α x i + ((a : ℕ) : ℝ) - 1) := by
      refine mul_pos hα0 ?_; linarith
    rw [hv, if_neg (ne_of_gt hgt), div_eq_iff hα0.ne']
    linear_combination hmul

/-- The reflection that turns the upper arc into a lower coding. -/
noncomputable def reflUp (α x : ℝ) (i : ℕ) : ℝ := 1 - coordUp α x i

theorem reflUp_succ (hα0 : 0 < α) (hα1 : α < 1) (hβ : (a : ℝ) + β = 1/α)
    (hβ0 : 0 < β) (hβ1 : β < 1) (x : ℝ) (i : ℕ) :
    reflUp α x (i + 1) = Int.fract (reflUp α x i + β) := by
  have hu0 := coordUp_pos hα0 x i
  have hu1 := coordUp_le_one hα0 x i
  unfold reflUp
  rw [coordUp_succ hα0 hα1 hβ hβ0 hβ1 x i]
  by_cases hu : coordUp α x i ≤ β
  · rw [if_pos hu]
    have hb0 : (0 : ℝ) ≤ 1 - coordUp α x i + β - 1 := by linarith
    have hb1 : 1 - coordUp α x i + β - 1 < 1 := by linarith
    have hval : Int.fract (1 - coordUp α x i + β) = 1 - coordUp α x i + β - 1 := by
      have h2 : (1 - coordUp α x i + β) = (1 - coordUp α x i + β - 1) + ((1 : ℤ) : ℝ) := by
        push_cast; ring
      rw [h2, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨hb0, hb1⟩]
      ring
    rw [hval]; ring
  · rw [if_neg hu]
    push Not at hu
    rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    ring

theorem reflUp_eq (hα0 : 0 < α) (hα1 : α < 1) (hβ : (a : ℝ) + β = 1/α)
    (hβ0 : 0 < β) (hβ1 : β < 1) (x : ℝ) : ∀ i : ℕ,
    reflUp α x i = Int.fract (reflUp α x 0 + (i : ℝ) * β)
  | 0 => by
      have h0 := coordUp_pos hα0 x 0
      have h1 := coordUp_le_one hα0 x 0
      simp only [Nat.cast_zero, zero_mul, add_zero]
      exact (Int.fract_eq_self.mpr ⟨by unfold reflUp; linarith, by unfold reflUp; linarith⟩).symm
  | (i + 1) => by
      rw [reflUp_succ hα0 hα1 hβ hβ0 hβ1 x i, reflUp_eq hα0 hα1 hβ hβ0 hβ1 x i,
        ← fract_add_left]
      congr 1
      push_cast
      ring

/-- **Theorem 5.1, second half.**  Deriving an upper coding gives a lower coding
of slope `β`. -/
theorem derive_codeUp (hα0 : 0 < α) (hα1 : α < 1) (hβ : (a : ℝ) + β = 1/α)
    (hβ0 : 0 < β) (hβ1 : β < 1) (x : ℝ) :
    derivedUp α x a = code β (reflUp α x 0) := by
  funext i
  rw [derivedUp_eq hα0 hα1 hβ hβ0.le hβ1 x i]
  unfold code
  rw [← reflUp_eq hα0 hα1 hβ hβ0 hβ1 x i]
  by_cases hc : coordUp α x i ≤ β
  · rw [if_pos hc, if_pos (by unfold reflUp; linarith)]
  · push Not at hc
    rw [if_neg (by linarith), if_neg (by unfold reflUp; push Not; linarith)]


end Upper

/-! ## §6 Morse and Hedlund — the statement in `sturmian.tex` is false

`sturmian.tex` §2 asserts that every Sturmian sequence is `code α' x` for some
irrational `α'` and some `x ∈ [0,1)`.  Prefixing a `1` to the Fibonacci
sequence gives an upper coding that is not a lower coding of anything. -/

/-- `ℓ` with a `1` prefixed. -/
def cons1 (ℓ : ℕ → ℕ) : ℕ → ℕ := fun k => if k = 0 then 1 else ℓ (k - 1)

/-- The upper coding at the fixed point `0` is a lower coding with a `1` prefixed. -/
theorem codeUp_zero_eq (hα : Irrational α) (hα0 : 0 < α) (hα1 : α < 1) :
    codeUp α 0 = cons1 (code α α) := by
  have hne : ∀ k : ℕ, Int.fract (α + (k : ℝ) * α) ≠ 0 := by
    intro k
    have e : α + (k : ℝ) * α = ((k + 1 : ℕ) : ℝ) * α := by push_cast; ring
    rw [e]
    exact fract_nat_mul_ne_zero hα (by omega)
  funext k
  match k with
  | 0 => simp [codeUp, cons1]
  | (m + 1) =>
      have h : Int.fract ((0 : ℝ) + α) = α := by
        rw [zero_add]; exact Int.fract_eq_self.mpr ⟨le_of_lt hα0, hα1⟩
      simp only [cons1, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      rw [codeUp_succ, h, ← code_eq_codeUp hne]

/-- Counting the ones: the prefixed sequence carries `1 + ⌊Nα⌋` of them. -/
lemma sum_cons1 (hα0 : 0 < α) (hα1 : α < 1) (M : ℕ) :
    ∑ k ∈ Finset.range (M + 1), (cons1 (code α α) k : ℤ) = 1 + ⌊((M : ℝ) + 1) * α⌋ := by
  have h2 : ∑ k ∈ Finset.range M, (code α α k : ℤ) = ⌊(M : ℝ) * α + α⌋ :=
    sum_code hα0 hα1 (le_of_lt hα0) hα1 M
  rw [Finset.sum_range_succ']
  have h3 : ∀ i ∈ Finset.range M, ((cons1 (code α α) (i + 1) : ℕ) : ℤ) = (code α α i : ℤ) := by
    intro i _; simp [cons1]
  rw [Finset.sum_congr rfl h3, h2]
  have : (M : ℝ) * α + α = ((M : ℝ) + 1) * α := by ring
  rw [this, cons1]
  simp
  ring

/-- `1` followed by the coding of slope `α` at `α` is not a lower coding. -/
theorem not_code (hα : Irrational α) (hα0 : 0 < α) (hα1 : α < 1) :
    ¬ ∃ α' x : ℝ, 0 < α' ∧ α' < 1 ∧ 0 ≤ x ∧ x < 1 ∧ cons1 (code α α) = code α' x := by
  rintro ⟨α', x, hα'0, hα'1, hx0, hx1, heq⟩
  -- Lemma 1.4 on both sides
  have hsum : ∀ M : ℕ, ⌊((M : ℝ) + 1) * α' + x⌋ = 1 + ⌊((M : ℝ) + 1) * α⌋ := by
    intro M
    have h1 : ∑ k ∈ Finset.range (M + 1), (code α' x k : ℤ) = ⌊((M + 1 : ℕ) : ℝ) * α' + x⌋ :=
      sum_code hα'0 hα'1 hx0 hx1 (M + 1)
    rw [← heq, sum_cons1 hα0 hα1 M] at h1
    push_cast at h1
    exact h1.symm
  -- the slopes agree, by the Archimedean property
  have hslope : α' = α := by
    by_contra hne
    have hdpos : 0 < |α' - α| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨m, hm⟩ := exists_nat_gt (2 / |α' - α|)
    set N : ℝ := (m : ℝ) + 1 with hNdef
    have hNm : 2 / |α' - α| < N := by rw [hNdef]; linarith
    have hgt : 2 < N * |α' - α| := by
      rw [div_lt_iff₀ hdpos] at hNm; linarith
    have hb := hsum m
    have f1 : ((⌊N * α⌋ : ℤ) : ℝ) ≤ N * α := Int.floor_le _
    have f2 : N * α < (⌊N * α⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have g1 : ((⌊N * α' + x⌋ : ℤ) : ℝ) ≤ N * α' + x := Int.floor_le _
    have g2 : N * α' + x < (⌊N * α' + x⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    rw [hb] at g1 g2
    push_cast at g1 g2
    rcases abs_cases (α' - α) with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] at hgt <;> nlinarith
  rw [hslope] at hsum
  -- so every orbit point of `α` is at distance `≥ 1 - x` from `0`
  have hfr : ∀ M : ℕ, 1 - x ≤ Int.fract (((M : ℝ) + 1) * α) := by
    intro M
    have hb := hsum M
    have e : ((M : ℝ) + 1) * α + x
        = ((⌊((M : ℝ) + 1) * α⌋ : ℤ) : ℝ) + (Int.fract (((M : ℝ) + 1) * α) + x) := by
      rw [Int.fract]; ring
    rw [e, Int.floor_intCast_add] at hb
    have h1 : (1 : ℤ) ≤ ⌊Int.fract (((M : ℝ) + 1) * α) + x⌋ := by omega
    rw [Int.le_floor] at h1
    push_cast at h1
    linarith
  -- but the orbit of `0` comes within `1 - x` of `0`
  obtain ⟨k, hk1, -, h2⟩ :=
    exists_fract_mem_Ico hα 0 (c := 0) (ε := 1 - x) le_rfl (by linarith) (by linarith)
  have hk : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
    have : (1 : ℕ) ≤ k := hk1
    push_cast [this]
    ring
  have := hfr (k - 1)
  rw [hk] at this
  rw [zero_add] at h2
  linarith

/-! ### The Fibonacci instance of `all-the-proofs.tex` Theorem 6.1 -/

/-- `1/φ = (√5 - 1)/2`, the slope of the Fibonacci sequence. -/
noncomputable abbrev invPhi : ℝ := (Real.sqrt 5 - 1) / 2

lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

lemma two_lt_sqrt5 : (2 : ℝ) < Real.sqrt 5 := by
  nlinarith [sqrt5_sq, Real.sqrt_nonneg 5]

lemma sqrt5_lt_three : Real.sqrt 5 < 3 := by
  nlinarith [sqrt5_sq, Real.sqrt_nonneg 5]

lemma invPhi_pos : 0 < invPhi := by
  have := two_lt_sqrt5; unfold invPhi; linarith

lemma invPhi_lt_one : invPhi < 1 := by
  have := sqrt5_lt_three; unfold invPhi; linarith

lemma irrational_invPhi : Irrational ((Real.sqrt 5 - 1) / 2) := by
  have h5 : Irrational (Real.sqrt 5) := by
    simpa using (by norm_num : Nat.Prime 5).irrational_sqrt
  simpa using ((h5.sub_natCast 1).div_natCast (by norm_num : (2 : ℕ) ≠ 0))

theorem not_code_fib :
    ¬ ∃ α' x : ℝ, 0 < α' ∧ α' < 1 ∧ 0 ≤ x ∧ x < 1 ∧
      cons1 (code ((Real.sqrt 5 - 1) / 2) ((Real.sqrt 5 - 1) / 2)) = code α' x :=
  not_code irrational_invPhi invPhi_pos invPhi_lt_one

theorem isSturmian_cons1_code (hα : Irrational α) (hα0 : 0 < α) (hα1 : α < 1) :
    IsSturmian (cons1 (code α α)) := by
  rw [← codeUp_zero_eq hα hα0 hα1]
  exact isSturmian_codeUp hα hα0 hα1 0

/-- **`all-the-proofs.tex` Theorem 6.1, now complete.**  `sturmian.tex` §2
asserts that every Sturmian sequence is a lower coding `code α' x`.  It is not:
`cons1 (code α α)` is Sturmian — it has exactly `m + 1` factors of every
length — and is a lower coding of nothing. -/
theorem sturmian_not_code (hα : Irrational α) (hα0 : 0 < α) (hα1 : α < 1) :
    IsSturmian (cons1 (code α α)) ∧
      ¬ ∃ α' x : ℝ, 0 < α' ∧ α' < 1 ∧ 0 ≤ x ∧ x < 1 ∧ cons1 (code α α) = code α' x :=
  ⟨isSturmian_cons1_code hα hα0 hα1, not_code hα hα0 hα1⟩

/-- The Fibonacci instance: the headline of §6, with the word *Sturmian* now
discharged inside Lean rather than taken from the paper. -/
theorem fib_sturmian_not_code :
    IsSturmian (cons1 (code ((Real.sqrt 5 - 1) / 2) ((Real.sqrt 5 - 1) / 2))) ∧
      ¬ ∃ α' x : ℝ, 0 < α' ∧ α' < 1 ∧ 0 ≤ x ∧ x < 1 ∧
        cons1 (code ((Real.sqrt 5 - 1) / 2) ((Real.sqrt 5 - 1) / 2)) = code α' x :=
  sturmian_not_code irrational_invPhi invPhi_pos invPhi_lt_one

/-! ## §6.1 The converse of Morse–Hedlund

Every Sturmian sequence is a mechanical coding.  `../all-the-proofs.tex` §6
proves it in five steps and `PLAN.md` Phase 9 tracks the formalisation; what is
here is `lem:evper` and the pair of words step 2 is built on. -/

section MorseHedlund

variable {ℓ : ℕ → ℕ}

/-! ### Eventual periodicity — `lem:evper` -/

/-- A preperiod `q` and a period `p`. -/
def EventuallyPeriodic (ℓ : ℕ → ℕ) : Prop :=
  ∃ q p : ℕ, 0 < p ∧ ∀ k, q ≤ k → ℓ (k + p) = ℓ k

/-- Every position reads the same as one below `q + p`. -/
lemma exists_shift_lt {q p : ℕ} (hp : 0 < p)
    (hper : ∀ k, q ≤ k → ℓ (k + p) = ℓ k) (k : ℕ) :
    ∃ k' < q + p, ∀ j, ℓ (k' + j) = ℓ (k + j) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases lt_or_ge k (q + p) with h | h
    · exact ⟨k, h, fun j => rfl⟩
    · obtain ⟨k', hk', hval⟩ := ih (k - p) (by omega)
      refine ⟨k', hk', fun j => ?_⟩
      rw [hval j, ← hper (k - p + j) (by omega)]
      congr 1
      omega

/-- **`lem:evper`.**  An eventually periodic sequence has bounded complexity. -/
theorem exists_bound_of_eventuallyPeriodic (h : EventuallyPeriodic ℓ) :
    ∃ B, ∀ n, (factors ℓ n).ncard ≤ B := by
  obtain ⟨q, p, hp, hper⟩ := h
  refine ⟨q + p, fun n => ?_⟩
  have hsub : factors ℓ n
      ⊆ (fun k => fun j : Fin n => ℓ (k + (j : ℕ))) '' Set.Iio (q + p) := by
    rintro w ⟨k, rfl⟩
    obtain ⟨k', hk', hval⟩ := exists_shift_lt hp hper k
    exact ⟨k', hk', by funext j; exact hval j⟩
  calc (factors ℓ n).ncard
      ≤ ((fun k => fun j : Fin n => ℓ (k + (j : ℕ))) '' Set.Iio (q + p)).ncard :=
        Set.ncard_le_ncard hsub ((Set.finite_Iio _).image _)
    _ ≤ (Set.Iio (q + p)).ncard := Set.ncard_image_le (Set.finite_Iio _)
    _ = q + p := by
        rw [show (Set.Iio (q + p) : Set ℕ) = ↑(Finset.Iio (q + p)) by ext; simp,
            Set.ncard_coe_finset, Nat.card_Iio]

theorem not_eventuallyPeriodic (hS : IsSturmian ℓ) : ¬ EventuallyPeriodic ℓ := by
  intro h
  obtain ⟨B, hB⟩ := exists_bound_of_eventuallyPeriodic h
  have h1 := hB (B + 1)
  rw [hS (B + 1) (by omega)] at h1
  omega

/-- A Sturmian sequence over `{0,1}` has infinitely many `1`s: otherwise it ends
in `0^∞`. -/
theorem exists_one_ge (hb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ) (N : ℕ) :
    ∃ k, N ≤ k ∧ ℓ k = 1 := by
  by_contra hcon
  push Not at hcon
  refine not_eventuallyPeriodic hS ⟨N, 1, one_pos, fun k hk => ?_⟩
  have h1 := hcon k hk
  have h2 := hcon (k + 1) (by omega)
  have h3 := hb k
  have h4 := hb (k + 1)
  omega

/-! ### The four words of step 2

`prop:blocks` runs on `0^{j+1}` and `1 0^j` and the two extensions of each. -/

/-- `0^m`. -/
def zeros (m : ℕ) : Fin m → ℕ := fun _ => 0

/-- `1 0^j`. -/
def oneZeros (j : ℕ) : Fin (j + 1) → ℕ := fun i => if (i : ℕ) = 0 then 1 else 0

/-- `0^m 1`. -/
def zerosOne (m : ℕ) : Fin (m + 1) → ℕ := Fin.snoc (zeros m) 1

/-- `1 0^j 1`. -/
def oneZerosOne (j : ℕ) : Fin (j + 2) → ℕ := Fin.snoc (oneZeros j) 1

lemma snoc_zeros (m : ℕ) :
    (Fin.snoc (zeros m) 0 : Fin (m + 1) → ℕ) = zeros (m + 1) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp [zeros]
  · intro t; simp [zeros]

lemma snoc_oneZeros (j : ℕ) :
    (Fin.snoc (oneZeros j) 0 : Fin (j + 2) → ℕ) = oneZeros (j + 1) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp [oneZeros]
  · intro t; simp [oneZeros]

/-- They have the same length and differ in their first letter. -/
lemma zeros_ne_oneZeros (j : ℕ) : zeros (j + 1) ≠ oneZeros j := by
  intro h
  have := congrFun h 0
  simp [zeros, oneZeros] at this

/-! ### Occurrence

Membership in `factors` becomes a statement about positions, and each of the
four words gets its own form.  Step 2's deductions — this word sits inside that
factor — are then arithmetic on the witness, which is what `omega` wants. -/

lemma mem_factors_iff {m : ℕ} {w : Fin m → ℕ} :
    w ∈ factors ℓ m ↔ ∃ k, ∀ i : Fin m, ℓ (k + (i : ℕ)) = w i := by
  constructor
  · rintro ⟨k, rfl⟩; exact ⟨k, fun i => rfl⟩
  · rintro ⟨k, h⟩; exact ⟨k, by funext j; exact (h j).symm⟩

lemma zerosOne_apply (m : ℕ) (i : Fin (m + 1)) :
    zerosOne m i = if (i : ℕ) = m then 1 else 0 := by
  refine Fin.lastCases ?_ ?_ i
  · simp [zerosOne]
  · intro t
    have ht : (t : ℕ) ≠ m := Nat.ne_of_lt t.2
    simp [zerosOne, zeros, ht]

lemma oneZerosOne_apply (j : ℕ) (i : Fin (j + 2)) :
    oneZerosOne j i = if (i : ℕ) = 0 then 1 else if (i : ℕ) = j + 1 then 1 else 0 := by
  refine Fin.lastCases ?_ ?_ i
  · simp [oneZerosOne]
  · intro t
    have ht : (t : ℕ) ≠ j + 1 := Nat.ne_of_lt t.2
    simp [oneZerosOne, oneZeros, ht]

lemma mem_factors_zeros_iff (m : ℕ) :
    zeros m ∈ factors ℓ m ↔ ∃ k, ∀ i < m, ℓ (k + i) = 0 := by
  rw [mem_factors_iff]
  exact ⟨fun ⟨k, h⟩ => ⟨k, fun i hi => h ⟨i, hi⟩⟩, fun ⟨k, h⟩ => ⟨k, fun i => h i i.2⟩⟩

lemma mem_factors_oneZeros_iff (j : ℕ) :
    oneZeros j ∈ factors ℓ (j + 1) ↔ ∃ k, ℓ k = 1 ∧ ∀ i < j, ℓ (k + 1 + i) = 0 := by
  rw [mem_factors_iff]
  constructor
  · rintro ⟨k, h⟩
    refine ⟨k, ?_, fun i hi => ?_⟩
    · have := h ⟨0, by omega⟩; simpa [oneZeros] using this
    · have := h ⟨i + 1, by omega⟩
      simp only [oneZeros] at this
      rw [show k + 1 + i = k + (i + 1) by omega]
      simpa using this
  · rintro ⟨k, h1, h2⟩
    refine ⟨k, fun i => ?_⟩
    rcases Nat.eq_zero_or_pos (i : ℕ) with hi | hi
    · simp [oneZeros, hi, h1]
    · obtain ⟨t, ht⟩ : ∃ t, (i : ℕ) = t + 1 := ⟨(i : ℕ) - 1, by omega⟩
      have htj : t < j := by have := i.2; omega
      have hv : oneZeros j i = 0 := by simp [oneZeros, ht]
      rw [hv, ht, show k + (t + 1) = k + 1 + t by omega]
      exact h2 t htj

lemma mem_factors_zerosOne_iff (m : ℕ) :
    zerosOne m ∈ factors ℓ (m + 1) ↔
      ∃ k, (∀ i < m, ℓ (k + i) = 0) ∧ ℓ (k + m) = 1 := by
  rw [mem_factors_iff]
  constructor
  · rintro ⟨k, h⟩
    refine ⟨k, fun i hi => ?_, ?_⟩
    · have := h ⟨i, by omega⟩; rw [zerosOne_apply] at this; simpa [Nat.ne_of_lt hi] using this
    · have := h ⟨m, by omega⟩; rw [zerosOne_apply] at this; simpa using this
  · rintro ⟨k, h1, h2⟩
    refine ⟨k, fun i => ?_⟩
    rw [zerosOne_apply]
    rcases eq_or_ne (i : ℕ) m with hi | hi
    · simp [hi, h2]
    · simp only [hi, if_false]
      exact h1 i (by have := i.2; omega)

lemma mem_factors_oneZerosOne_iff (j : ℕ) :
    oneZerosOne j ∈ factors ℓ (j + 2) ↔
      ∃ k, ℓ k = 1 ∧ (∀ i < j, ℓ (k + 1 + i) = 0) ∧ ℓ (k + 1 + j) = 1 := by
  rw [mem_factors_iff]
  constructor
  · rintro ⟨k, h⟩
    refine ⟨k, ?_, fun i hi => ?_, ?_⟩
    · have := h ⟨0, by omega⟩; rw [oneZerosOne_apply] at this; simpa using this
    · have := h ⟨i + 1, by omega⟩
      rw [oneZerosOne_apply] at this
      simp only [Nat.succ_ne_zero, if_false] at this
      rw [if_neg (by omega : ¬ (i + 1 = j + 1))] at this
      rw [show k + 1 + i = k + (i + 1) by omega]
      simpa using this
    · have := h ⟨j + 1, by omega⟩
      rw [oneZerosOne_apply] at this
      simp only [Nat.succ_ne_zero, if_false] at this
      rw [show k + 1 + j = k + (j + 1) by omega]
      simpa using this
  · rintro ⟨k, h1, h2, h3⟩
    refine ⟨k, fun i => ?_⟩
    rcases Nat.eq_zero_or_pos (i : ℕ) with hi | hi
    · have hv : oneZerosOne j i = 1 := by rw [oneZerosOne_apply, if_pos hi]
      rw [hv, hi]
      simpa using h1
    obtain ⟨t, ht⟩ : ∃ t, (i : ℕ) = t + 1 := ⟨(i : ℕ) - 1, by omega⟩
    rcases eq_or_ne t j with htj | htj
    · have hv : oneZerosOne j i = 1 := by
        rw [oneZerosOne_apply, if_neg (by omega), if_pos (by omega)]
      rw [hv, ht, htj, show k + (j + 1) = k + 1 + j by omega]
      exact h3
    · have hv : oneZerosOne j i = 0 := by
        rw [oneZerosOne_apply, if_neg (by omega), if_neg (by omega)]
      rw [hv, ht, show k + (t + 1) = k + 1 + t by omega]
      exact h2 t (by have := i.2; omega)

lemma rightSpecial_zeros_iff (j : ℕ) :
    zeros (j + 1) ∈ rightSpecial ℓ (j + 1) ↔
      zeros (j + 2) ∈ factors ℓ (j + 2) ∧ zerosOne (j + 1) ∈ factors ℓ (j + 2) := by
  rw [rightSpecial, Set.mem_inter_iff]
  constructor
  · rintro ⟨hA, hB⟩
    exact ⟨by rw [← snoc_zeros]; exact hA, hB⟩
  · rintro ⟨hA, hB⟩
    refine ⟨?_, hB⟩
    show (Fin.snoc (zeros (j + 1)) 0 : Fin (j + 2) → ℕ) ∈ factors ℓ (j + 2)
    rw [snoc_zeros]; exact hA

lemma rightSpecial_oneZeros_iff (j : ℕ) :
    oneZeros j ∈ rightSpecial ℓ (j + 1) ↔
      oneZeros (j + 1) ∈ factors ℓ (j + 2) ∧ oneZerosOne j ∈ factors ℓ (j + 2) := by
  rw [rightSpecial, Set.mem_inter_iff]
  constructor
  · rintro ⟨hA, hB⟩
    exact ⟨by rw [← snoc_oneZeros]; exact hA, hB⟩
  · rintro ⟨hA, hB⟩
    refine ⟨?_, hB⟩
    show (Fin.snoc (oneZeros j) 0 : Fin (j + 2) → ℕ) ∈ factors ℓ (j + 2)
    rw [snoc_oneZeros]; exact hA

/-- The pair that does the work: `0^{j+1}` and `1 0^j` cannot both be
right-special. -/
theorem not_both_rightSpecial (hb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ) (j : ℕ)
    (h0 : zeros (j + 1) ∈ rightSpecial ℓ (j + 1))
    (h1 : oneZeros j ∈ rightSpecial ℓ (j + 1)) : False := by
  obtain ⟨u, hu⟩ :=
    Set.ncard_eq_one.1 ((isSturmian_iff_ncard_rightSpecial hb).1 hS (j + 1))
  rw [hu, Set.mem_singleton_iff] at h0 h1
  exact zeros_ne_oneZeros j (h0.trans h1.symm)

/-! ### Step 1 — exactly one of `00`, `11` is absent -/

/-- A letter that is never left makes `ℓ` eventually periodic. -/
lemma eventuallyPeriodic_of_absorbing (hbb : ∀ k, ℓ k ≤ 1) {b : ℕ} (hb1 : b ≤ 1)
    (habs : ∀ k, ℓ k = b → ℓ (k + 1) = b) : EventuallyPeriodic ℓ := by
  by_cases hex : ∃ k, ℓ k = b
  · obtain ⟨k₀, hk₀⟩ := hex
    refine ⟨k₀, 1, one_pos, fun k hk => ?_⟩
    have key : ∀ t, ℓ (k₀ + t) = b := by
      intro t
      induction t with
      | zero => simpa using hk₀
      | succ n ih =>
          rw [show k₀ + (n + 1) = k₀ + n + 1 by omega]
          exact habs _ ih
    have h1 : ℓ k = b := by rw [show k = k₀ + (k - k₀) by omega]; exact key _
    have h2 : ℓ (k + 1) = b := habs k h1
    omega
  · push Not at hex
    refine ⟨0, 1, one_pos, fun k _ => ?_⟩
    have h1 := hex k
    have h2 := hex (k + 1)
    have h3 := hbb k
    have h4 := hbb (k + 1)
    omega

/-- **Step 1.**  `00` or `11` is absent.  Both `01` and `10` must occur, so the
engine at length `1` decides between the other two. -/
theorem step_one (hbb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ) :
    (∀ k, ℓ k = 0 → ℓ (k + 1) = 1) ∨ (∀ k, ℓ k = 1 → ℓ (k + 1) = 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨k, hk0, hk0'⟩, ⟨m, hm1, hm1'⟩⟩ := hcon
  have h00 : ℓ (k + 1) = 0 := by have := hbb (k + 1); omega
  have h11 : ℓ (m + 1) = 1 := by have := hbb (m + 1); omega
  have h01 : ∃ p, ℓ p = 0 ∧ ℓ (p + 1) = 1 := by
    by_contra hc
    push Not at hc
    refine not_eventuallyPeriodic hS
      (eventuallyPeriodic_of_absorbing hbb (b := 0) (by omega) fun p hp => ?_)
    have h1 := hbb (p + 1)
    have h2 := hc p hp
    omega
  have h10 : ∃ p, ℓ p = 1 ∧ ℓ (p + 1) = 0 := by
    by_contra hc
    push Not at hc
    refine not_eventuallyPeriodic hS
      (eventuallyPeriodic_of_absorbing hbb (b := 1) (by omega) fun p hp => ?_)
    have h1 := hbb (p + 1)
    have h2 := hc p hp
    omega
  obtain ⟨p, hp0, hp1⟩ := h01
  obtain ⟨q, hq1, hq0⟩ := h10
  refine not_both_rightSpecial hbb hS 0 ?_ ?_
  · refine (rightSpecial_zeros_iff 0).2 ⟨?_, ?_⟩
    · refine (mem_factors_zeros_iff 2).2 ⟨k, fun i hi => ?_⟩
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · simpa using hk0
      · simpa using h00
    · refine (mem_factors_zerosOne_iff 1).2 ⟨p, fun i hi => ?_, by simpa using hp1⟩
      rcases (by omega : i = 0) with rfl
      simpa using hp0
  · refine (rightSpecial_oneZeros_iff 0).2 ⟨?_, ?_⟩
    · refine (mem_factors_oneZeros_iff 1).2 ⟨q, hq1, fun i hi => ?_⟩
      rcases (by omega : i = 0) with rfl
      simpa using hq0
    · exact (mem_factors_oneZerosOne_iff 0).2
        ⟨m, hm1, fun i hi => absurd hi (by omega), by simpa using h11⟩

/-! ### The interior block lengths -/

def blockLens (ℓ : ℕ → ℕ) : Set ℕ := {j | oneZerosOne j ∈ factors ℓ (j + 2)}

lemma oneZeros_mem_of_blockLens {j t : ℕ} (hj : j ∈ blockLens ℓ) (ht : t ≤ j) :
    oneZeros t ∈ factors ℓ (t + 1) := by
  obtain ⟨k, h1, h2, -⟩ := (mem_factors_oneZerosOne_iff j).1 hj
  exact (mem_factors_oneZeros_iff t).2 ⟨k, h1, fun i hi => h2 i (by omega)⟩

lemma zeros_mem_of_blockLens {j t : ℕ} (hj : j ∈ blockLens ℓ) (ht : t ≤ j) :
    zeros t ∈ factors ℓ t := by
  obtain ⟨k, -, h2, -⟩ := (mem_factors_oneZerosOne_iff j).1 hj
  exact (mem_factors_zeros_iff t).2 ⟨k + 1, fun i hi => h2 i (by omega)⟩

lemma zerosOne_mem_of_blockLens {j t : ℕ} (hj : j ∈ blockLens ℓ) (ht : t ≤ j) :
    zerosOne t ∈ factors ℓ (t + 1) := by
  obtain ⟨k, -, h2, h3⟩ := (mem_factors_oneZerosOne_iff j).1 hj
  refine (mem_factors_zerosOne_iff t).2 ⟨k + 1 + (j - t), fun i hi => ?_, ?_⟩
  · rw [show k + 1 + (j - t) + i = k + 1 + (j - t + i) by omega]
    exact h2 _ (by omega)
  · rw [show k + 1 + (j - t) + t = k + 1 + j by omega]
    exact h3

/-- Two interior block lengths differ by at most one.  This is the boundedness
paragraph of `prop:blocks` and its later display at once. -/
theorem blockLens_le (hb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ)
    {j s : ℕ} (hj : j ∈ blockLens ℓ) (hs : s ∈ blockLens ℓ) : s ≤ j + 1 := by
  by_contra hcon
  push Not at hcon
  refine not_both_rightSpecial hb hS j ?_ ?_
  · exact (rightSpecial_zeros_iff j).2
      ⟨zeros_mem_of_blockLens hs (by omega), zerosOne_mem_of_blockLens hs (by omega)⟩
  · exact (rightSpecial_oneZeros_iff j).2
      ⟨oneZeros_mem_of_blockLens hs (by omega), hj⟩

/-- The next `1` strictly after `k`, and only `0`s before it. -/
lemma exists_next_one (hb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ) (k : ℕ) :
    ∃ d, 0 < d ∧ ℓ (k + d) = 1 ∧ ∀ i, 0 < i → i < d → ℓ (k + i) = 0 := by
  classical
  have hex : ∃ d, 0 < d ∧ ℓ (k + d) = 1 := by
    obtain ⟨k', hk', h1⟩ := exists_one_ge hb hS (k + 1)
    exact ⟨k' - k, by omega, by rw [show k + (k' - k) = k' by omega]; exact h1⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun i hi0 hid => ?_⟩
  have hne : ℓ (k + i) ≠ 1 := fun h => Nat.find_min hex hid ⟨hi0, h⟩
  have := hb (k + i)
  omega

lemma blockLens_nonempty (hb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ) :
    (blockLens ℓ).Nonempty := by
  obtain ⟨k, -, hk1⟩ := exists_one_ge hb hS 0
  obtain ⟨d, hd0, hd1, hd2⟩ := exists_next_one hb hS k
  refine ⟨d - 1, (mem_factors_oneZerosOne_iff (d - 1)).2 ⟨k, hk1, fun i hi => ?_, ?_⟩⟩
  · rw [show k + 1 + i = k + (i + 1) by omega]
    exact hd2 (i + 1) (by omega) (by omega)
  · rw [show k + 1 + (d - 1) = k + d by omega]
    exact hd1

/-- `11` absent forces every interior block to be nonempty. -/
lemma one_le_of_mem_blockLens (h11 : ∀ k, ℓ k = 1 → ℓ (k + 1) = 0)
    {j : ℕ} (hj : j ∈ blockLens ℓ) : 1 ≤ j := by
  rcases Nat.eq_zero_or_pos j with rfl | h
  · obtain ⟨k, h1, -, h3⟩ := (mem_factors_oneZerosOne_iff 0).1 hj
    have h4 : ℓ (k + 1) = 1 := by simpa using h3
    have h5 := h11 k h1
    omega
  · exact h

/-! ### `a`, the longest block -/

lemma blockLens_bddAbove (hb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ) :
    BddAbove (blockLens ℓ) := by
  obtain ⟨j, hj⟩ := blockLens_nonempty hb hS
  exact ⟨j + 1, fun s hs => blockLens_le hb hS hj hs⟩

noncomputable def blockMax (ℓ : ℕ → ℕ) : ℕ := sSup (blockLens ℓ)

theorem blockMax_mem (hb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ) :
    blockMax ℓ ∈ blockLens ℓ :=
  Nat.sSup_mem (blockLens_nonempty hb hS) (blockLens_bddAbove hb hS)

theorem le_blockMax (hb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ) {s : ℕ}
    (hs : s ∈ blockLens ℓ) : s ≤ blockMax ℓ :=
  le_csSup (blockLens_bddAbove hb hS) hs

/-- Every interior block length is `a - 1` or `a`. -/
theorem blockLens_subset (hb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ) :
    blockLens ℓ ⊆ {blockMax ℓ - 1, blockMax ℓ} := by
  intro s hs
  have h1 := le_blockMax hb hS hs
  have h2 := blockLens_le hb hS hs (blockMax_mem hb hS)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- A second block length forces `a ≥ 2`. -/
theorem two_le_blockMax (hb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ)
    (h11 : ∀ k, ℓ k = 1 → ℓ (k + 1) = 0)
    (hne : ∃ s ∈ blockLens ℓ, s ≠ blockMax ℓ) : 2 ≤ blockMax ℓ := by
  obtain ⟨s, hs, hsne⟩ := hne
  have h1 := le_blockMax hb hS hs
  have h2 := blockLens_le hb hS hs (blockMax_mem hb hS)
  have h3 := one_le_of_mem_blockLens h11 hs
  omega

/-! ### A single block length is periodic -/

/-- A single interior block length makes the gap after every `1` equal to
`a + 1`, hence `ℓ` eventually periodic.  `11` absent is not needed. -/
theorem exists_mem_blockLens_ne (hbb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ) :
    ∃ s ∈ blockLens ℓ, s ≠ blockMax ℓ := by
  by_contra hcon
  push Not at hcon
  set a := blockMax ℓ with ha
  have key : ∀ k, ℓ k = 1 →
      ℓ (k + (a + 1)) = 1 ∧ ∀ i, 0 < i → i < a + 1 → ℓ (k + i) = 0 := by
    intro k hk
    obtain ⟨d, hd0, hd1, hd2⟩ := exists_next_one hbb hS k
    have hmem : d - 1 ∈ blockLens ℓ := by
      refine (mem_factors_oneZerosOne_iff (d - 1)).2 ⟨k, hk, fun i hi => ?_, ?_⟩
      · rw [show k + 1 + i = k + (i + 1) by omega]
        exact hd2 (i + 1) (by omega) (by omega)
      · rw [show k + 1 + (d - 1) = k + d by omega]
        exact hd1
    have hda : d = a + 1 := by have := hcon _ hmem; omega
    refine ⟨by rw [← hda]; exact hd1, fun i hi0 hid => hd2 i hi0 (by omega)⟩
  obtain ⟨k₀, -, hk₀⟩ := exists_one_ge hbb hS 0
  have hA : ∀ t, ℓ (k₀ + t * (a + 1)) = 1 := by
    intro t
    induction t with
    | zero => simpa using hk₀
    | succ n ih =>
        rw [show k₀ + (n + 1) * (a + 1) = k₀ + n * (a + 1) + (a + 1) by ring]
        exact (key _ ih).1
  have hsplit : ∀ k, k₀ ≤ k →
      k = k₀ + ((k - k₀) / (a + 1)) * (a + 1) + (k - k₀) % (a + 1) := by
    intro k hk
    have h := Nat.div_add_mod (k - k₀) (a + 1)
    rw [Nat.mul_comm] at h
    omega
  have hB : ∀ k, k₀ ≤ k → (ℓ k = 1 ↔ (k - k₀) % (a + 1) = 0) := by
    intro k hk
    have hs := hsplit k hk
    have hrlt : (k - k₀) % (a + 1) < a + 1 := Nat.mod_lt _ (by omega)
    have hAt := hA ((k - k₀) / (a + 1))
    constructor
    · intro h1
      by_contra hr
      have h0 := (key _ hAt).2 ((k - k₀) % (a + 1)) (by omega) hrlt
      rw [← hs] at h0
      omega
    · intro h1
      rw [h1, Nat.add_zero] at hs
      rw [← hs] at hAt
      exact hAt
  refine not_eventuallyPeriodic hS ⟨k₀, a + 1, by omega, fun k hk => ?_⟩
  have hmod : (k + (a + 1) - k₀) % (a + 1) = (k - k₀) % (a + 1) := by
    rw [show k + (a + 1) - k₀ = (k - k₀) + (a + 1) by omega, Nat.add_mod_right]
  have e1 := hB k hk
  have e2 := hB (k + (a + 1)) (by omega)
  rw [hmod] at e2
  by_cases hp : (k - k₀) % (a + 1) = 0
  · rw [e2.2 hp, e1.2 hp]
  · have g1 : ℓ k ≠ 1 := fun h => hp (e1.1 h)
    have g2 : ℓ (k + (a + 1)) ≠ 1 := fun h => hp (e2.1 h)
    have := hbb k
    have := hbb (k + (a + 1))
    omega

theorem blockMax_sub_one_mem (hbb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ) :
    blockMax ℓ - 1 ∈ blockLens ℓ := by
  obtain ⟨s, hs, hsne⟩ := exists_mem_blockLens_ne hbb hS
  have h1 := le_blockMax hbb hS hs
  have h2 := blockLens_le hbb hS hs (blockMax_mem hbb hS)
  have he : s = blockMax ℓ - 1 := by omega
  rwa [he] at hs

/-- **`prop:blocks`.**  `a ≥ 2`, and the interior blocks have lengths `a-1` and
`a`, both occurring. -/
theorem blocks (hbb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ)
    (h11 : ∀ k, ℓ k = 1 → ℓ (k + 1) = 0) :
    2 ≤ blockMax ℓ ∧ blockLens ℓ = {blockMax ℓ - 1, blockMax ℓ} := by
  refine ⟨two_le_blockMax hbb hS h11 (exists_mem_blockLens_ne hbb hS), ?_⟩
  refine Set.Subset.antisymm (blockLens_subset hbb hS) ?_
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl
  · exact blockMax_sub_one_mem hbb hS
  · exact blockMax_mem hbb hS

/-- **`prop:blocks`, last clause.**  The block before the first `1` has length
at most `a`.  `blockMax` is the largest *interior* length, so this is a lemma
rather than the definitional triviality it is in the paper. -/
theorem initial_block_le (hbb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ)
    (h11 : ∀ k, ℓ k = 1 → ℓ (k + 1) = 0) {k₀ : ℕ}
    (hk₀ : ℓ k₀ = 1) (hlt : ∀ i, i < k₀ → ℓ i = 0) : k₀ ≤ blockMax ℓ := by
  by_contra hcon
  push Not at hcon
  have ha2 : 2 ≤ blockMax ℓ := (blocks hbb hS h11).1
  obtain ⟨b, hbe⟩ : ∃ b, blockMax ℓ = b + 1 := ⟨blockMax ℓ - 1, by omega⟩
  refine not_both_rightSpecial hbb hS b ?_ ?_
  · refine (rightSpecial_zeros_iff b).2 ⟨?_, ?_⟩
    · exact (mem_factors_zeros_iff (b + 2)).2
        ⟨0, fun i hi => by simpa using hlt i (by omega)⟩
    · refine (mem_factors_zerosOne_iff (b + 1)).2 ⟨k₀ - (b + 1), fun i hi => ?_, ?_⟩
      · exact hlt _ (by omega)
      · rw [show k₀ - (b + 1) + (b + 1) = k₀ by omega]; exact hk₀
  · refine (rightSpecial_oneZeros_iff b).2 ⟨?_, ?_⟩
    · exact oneZeros_mem_of_blockLens (blockMax_mem hbb hS) (by omega)
    · have h := blockMax_sub_one_mem hbb hS
      rwa [show blockMax ℓ - 1 = b by omega] at h

/-! ### Step 3 — the block decomposition for an abstract `ℓ` -/

/-- Deriving, as an operation on sequences.  Stated here rather than in §8
because step 3 is where an abstract `ℓ` first needs it. -/
noncomputable def deriveSeq (ℓ : ℕ → ℕ) (a : ℕ) (i : ℕ) : ℕ :=
  Nat.nth (fun k => ℓ k = 1) (i + 1) - Nat.nth (fun k => ℓ k = 1) i - a

lemma deriveSeq_code (α x : ℝ) (a : ℕ) : deriveSeq (code α x) a = derived α x a := rfl

lemma deriveSeq_codeUp (α x : ℝ) (a : ℕ) :
    deriveSeq (codeUp α x) a = derivedUp α x a := rfl

/-- The position of the `i`-th `1`. -/
noncomputable def onesPos (ℓ : ℕ → ℕ) (i : ℕ) : ℕ := Nat.nth (fun k => ℓ k = 1) i

lemma deriveSeq_eq (a i : ℕ) :
    deriveSeq ℓ a i = onesPos ℓ (i + 1) - onesPos ℓ i - a := rfl

lemma setOf_one_infinite' (hbb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ) :
    {k : ℕ | ℓ k = 1}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨k, hk1, hk2⟩ := exists_one_ge hbb hS (N + 1)
  have := hN (show k ∈ {k : ℕ | ℓ k = 1} from hk2)
  omega

lemma one_onesPos (hbb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ) (i : ℕ) :
    ℓ (onesPos ℓ i) = 1 :=
  Nat.nth_mem_of_infinite (setOf_one_infinite' hbb hS) i

lemma onesPos_lt_succ (hbb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ) (i : ℕ) :
    onesPos ℓ i < onesPos ℓ (i + 1) :=
  Nat.nth_strictMono (setOf_one_infinite' hbb hS) (Nat.lt_succ_self i)

/-- Nothing between consecutive `1`s is a `1`. -/
lemma onesPos_succ_le {i m : ℕ} (hm : ℓ m = 1) (hlt : onesPos ℓ i < m) :
    onesPos ℓ (i + 1) ≤ m := by
  by_contra h
  push Not at h
  have := Nat.le_nth_of_lt_nth_succ (p := fun k => ℓ k = 1) h hm
  simp only [onesPos] at hlt
  omega

/-- Inside a block there are only zeros. -/
theorem onesPos_block_zero (hbb : ∀ k, ℓ k ≤ 1) {i j : ℕ} (hj0 : 0 < j)
    (hj : onesPos ℓ i + j < onesPos ℓ (i + 1)) : ℓ (onesPos ℓ i + j) = 0 := by
  have h1 := hbb (onesPos ℓ i + j)
  by_contra hc
  have he : ℓ (onesPos ℓ i + j) = 1 := by omega
  have := onesPos_succ_le (i := i) he (by omega)
  omega

/-- The zeros between consecutive `1`s form an interior block. -/
theorem gap_mem_blockLens (hbb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ) (i : ℕ) :
    onesPos ℓ (i + 1) - onesPos ℓ i - 1 ∈ blockLens ℓ := by
  have hlt := onesPos_lt_succ hbb hS i
  refine (mem_factors_oneZerosOne_iff _).2
    ⟨onesPos ℓ i, one_onesPos hbb hS i, fun t ht => ?_, ?_⟩
  · rw [show onesPos ℓ i + 1 + t = onesPos ℓ i + (1 + t) by omega]
    exact onesPos_block_zero hbb (by omega) (by omega)
  · rw [show onesPos ℓ i + 1 + (onesPos ℓ (i + 1) - onesPos ℓ i - 1)
        = onesPos ℓ (i + 1) by omega]
    exact one_onesPos hbb hS (i + 1)

/-- **Step 3.**  Block `i` has length `a + ℓ'ᵢ`: with `onesPos ℓ 0 = k₀` and
`ℓ' = deriveSeq ℓ a`, this is `ℓ = 0^{k₀} τ_a(ℓ')`. -/
theorem onesPos_block_length (hbb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ)
    (h11 : ∀ k, ℓ k = 1 → ℓ (k + 1) = 0) (i : ℕ) :
    onesPos ℓ (i + 1) = onesPos ℓ i + (blockMax ℓ + deriveSeq ℓ (blockMax ℓ) i) := by
  obtain ⟨ha2, hset⟩ := blocks hbb hS h11
  have hmem := gap_mem_blockLens hbb hS i
  rw [hset] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  have hlt := onesPos_lt_succ hbb hS i
  rw [deriveSeq_eq]
  omega

/-- The derived letter is binary. -/
theorem deriveSeq_le_one (hbb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ)
    (h11 : ∀ k, ℓ k = 1 → ℓ (k + 1) = 0) (i : ℕ) :
    deriveSeq ℓ (blockMax ℓ) i ≤ 1 := by
  obtain ⟨ha2, hset⟩ := blocks hbb hS h11
  have hmem := gap_mem_blockLens hbb hS i
  rw [hset] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  have hlt := onesPos_lt_succ hbb hS i
  rw [deriveSeq_eq]
  omega

/-- Before the first `1` there are only zeros. -/
theorem onesPos_zero_zeros (hbb : ∀ k, ℓ k ≤ 1) {i : ℕ} (hi : i < onesPos ℓ 0) :
    ℓ i = 0 := by
  have h1 := hbb i
  by_contra hc
  have he : ℓ i = 1 := by omega
  have : onesPos ℓ 0 ≤ i := by
    rw [onesPos, Nat.nth_zero]
    exact Nat.sInf_le he
  omega

/-- **Step 3, the prefix.**  The initial block is at most `a` long. -/
theorem onesPos_zero_le (hbb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ)
    (h11 : ∀ k, ℓ k = 1 → ℓ (k + 1) = 0) : onesPos ℓ 0 ≤ blockMax ℓ :=
  initial_block_le hbb hS h11 (one_onesPos hbb hS 0) (fun _ hi => onesPos_zero_zeros hbb hi)

/-! ### `lem:aper` — no right-special factor means periodic -/

/-- The window of length `m` at `k`. -/
def window (ℓ : ℕ → ℕ) (m k : ℕ) : Fin m → ℕ := fun t => ℓ (k + (t : ℕ))

lemma window_mem (m k : ℕ) : window ℓ m k ∈ factors ℓ m := ⟨k, rfl⟩

lemma window_snoc (m k : ℕ) :
    (Fin.snoc (window ℓ m k) (ℓ (k + m)) : Fin (m + 1) → ℕ) = window ℓ (m + 1) k :=
  snoc_factor k m _ rfl

lemma window_mem_extBy (m k : ℕ) : window ℓ m k ∈ extBy ℓ m (ℓ (k + m)) := by
  show (Fin.snoc (window ℓ m k) (ℓ (k + m)) : Fin (m + 1) → ℕ) ∈ factors ℓ (m + 1)
  rw [window_snoc]
  exact window_mem (m + 1) k

/-- **`lem:aper`.**  With no right-special factor of length `m`, the window
determines its own successor, and the windows lie in a finite set. -/
theorem eventuallyPeriodic_of_rightSpecial_empty (hbb : ∀ k, ℓ k ≤ 1) {m : ℕ}
    (hm : 1 ≤ m) (hemp : rightSpecial ℓ m = ∅) : EventuallyPeriodic ℓ := by
  have hdet : ∀ k k', window ℓ m k = window ℓ m k' → ℓ (k + m) = ℓ (k' + m) := by
    intro k k' h
    by_contra hne
    have h0 := hbb (k + m)
    have h1 := hbb (k' + m)
    have hmem : window ℓ m k ∈ rightSpecial ℓ m := by
      rcases (by omega : ℓ (k + m) = 0 ∧ ℓ (k' + m) = 1
          ∨ ℓ (k + m) = 1 ∧ ℓ (k' + m) = 0) with ⟨e, e'⟩ | ⟨e, e'⟩
      · refine ⟨by rw [← e]; exact window_mem_extBy m k, ?_⟩
        rw [h, ← e']; exact window_mem_extBy m k'
      · refine ⟨?_, by rw [← e]; exact window_mem_extBy m k⟩
        rw [h, ← e']; exact window_mem_extBy m k'
    rw [hemp] at hmem
    exact hmem
  have hstep : ∀ k k', window ℓ m k = window ℓ m k' →
      window ℓ m (k + 1) = window ℓ m (k' + 1) := by
    intro k k' h
    funext t
    rcases (by have := t.2; omega : (t : ℕ) + 1 < m ∨ (t : ℕ) + 1 = m) with ht | ht
    · have := congrFun h ⟨(t : ℕ) + 1, ht⟩
      simp only [window] at this ⊢
      rw [show k + 1 + (t : ℕ) = k + ((t : ℕ) + 1) by omega,
          show k' + 1 + (t : ℕ) = k' + ((t : ℕ) + 1) by omega]
      exact this
    · simp only [window]
      rw [show k + 1 + (t : ℕ) = k + m by omega, show k' + 1 + (t : ℕ) = k' + m by omega]
      exact hdet k k' h
  obtain ⟨i, -, j, -, hij, heq⟩ :=
    Set.Infinite.exists_ne_map_eq_of_mapsTo (Set.infinite_univ (α := ℕ))
      (f := fun k => window ℓ m k) (fun k _ => window_mem m k) (factors_finite hbb m)
  rcases Nat.lt_or_ge i j with hlt | hge
  · refine ⟨i, j - i, by omega, fun k hk => ?_⟩
    have hall : ∀ t, window ℓ m (i + t) = window ℓ m (j + t) := by
      intro t
      induction t with
      | zero => simpa using heq
      | succ n ih =>
          rw [show i + (n + 1) = i + n + 1 by omega, show j + (n + 1) = j + n + 1 by omega]
          exact hstep _ _ ih
    have h := congrFun (hall (k - i)) ⟨0, by omega⟩
    simp only [window] at h
    rw [show i + (k - i) + 0 = k by omega, show j + (k - i) + 0 = k + (j - i) by omega] at h
    exact h.symm
  · have hlt : j < i := by omega
    refine ⟨j, i - j, by omega, fun k hk => ?_⟩
    have hall : ∀ t, window ℓ m (j + t) = window ℓ m (i + t) := by
      intro t
      induction t with
      | zero => simpa using heq.symm
      | succ n ih =>
          rw [show j + (n + 1) = j + n + 1 by omega, show i + (n + 1) = i + n + 1 by omega]
          exact hstep _ _ ih
    have h := congrFun (hall (k - j)) ⟨0, by omega⟩
    simp only [window] at h
    rw [show j + (k - j) + 0 = k by omega, show i + (k - j) + 0 = k + (i - j) by omega] at h
    exact h.symm

/-! ### Periodicity transfers up the derivation -/

lemma onesPos_strictMono (hbb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ) :
    StrictMono (onesPos ℓ) :=
  Nat.nth_strictMono (setOf_one_infinite' hbb hS)

lemma le_onesPos (hbb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ) (i : ℕ) :
    i ≤ onesPos ℓ i :=
  (onesPos_strictMono hbb hS).le_apply

/-- Which block contains `k`. -/
lemma exists_block (hbb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ) {k : ℕ}
    (hk : onesPos ℓ 0 ≤ k) : ∃ i, onesPos ℓ i ≤ k ∧ k < onesPos ℓ (i + 1) := by
  classical
  have hex : ∃ i, k < onesPos ℓ (i + 1) :=
    ⟨k, by have := le_onesPos hbb hS (k + 1); omega⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h]; exact hk
  · obtain ⟨i', hi'⟩ : ∃ i', Nat.find hex = i' + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hmin := Nat.find_min hex (m := i') (by omega)
    rw [hi']
    omega

/-- An eventually periodic derived sequence makes `ℓ` eventually periodic: one
`ℓ'`-period of blocks has a fixed total length. -/
theorem eventuallyPeriodic_of_deriveSeq (hbb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ)
    (h11 : ∀ k, ℓ k = 1 → ℓ (k + 1) = 0)
    (h' : EventuallyPeriodic (deriveSeq ℓ (blockMax ℓ))) : EventuallyPeriodic ℓ := by
  obtain ⟨q, p, hp, hper⟩ := h'
  have hmono := onesPos_strictMono hbb hS
  set P := onesPos ℓ (q + p) - onesPos ℓ q with hP
  have hPpos : 0 < P := by
    have := hmono (show q < q + p by omega)
    omega
  have hshift : ∀ t, onesPos ℓ (q + t + p) = onesPos ℓ (q + t) + P := by
    intro t
    induction t with
    | zero => simp only [Nat.add_zero]; omega
    | succ n ih =>
        have hb1 := onesPos_block_length hbb hS h11 (q + n + p)
        have hb2 := onesPos_block_length hbb hS h11 (q + n)
        have hd := hper (q + n) (by omega)
        rw [show q + (n + 1) + p = q + n + p + 1 by omega,
            show q + (n + 1) = q + n + 1 by omega, hb1, hb2, hd]
        omega
  refine ⟨onesPos ℓ q, P, hPpos, fun k hk => ?_⟩
  have hk0 : onesPos ℓ 0 ≤ k := by
    have := hmono.monotone (show 0 ≤ q by omega)
    omega
  obtain ⟨i, hi1, hi2⟩ := exists_block hbb hS hk0
  have hiq : q ≤ i := by
    by_contra hc
    push Not at hc
    have := hmono.monotone (show i + 1 ≤ q by omega)
    omega
  obtain ⟨t, ht⟩ : ∃ t, i = q + t := ⟨i - q, by omega⟩
  subst ht
  have hs1 := hshift t
  have hs2 : onesPos ℓ (q + t + p + 1) = onesPos ℓ (q + t + 1) + P := by
    have h := hshift (t + 1)
    rw [show q + (t + 1) + p = q + t + p + 1 by omega,
        show q + (t + 1) = q + t + 1 by omega] at h
    exact h
  rcases Nat.eq_zero_or_pos (k - onesPos ℓ (q + t)) with hj | hj
  · have hk1 : k = onesPos ℓ (q + t) := by omega
    have h1 : ℓ k = 1 := by rw [hk1]; exact one_onesPos hbb hS _
    have h2 : ℓ (k + P) = 1 := by
      have h := one_onesPos hbb hS (q + t + p)
      rw [show onesPos ℓ (q + t + p) = k + P by omega] at h
      exact h
    omega
  · have h1 : ℓ k = 0 := by
      have h : ℓ (onesPos ℓ (q + t) + (k - onesPos ℓ (q + t))) = 0 :=
        onesPos_block_zero hbb (by omega) (by omega)
      rw [show onesPos ℓ (q + t) + (k - onesPos ℓ (q + t)) = k by omega] at h
      exact h
    have h2 : ℓ (k + P) = 0 := by
      have h : ℓ (onesPos ℓ (q + t + p) + (k - onesPos ℓ (q + t))) = 0 :=
        onesPos_block_zero hbb (by omega) (by omega)
      rw [show onesPos ℓ (q + t + p) + (k - onesPos ℓ (q + t)) = k + P by omega] at h
      exact h
    omega

/-- The easy half of **`prop:derived`**: `ℓ'` has a right-special factor of
every length. -/
theorem rightSpecial_deriveSeq_nonempty (hbb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ)
    (h11 : ∀ k, ℓ k = 1 → ℓ (k + 1) = 0) {m : ℕ} (hm : 1 ≤ m) :
    (rightSpecial (deriveSeq ℓ (blockMax ℓ)) m).Nonempty := by
  rcases Set.eq_empty_or_nonempty (rightSpecial (deriveSeq ℓ (blockMax ℓ)) m) with hemp | h
  · exact absurd (eventuallyPeriodic_of_deriveSeq hbb hS h11
      (eventuallyPeriodic_of_rightSpecial_empty
        (fun k => deriveSeq_le_one hbb hS h11 k) hm hemp))
      (not_eventuallyPeriodic hS)
  · exact h

/-! ### `lem:rschain` — the right-special factors form a suffix chain -/

/-- Drop the first letter. -/
def tail {m : ℕ} (u : Fin (m + 1) → ℕ) : Fin m → ℕ :=
  fun t => u ⟨(t : ℕ) + 1, by omega⟩

lemma tail_mem_factors {m : ℕ} {u : Fin (m + 1) → ℕ} (hu : u ∈ factors ℓ (m + 1)) :
    tail u ∈ factors ℓ m := by
  obtain ⟨k, hk⟩ := mem_factors_iff.1 hu
  refine mem_factors_iff.2 ⟨k + 1, fun t => ?_⟩
  have h := hk ⟨(t : ℕ) + 1, by omega⟩
  simp only [tail]
  rw [show k + 1 + (t : ℕ) = k + ((t : ℕ) + 1) by omega]
  exact h

lemma snoc_tail {m : ℕ} (b : ℕ) (u : Fin (m + 1) → ℕ) :
    (Fin.snoc (tail u) b : Fin (m + 1) → ℕ)
      = tail (Fin.snoc u b : Fin (m + 2) → ℕ) := by
  funext s
  refine Fin.lastCases ?_ ?_ s
  · have he : (⟨(Fin.last m : ℕ) + 1, by omega⟩ : Fin (m + 2)) = Fin.last (m + 1) := by
      apply Fin.ext; simp
    simp only [tail, Fin.snoc_last, he, Fin.snoc_last]
  · intro t
    have he : (⟨((t.castSucc : Fin (m + 1)) : ℕ) + 1, by omega⟩ : Fin (m + 2))
        = (⟨(t : ℕ) + 1, by omega⟩ : Fin (m + 1)).castSucc := by
      apply Fin.ext; simp
    simp only [tail, Fin.snoc_castSucc, he, Fin.snoc_castSucc]

lemma tail_rightSpecial {m : ℕ} {u : Fin (m + 1) → ℕ}
    (hu : u ∈ rightSpecial ℓ (m + 1)) : tail u ∈ rightSpecial ℓ m := by
  obtain ⟨h0, h1⟩ := hu
  refine ⟨?_, ?_⟩
  · show (Fin.snoc (tail u) 0 : Fin (m + 1) → ℕ) ∈ factors ℓ (m + 1)
    rw [snoc_tail]
    exact tail_mem_factors h0
  · show (Fin.snoc (tail u) 1 : Fin (m + 1) → ℕ) ∈ factors ℓ (m + 1)
    rw [snoc_tail]
    exact tail_mem_factors h1

/-- **`lem:rschain`.**  With exactly one right-special factor of each length,
each is the suffix of the next. -/
theorem rightSpecial_chain (hbb : ∀ k, ℓ k ≤ 1) (hS : IsSturmian ℓ) {m : ℕ}
    {u : Fin (m + 1) → ℕ} (hu : u ∈ rightSpecial ℓ (m + 1))
    {v : Fin m → ℕ} (hv : v ∈ rightSpecial ℓ m) : tail u = v := by
  obtain ⟨w, hw⟩ :=
    Set.ncard_eq_one.1 ((isSturmian_iff_ncard_rightSpecial hbb).1 hS m)
  have h1 : tail u ∈ rightSpecial ℓ m := tail_rightSpecial hu
  rw [hw, Set.mem_singleton_iff] at h1 hv
  rw [h1, hv]

end MorseHedlund

/-! ## §8 The tower

The slope at level `j` is `α j` and the partial quotient is `a j`; the identity
`(a j : ℝ) + α (j+1) = 1 / α j` is the continued fraction algorithm.  For `√n`
the caller supplies these from `Palindrome.alpha` and `Palindrome.a`. -/

section Tower

variable {γ γ' : ℝ} {a : ℕ}

lemma fract_nat_mul (hγ0 : 0 < γ) {k : ℕ} (hk : (k : ℝ) * γ < 1) :
    Int.fract ((k : ℝ) * γ) = (k : ℝ) * γ :=
  Int.fract_eq_self.mpr ⟨by positivity, hk⟩

/-- The first `1` of `code γ 0` is at `a`. -/
lemma isLeast_code_zero (hγ0 : 0 < γ) (hγ1 : γ < 1) (hg : (a : ℝ) + γ' = 1/γ)
    (hg0 : 0 < γ') (hg1 : γ' < 1) : IsLeast {k : ℕ | code γ 0 k = 1} a := by
  have ha := one_le_of_inv hγ0 hγ1 hg hg1
  have key := mul_ge_one_iff (a := a) (β := γ') hγ0 hg
  have hlt : ∀ k : ℕ, k ≤ a → (k : ℝ) * γ < 1 := by
    intro k hk
    have hkR : (k : ℝ) ≤ (a : ℝ) := by exact_mod_cast hk
    rw [mul_comm, ← not_le, key]
    linarith
  constructor
  · have hmem : 1 - γ ≤ (a : ℝ) * γ := by
      have : 1 ≤ γ * ((a : ℝ) + 1) := by rw [key]; linarith
      nlinarith
    simp only [Set.mem_setOf_eq, code, zero_add, fract_nat_mul hγ0 (hlt a le_rfl)]
    rw [if_pos hmem]
  · intro k hk
    by_contra hc
    push Not at hc
    have hk1 : (k : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hc
    have hfail : (k : ℝ) * γ < 1 - γ := by
      have : γ * ((k : ℝ) + 1) < 1 := by
        rw [← not_le, key]; push Not; linarith
      nlinarith
    have := hk
    simp only [Set.mem_setOf_eq, code, zero_add, fract_nat_mul hγ0 (hlt k (by omega))] at this
    rw [if_neg (by linarith)] at this
    exact absurd this (by norm_num)

/-- The first `1` of a coding whose intercept is its slope is at `a - 1`. -/
lemma isLeast_code_slope (hγ0 : 0 < γ) (hγ1 : γ < 1) (hg : (a : ℝ) + γ' = 1/γ)
    (hg0 : 0 < γ') (hg1 : γ' < 1) : IsLeast {k : ℕ | code γ γ k = 1} (a - 1) := by
  have ha := one_le_of_inv hγ0 hγ1 hg hg1
  have key := mul_ge_one_iff (a := a) (β := γ') hγ0 hg
  have hshift : ∀ k : ℕ, γ + (k : ℝ) * γ = ((k + 1 : ℕ) : ℝ) * γ := by
    intro k; push_cast; ring
  have hlt : ∀ k : ℕ, k ≤ a → (k : ℝ) * γ < 1 := by
    intro k hk
    have hkR : (k : ℝ) ≤ (a : ℝ) := by exact_mod_cast hk
    rw [mul_comm, ← not_le, key]; linarith
  constructor
  · have hmem : 1 - γ ≤ (a : ℝ) * γ := by
      have : 1 ≤ γ * ((a : ℝ) + 1) := by rw [key]; linarith
      nlinarith
    simp only [Set.mem_setOf_eq, code, hshift]
    rw [show ((a - 1 + 1 : ℕ) : ℝ) = (a : ℝ) by congr 1; omega,
      fract_nat_mul hγ0 (by rw [show ((a : ℕ) : ℝ) = (a : ℝ) from rfl]; exact hlt a le_rfl),
      if_pos hmem]
  · intro k hk
    by_contra hc
    push Not at hc
    have hk1 : (k : ℝ) + 1 + 1 ≤ (a : ℝ) := by
      have : k + 1 + 1 ≤ a := by omega
      exact_mod_cast this
    have hfail : ((k + 1 : ℕ) : ℝ) * γ < 1 - γ := by
      have : γ * (((k + 1 : ℕ) : ℝ) + 1) < 1 := by
        rw [← not_le, key]; push Not; push_cast; linarith
      push_cast at this ⊢
      nlinarith
    have hthis := hk
    simp only [Set.mem_setOf_eq, code, hshift,
      fract_nat_mul hγ0 (hlt (k+1) (by omega))] at hthis
    rw [if_neg (by linarith)] at hthis
    exact absurd hthis (by norm_num)

/-- The first `1` of an upper coding whose intercept is its slope is at `a - 1`. -/
lemma isLeast_codeUp_slope (hγ0 : 0 < γ) (hγ1 : γ < 1) (hg : (a : ℝ) + γ' = 1/γ)
    (hg0 : 0 < γ') (hg1 : γ' < 1) : IsLeast {k : ℕ | codeUp γ γ k = 1} (a - 1) := by
  have ha := one_le_of_inv hγ0 hγ1 hg hg1
  have key := mul_ge_one_iff (a := a) (β := γ') hγ0 hg
  have hshift : ∀ k : ℕ, γ + (k : ℝ) * γ = ((k + 1 : ℕ) : ℝ) * γ := by
    intro k; push_cast; ring
  have hlt : ∀ k : ℕ, k ≤ a → (k : ℝ) * γ < 1 := by
    intro k hk
    have hkR : (k : ℝ) ≤ (a : ℝ) := by exact_mod_cast hk
    rw [mul_comm, ← not_le, key]; linarith
  constructor
  · have hmem : 1 - γ < (a : ℝ) * γ := by
      have : 1 < γ * ((a : ℝ) + 1) := by
        rw [mul_gt_one_iff (a := a) (β := γ') hγ0 hg]; linarith
      nlinarith
    simp only [Set.mem_setOf_eq, codeUp, hshift]
    rw [show ((a - 1 + 1 : ℕ) : ℝ) = (a : ℝ) by congr 1; omega,
      fract_nat_mul hγ0 (hlt a le_rfl), if_pos (Or.inl hmem)]
  · intro k hk
    by_contra hc
    push Not at hc
    have hk1 : (k : ℝ) + 1 + 1 ≤ (a : ℝ) := by
      have : k + 1 + 1 ≤ a := by omega
      exact_mod_cast this
    have hval := fract_nat_mul hγ0 (hlt (k + 1) (by omega))
    have hfail : ((k + 1 : ℕ) : ℝ) * γ ≤ 1 - γ := by
      have : γ * (((k + 1 : ℕ) : ℝ) + 1) ≤ 1 := by
        rw [← not_lt, mul_gt_one_iff (a := a) (β := γ') hγ0 hg]
        push Not; push_cast; linarith
      push_cast at this ⊢
      nlinarith
    have hne : ((k + 1 : ℕ) : ℝ) * γ ≠ 0 := by positivity
    have hthis := hk
    simp only [Set.mem_setOf_eq, codeUp, hshift, hval] at hthis
    rw [if_neg (by push Not; exact ⟨by linarith, hne⟩)] at hthis
    exact absurd hthis (by norm_num)

/-! ### The first coordinate -/

lemma coord_eq_of_isLeast (hγ0 : 0 < γ) (hg : (a : ℝ) + γ' = 1/γ) {x : ℝ} {k : ℕ}
    (hk : ones γ x 0 = k) (hval : Int.fract (x + (k : ℝ) * γ) = (a : ℝ) * γ) :
    coord γ x 0 = 1 - γ' := by
  have hmul : γ * ((a : ℝ) + γ') = 1 := by rw [hg]; field_simp
  unfold coord
  rw [hk, hval, div_eq_iff hγ0.ne']
  linear_combination hmul

lemma ones_zero_eq {x : ℝ} {k : ℕ} (h : IsLeast {k : ℕ | code γ x k = 1} k) :
    ones γ x 0 = k := by
  unfold ones; rw [Nat.nth_zero]; exact h.csInf_eq

lemma onesUp_zero_eq {x : ℝ} {k : ℕ} (h : IsLeast {k : ℕ | codeUp γ x k = 1} k) :
    onesUp γ x 0 = k := by
  unfold onesUp; rw [Nat.nth_zero]; exact h.csInf_eq

lemma fract_lt_one_of_le (hγ0 : 0 < γ) (hg : (a : ℝ) + γ' = 1/γ)
    (hg0 : 0 < γ') : (a : ℝ) * γ < 1 := by
  rw [mul_comm, ← not_le, mul_ge_one_iff (a := a) (β := γ') hγ0 hg]
  push Not; linarith

lemma refl_zero_eq (hγ0 : 0 < γ) (hγ1 : γ < 1) (hg : (a : ℝ) + γ' = 1/γ)
    (hg0 : 0 < γ') (hg1 : γ' < 1) : refl γ 0 0 = γ' := by
  have hc : coord γ 0 0 = 1 - γ' :=
    coord_eq_of_isLeast hγ0 hg (ones_zero_eq (isLeast_code_zero hγ0 hγ1 hg hg0 hg1))
      (by rw [zero_add, fract_nat_mul hγ0 (fract_lt_one_of_le hγ0 hg hg0)])
  unfold refl
  rw [hc, show -(1 - γ') = γ' + ((-1 : ℤ) : ℝ) by push_cast; ring, Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨hg0.le, hg1⟩

lemma refl_slope_eq (hγ0 : 0 < γ) (hγ1 : γ < 1) (hg : (a : ℝ) + γ' = 1/γ)
    (hg0 : 0 < γ') (hg1 : γ' < 1) : refl γ γ 0 = γ' := by
  have ha := one_le_of_inv hγ0 hγ1 hg hg1
  have hc : coord γ γ 0 = 1 - γ' :=
    coord_eq_of_isLeast hγ0 hg (ones_zero_eq (isLeast_code_slope hγ0 hγ1 hg hg0 hg1))
      (by rw [show γ + ((a - 1 : ℕ) : ℝ) * γ = ((a : ℕ) : ℝ) * γ by
            have : ((a - 1 : ℕ) : ℝ) + 1 = (a : ℝ) := by
              have : (a - 1 : ℕ) + 1 = a := by omega
              exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) this
            linear_combination γ * this
          , fract_nat_mul hγ0 (fract_lt_one_of_le hγ0 hg hg0)])
  unfold refl
  rw [hc, show -(1 - γ') = γ' + ((-1 : ℤ) : ℝ) by push_cast; ring, Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨hg0.le, hg1⟩

lemma reflUp_slope_eq (hγ0 : 0 < γ) (hγ1 : γ < 1) (hg : (a : ℝ) + γ' = 1/γ)
    (hg0 : 0 < γ') (hg1 : γ' < 1) : reflUp γ γ 0 = γ' := by
  have ha := one_le_of_inv hγ0 hγ1 hg hg1
  have hmul : γ * ((a : ℝ) + γ') = 1 := by rw [hg]; field_simp
  have hk := onesUp_zero_eq (isLeast_codeUp_slope hγ0 hγ1 hg hg0 hg1)
  have hshift : γ + ((a - 1 : ℕ) : ℝ) * γ = ((a : ℕ) : ℝ) * γ := by
    have h1 : ((a - 1 : ℕ) : ℝ) + 1 = (a : ℝ) := by
      have : (a - 1 : ℕ) + 1 = a := by omega
      exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) this
    linear_combination γ * h1
  have hval : Int.fract (γ + ((onesUp γ γ 0 : ℕ) : ℝ) * γ) = (a : ℝ) * γ := by
    rw [hk, hshift, fract_nat_mul hγ0 (fract_lt_one_of_le hγ0 hg hg0)]
  have hne : Int.fract (γ + ((onesUp γ γ 0 : ℕ) : ℝ) * γ) ≠ 0 := by
    rw [hval]
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    positivity
  unfold reflUp coordUp
  have hdiv : ((a : ℝ) * γ - (1 - γ)) / γ = 1 - γ' := by
    rw [div_eq_iff hγ0.ne']; linear_combination hmul
  rw [if_neg hne, hval, hdiv]
  ring

/-! ### The three steps -/

theorem step_zero (hγ0 : 0 < γ) (hγ1 : γ < 1) (hg : (a : ℝ) + γ' = 1/γ)
    (hg0 : 0 < γ') (hg1 : γ' < 1) : derived γ 0 a = codeUp γ' γ' := by
  rw [derive_code hγ0 hγ1 hg hg0 hg1 0, refl_zero_eq hγ0 hγ1 hg hg0 hg1]

theorem step_low (hγ0 : 0 < γ) (hγ1 : γ < 1) (hg : (a : ℝ) + γ' = 1/γ)
    (hg0 : 0 < γ') (hg1 : γ' < 1) : derived γ γ a = codeUp γ' γ' := by
  rw [derive_code hγ0 hγ1 hg hg0 hg1 γ, refl_slope_eq hγ0 hγ1 hg hg0 hg1]

theorem step_up (hγ0 : 0 < γ) (hγ1 : γ < 1) (hg : (a : ℝ) + γ' = 1/γ)
    (hg0 : 0 < γ') (hg1 : γ' < 1) : derivedUp γ γ a = code γ' γ' := by
  rw [derive_codeUp hγ0 hγ1 hg hg0 hg1 γ, reflUp_slope_eq hγ0 hγ1 hg hg0 hg1]

/-! ### The tower -/

/-- The tower of derived sequences of `code (α 0) 0`. -/
noncomputable def tower (α : ℕ → ℝ) (a : ℕ → ℕ) : ℕ → (ℕ → ℕ)
  | 0 => code (α 0) 0
  | (j + 1) => deriveSeq (tower α a j) (a j)

/-- **Theorem 8.1.**  At every level the intercept equals the slope, and the two
codings alternate. -/
theorem tower_eq {α : ℕ → ℝ} {a : ℕ → ℕ}
    (hrec : ∀ j, (a j : ℝ) + α (j + 1) = 1 / α j)
    (hpos : ∀ j, 0 < α j) (hlt : ∀ j, α j < 1) : ∀ j : ℕ,
    tower α a (j + 1)
      = if Even j then codeUp (α (j + 1)) (α (j + 1)) else code (α (j + 1)) (α (j + 1))
  | 0 => by
      show deriveSeq (code (α 0) 0) (a 0) = _
      rw [deriveSeq_code, step_zero (hpos 0) (hlt 0) (hrec 0) (hpos 1) (hlt 1)]
      simp
  | (j + 1) => by
      show deriveSeq (tower α a (j + 1)) (a (j + 1)) = _
      rw [tower_eq hrec hpos hlt j]
      by_cases hj : Even j
      · rw [if_pos hj, deriveSeq_codeUp,
          step_up (hpos (j + 1)) (hlt (j + 1)) (hrec (j + 1)) (hpos (j + 2)) (hlt (j + 2)),
          if_neg (by simp [Nat.even_add_one, hj])]
      · rw [if_neg hj, deriveSeq_code,
          step_low (hpos (j + 1)) (hlt (j + 1)) (hrec (j + 1)) (hpos (j + 2)) (hlt (j + 2)),
          if_pos (by simp [Nat.even_add_one, hj])]

/-- **Corollary 8.2.**  If the tails are periodic with period `L`, the tower
returns the sequence with its first letter removed. -/
theorem tower_period {α : ℕ → ℝ} {a : ℕ → ℕ}
    (hrec : ∀ j, (a j : ℝ) + α (j + 1) = 1 / α j)
    (hpos : ∀ j, 0 < α j) (hlt : ∀ j, α j < 1) {L : ℕ} (hL : 0 < L) (hper : α L = α 0)
    (hirr : ∀ k : ℕ, Int.fract (α 0 + (k : ℝ) * α 0) ≠ 0) :
    tower α a L = fun k => code (α 0) 0 (k + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  have hshift : code (α 0) (α 0) = fun k => code (α 0) 0 (k + 1) := by
    funext k
    rw [code_succ]
    congr 1
    rw [zero_add]
    exact (Int.fract_eq_self.mpr ⟨(hpos 0).le, hlt 0⟩).symm
  rw [tower_eq hrec hpos hlt m, hper]
  split_ifs with h
  · rw [← code_eq_codeUp hirr, hshift]
  · rw [hshift]

end Tower

/-! ## §7 The substitution

Placed after §8 because it consumes `step_low` and `isLeast_code_slope`, which
are stated there for an abstract slope: §7 is their instance at the fixed point
`β = α` of `α ↦ {1/α}`. -/

section Substitution

/-- The orbit of the base point `α` never meets `0`, so the two codings of the
slope agree.  This is the hypothesis inlined in `codeUp_zero_eq`. -/
lemma fract_slope_ne_zero (hα : Irrational α) (k : ℕ) :
    Int.fract (α + (k : ℝ) * α) ≠ 0 := by
  have e : α + (k : ℝ) * α = ((k + 1 : ℕ) : ℝ) * α := by push_cast; ring
  rw [e]
  exact fract_nat_mul_ne_zero hα (by omega)

/-! ### The golden ratio

`invPhi`, `invPhi_pos` and `invPhi_lt_one` are in §6, where `not_code_fib`
first needs them. -/

/-- `1/α = 1 + α`: the partial quotient is `a₁ = 1` and the next slope is
`β = α`.  This is the computation opening the proof of Theorem 7.1. -/
lemma invPhi_rec : ((1 : ℕ) : ℝ) + invPhi = 1 / invPhi := by
  rw [eq_div_iff (ne_of_gt invPhi_pos)]
  unfold invPhi
  push_cast
  linear_combination sqrt5_sq / 4

/-! ### `c' = c` -/

/-- **`c' = c`.**  Deriving the Fibonacci sequence returns it unchanged: the
first claim of `../all-the-proofs.tex` Theorem 7.1. -/
theorem fib_derive : derived invPhi invPhi 1 = code invPhi invPhi := by
  rw [step_low invPhi_pos invPhi_lt_one invPhi_rec invPhi_pos invPhi_lt_one]
  exact (code_eq_codeUp (fract_slope_ne_zero irrational_invPhi)).symm

lemma fib_ones_zero : ones invPhi invPhi 0 = 0 := by
  simpa using ones_zero_eq
    (isLeast_code_slope invPhi_pos invPhi_lt_one invPhi_rec invPhi_pos invPhi_lt_one)

lemma fib_code_zero : code invPhi invPhi 0 = 1 := by
  have h := code_ones invPhi_pos invPhi 0
  rwa [fib_ones_zero] at h

/-- The blocks of the Fibonacci sequence: block `i` has length `1 + cᵢ`. -/
lemma fib_block_length (i : ℕ) :
    ones invPhi invPhi (i + 1) = ones invPhi invPhi i + (1 + code invPhi invPhi i) := by
  rw [← fib_derive]
  exact block_length invPhi_pos invPhi_lt_one invPhi_rec invPhi_pos.le invPhi_lt_one _ i

/-! ### `σ(c) = c` -/

/-- `σ(1) = 10`, `σ(0) = 1` — the substitution `τ_{a₁}` at `a₁ = 1`. -/
def sigma (l : List ℕ) : List ℕ := l.flatMap (fun b => if b = 1 then [1, 0] else [1])

lemma sigma_append (l l' : List ℕ) : sigma (l ++ l') = sigma l ++ sigma l' := by
  simp [sigma, List.flatMap_append]

/-- The prefix of length `m`. -/
def pre (ℓ : ℕ → ℕ) (m : ℕ) : List ℕ := (List.range m).map ℓ

lemma pre_succ (ℓ : ℕ → ℕ) (m : ℕ) : pre ℓ (m + 1) = pre ℓ m ++ [ℓ m] := by
  simp [pre, List.range_succ]

lemma pre_length (ℓ : ℕ → ℕ) (m : ℕ) : (pre ℓ m).length = m := by simp [pre]

/-- **`σ(c) = c`**, read on prefixes: applying `σ` to the first `m` letters of
`c` gives the first `ones m` letters of `c`.  Since `ones m → ∞` this says the
infinite sequences agree.  Second claim of Theorem 7.1. -/
theorem sigma_pre (m : ℕ) :
    sigma (pre (code invPhi invPhi) m) = pre (code invPhi invPhi) (ones invPhi invPhi m) := by
  induction m with
  | zero => simp [pre, sigma, fib_ones_zero]
  | succ m ih =>
      rw [pre_succ, sigma_append, ih]
      have hlen := fib_block_length m
      have h1 : code invPhi invPhi (ones invPhi invPhi m) = 1 := code_ones invPhi_pos _ m
      by_cases hc : code invPhi invPhi m = 1
      · have h2 : code invPhi invPhi (ones invPhi invPhi m + 1) = 0 :=
          block_zero _ m 1 one_pos (by omega)
        rw [hc, show ones invPhi invPhi (m + 1) = ones invPhi invPhi m + 1 + 1 by omega,
          pre_succ, pre_succ, h1, h2]
        simp [sigma]
      · have hc0 : code invPhi invPhi m = 0 := by
          have := code_le_one invPhi invPhi m; omega
        rw [hc0, show ones invPhi invPhi (m + 1) = ones invPhi invPhi m + 1 by omega,
          pre_succ, h1]
        simp [sigma]

/-! ### `c = lim σʲ(1)` -/

/-- The length of `σʲ(1)`: `1, 2, 3, 5, 8, …`, the Fibonacci numbers. -/
noncomputable def fibLen : ℕ → ℕ
  | 0 => 1
  | j + 1 => ones invPhi invPhi (fibLen j)

/-- **`c = lim σʲ(1)`.**  `σʲ(1)` is the prefix of `c` of length `fibLen j`.
Third claim of Theorem 7.1. -/
theorem fib_limit (j : ℕ) : sigma^[j] [1] = pre (code invPhi invPhi) (fibLen j) := by
  induction j with
  | zero => simp [pre, fibLen, fib_code_zero]
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih, sigma_pre, fibLen]

lemma succ_le_ones {m : ℕ} (hm : 1 ≤ m) : m + 1 ≤ ones invPhi invPhi m := by
  induction m, hm using Nat.le_induction with
  | base =>
      have h := fib_block_length 0
      rw [fib_ones_zero, fib_code_zero] at h
      norm_num at h
      omega
  | succ m hm ih =>
      have h := fib_block_length m
      omega

lemma one_le_fibLen (j : ℕ) : 1 ≤ fibLen j := by
  induction j with
  | zero => simp [fibLen]
  | succ j ih =>
      have := succ_le_ones ih
      rw [fibLen]
      omega

/-- The prefixes genuinely grow, so the limit in `fib_limit` exists. -/
theorem fibLen_lt_succ (j : ℕ) : fibLen j < fibLen (j + 1) := by
  have := succ_le_ones (one_le_fibLen j)
  rw [fibLen]
  omega

/-- The length of `σʲ(1)` is `fibLen j`, so `fib_limit` says `σʲ(1)` is the
prefix of `c` of its own length. -/
theorem length_sigma_iterate (j : ℕ) : (sigma^[j] [1]).length = fibLen j := by
  rw [fib_limit, pre_length]

end Substitution




#print axioms Sturmian.code_eq_sub_floor
#print axioms Sturmian.codeUp_eq_sub_ceil
#print axioms Sturmian.sum_code
#print axioms Sturmian.exists_fract_mem_Ioo
#print axioms Sturmian.Icc_subset_closure_orbit
#print axioms Sturmian.code_eq_codeUp
#print axioms Sturmian.complexity
#print axioms Sturmian.codeUp_add_code_reflect
#print axioms Sturmian.ncard_factors_code
#print axioms Sturmian.ncard_factors_codeUp
#print axioms Sturmian.ncard_factors_succ
#print axioms Sturmian.isSturmian_iff_ncard_rightSpecial
#print axioms Sturmian.exists_bound_of_eventuallyPeriodic
#print axioms Sturmian.not_eventuallyPeriodic
#print axioms Sturmian.exists_one_ge
#print axioms Sturmian.not_both_rightSpecial
#print axioms Sturmian.step_one
#print axioms Sturmian.mem_factors_oneZerosOne_iff
#print axioms Sturmian.blockLens_le
#print axioms Sturmian.blocks
#print axioms Sturmian.initial_block_le
#print axioms Sturmian.onesPos_block_length
#print axioms Sturmian.onesPos_zero_le
#print axioms Sturmian.eventuallyPeriodic_of_rightSpecial_empty
#print axioms Sturmian.eventuallyPeriodic_of_deriveSeq
#print axioms Sturmian.rightSpecial_deriveSeq_nonempty
#print axioms Sturmian.rightSpecial_chain
#print axioms Sturmian.return_time
#print axioms Sturmian.ones_succ_eq
#print axioms Sturmian.derived_eq
#print axioms Sturmian.coord_succ
#print axioms Sturmian.derive_code
#print axioms Sturmian.return_timeUp
#print axioms Sturmian.derivedUp_eq
#print axioms Sturmian.coordUp_succ
#print axioms Sturmian.derive_codeUp
#print axioms Sturmian.codeUp_zero_eq
#print axioms Sturmian.not_code
#print axioms Sturmian.not_code_fib
#print axioms Sturmian.sturmian_not_code
#print axioms Sturmian.fib_sturmian_not_code
#print axioms Sturmian.tower_eq
#print axioms Sturmian.tower_period
#print axioms Sturmian.fib_derive
#print axioms Sturmian.sigma_pre
#print axioms Sturmian.fib_limit

end Sturmian
