module

public import Mathlib

@[expose] public section

set_option linter.unusedSectionVars false

/-!
# Finite witness-union estimator

All sums here are finite real sums. No complexity claim, sampler implementation,
or external reliability theorem is assumed by these identities.
-/

namespace DirectedCycleFPRAS

open scoped BigOperators

noncomputable section

variable {Ω I : Type*} [Fintype Ω] [Fintype I]

/-- A finite nonnegative measure. Normalisation is unnecessary for the union identity. -/
structure Mass (Ω : Type*) where
  value : Ω → ℝ
  nonneg : ∀ x, 0 ≤ value x

namespace Mass

variable (μ : Mass Ω) (A : I → Ω → Prop) [∀ i, DecidablePred (A i)]

/-- The number of witnesses of an outcome, represented as a real number. -/
def multiplicity (x : Ω) : ℝ := ∑ i, if A i x then 1 else 0

/-- Probability/mass of a single witness event. -/
def weight (i : I) : ℝ := ∑ x, if A i x then μ.value x else 0

/-- Total witness mass, counting an outcome once per witness. -/
def totalWeight : ℝ := ∑ i, μ.weight A i

/-- Mass of the union of all witness events. -/
def unionMass : ℝ := ∑ x, if 0 < multiplicity A x then μ.value x else 0

/-- The size-biased distribution obtained by choosing a witness and conditioning on it. -/
def mixture (x : Ω) : ℝ := μ.value x * multiplicity A x / μ.totalWeight A

/-- Correction for multiple witnesses. Zero outside the event of interest. -/
def score (x : Ω) : ℝ := (multiplicity A x)⁻¹

variable {A}

theorem multiplicity_nonneg (x : Ω) : 0 ≤ multiplicity A x := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> norm_num

theorem one_le_multiplicity {x : Ω} {i : I} (hi : A i x) :
    1 ≤ multiplicity A x := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j : I => if A j x then (1 : ℝ) else 0)
    (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
  simpa [multiplicity, hi] using h

theorem multiplicity_pos_iff (x : Ω) :
    0 < multiplicity A x ↔ ∃ i, A i x := by
  constructor
  · intro h
    by_contra hn
    have hn' : ∀ i, ¬ A i x := by simpa using hn
    simp [multiplicity, hn'] at h
  · rintro ⟨i, hi⟩
    exact lt_of_lt_of_le zero_lt_one (one_le_multiplicity hi)

theorem multiplicity_le_card (x : Ω) :
    multiplicity A x ≤ Fintype.card I := by
  calc
    multiplicity A x ≤ ∑ _i : I, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> norm_num
    _ = Fintype.card I := by simp

variable (A)

theorem weight_nonneg (i : I) : 0 ≤ μ.weight A i := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact μ.nonneg x
  · rfl

theorem totalWeight_eq : μ.totalWeight A = ∑ x, μ.value x * multiplicity A x := by
  unfold totalWeight weight multiplicity
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem unionMass_nonneg : 0 ≤ μ.unionMass A := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact μ.nonneg x
  · rfl

theorem unionMass_le_totalWeight : μ.unionMass A ≤ μ.totalWeight A := by
  rw [totalWeight_eq]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : 0 < multiplicity A x
  · simp only [ite_eq_left hx]
    obtain ⟨i, hi⟩ := (multiplicity_pos_iff x).mp hx
    exact le_mul_of_one_le_right (μ.nonneg x) (one_le_multiplicity hi)
  · simp only [ite_eq_right hx]
    exact mul_nonneg (μ.nonneg x) (multiplicity_nonneg x)

theorem totalWeight_le_card_mul_unionMass :
    μ.totalWeight A ≤ (Fintype.card I : ℝ) * μ.unionMass A := by
  rw [totalWeight_eq, unionMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : 0 < multiplicity A x
  · simp only [ite_eq_left hx]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (multiplicity_le_card x) (μ.nonneg x)
  · have hz : multiplicity A x = 0 := le_antisymm (le_of_not_gt hx) (multiplicity_nonneg x)
    simp [hz]

theorem mixture_nonneg (hW : 0 < μ.totalWeight A) (x : Ω) :
    0 ≤ μ.mixture A x :=
  div_nonneg (mul_nonneg (μ.nonneg x) (multiplicity_nonneg x)) hW.le

theorem mixture_sum (hW : 0 < μ.totalWeight A) : ∑ x, μ.mixture A x = 1 := by
  simp only [mixture, ← Finset.sum_div]
  rw [← totalWeight_eq, div_self (ne_of_gt hW)]

theorem score_nonneg (x : Ω) : 0 ≤ score A x := inv_nonneg.mpr (multiplicity_nonneg x)

theorem score_le_one (x : Ω) : score A x ≤ 1 := by
  by_cases hx : 0 < multiplicity A x
  · obtain ⟨i, hi⟩ := (multiplicity_pos_iff x).mp hx
    exact (inv_le_one₀ hx).mpr (one_le_multiplicity hi)
  · have hz : multiplicity A x = 0 := le_antisymm (le_of_not_gt hx) (multiplicity_nonneg x)
    simp [score, hz]

/-- The central unbiasedness identity, including zero-multiplicity outcomes. -/
theorem mixture_score (hW : 0 < μ.totalWeight A) :
    (∑ x, μ.mixture A x * score A x) = μ.unionMass A / μ.totalWeight A := by
  unfold mixture score unionMass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : 0 < multiplicity A x
  · simp only [ite_eq_left hx]
    field_simp
  · have hz : multiplicity A x = 0 := le_antisymm (le_of_not_gt hx) (multiplicity_nonneg x)
    simp [hz]

/-- The expected score is at least the inverse number of witnesses. -/
theorem inverse_card_le_mean (hW : 0 < μ.totalWeight A) :
    (Fintype.card I : ℝ)⁻¹ ≤ μ.unionMass A / μ.totalWeight A := by
  have hb := μ.totalWeight_le_card_mul_unionMass A
  have hc : 0 < (Fintype.card I : ℝ) := by
    by_contra h
    have hz : (Fintype.card I : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
    rw [hz, zero_mul] at hb
    linarith
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ hc hW).mpr
  simpa [mul_comm] using hb

/-- The event-restricted mass at a point cannot exceed the whole event mass. -/
theorem point_le_weight {i : I} {x : Ω} (h : A i x) : μ.value x ≤ μ.weight A i := by
  have hb := Finset.single_le_sum (s := Finset.univ)
    (f := fun y => if A i y then μ.value y else 0)
    (fun y _ => by split_ifs; exact μ.nonneg y; rfl) (Finset.mem_univ x)
  simpa [weight, h] using hb

/-- Formula for conditioning on a witness event. At zero weight it is zero;
zero-weight events are never selected by the witness mixture. -/
def conditional (i : I) (x : Ω) : ℝ :=
  (if A i x then μ.value x else 0) / μ.weight A i

theorem conditional_sum {i : I} (hi : 0 < μ.weight A i) :
    ∑ x, μ.conditional A i x = 1 := by
  simp only [conditional, ← Finset.sum_div]
  change μ.weight A i / μ.weight A i = 1
  exact div_self (ne_of_gt hi)

/-- Choosing witness i with probability w_i/W and then conditioning on i
produces exactly the size-biased distribution, not an idealised substitute. -/
theorem mixture_eq_conditioned_sum (hW : 0 < μ.totalWeight A) (x : Ω) :
    μ.mixture A x = ∑ i, (μ.weight A i / μ.totalWeight A) * μ.conditional A i x := by
  have hterm : ∀ i, (μ.weight A i / μ.totalWeight A) * μ.conditional A i x =
      (if A i x then μ.value x else 0) / μ.totalWeight A := by
    intro i
    by_cases hw : μ.weight A i = 0
    · have hz : (if A i x then μ.value x else 0) = 0 := by
        split_ifs with hi
        · exact le_antisymm (hw ▸ μ.point_le_weight A hi) (μ.nonneg x)
        · rfl
      simp [conditional, hw, hz]
    · unfold conditional
      field_simp
  simp_rw [hterm]
  rw [← Finset.sum_div]
  unfold mixture multiplicity
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- The zero-probability case is equivalent to zero total witness mass. -/
theorem totalWeight_zero_iff_unionMass_zero :
    μ.totalWeight A = 0 ↔ μ.unionMass A = 0 := by
  have hZW := μ.unionMass_le_totalWeight A
  have hWZ := μ.totalWeight_le_card_mul_unionMass A
  have hZ := μ.unionMass_nonneg A
  constructor
  · intro h
    rw [h] at hZW
    exact le_antisymm hZW hZ
  · intro h
    rw [h, mul_zero] at hWZ
    rw [h] at hZW
    exact le_antisymm hWZ hZW

end Mass
end
end DirectedCycleFPRAS
