module

public import DirectedCycleFPRAS.WitnessMixture

@[expose] public section

/-!
# Stability of finite sampling

L1 distance is used rather than hiding the factor of two in total variation.
The lemmas apply to genuine distributions and to nonnormalised masses.
-/

namespace DirectedCycleFPRAS

open scoped BigOperators

noncomputable section

variable {Ω I : Type*} [Fintype Ω] [Fintype I]

/-- L1 distance between finite real-valued functions. -/
def l1 (p q : Ω → ℝ) : ℝ := ∑ x, |p x - q x|

/-- A bounded score changes by at most the L1 distance of the sampling laws. -/
theorem expectation_stability (p q f : Ω → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |(∑ x, p x * f x) - ∑ x, q x * f x| ≤ l1 p q := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ x, (p x * f x - q x * f x)| ≤ ∑ x, |p x * f x - q x * f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ l1 p q := by
      apply Finset.sum_le_sum
      intro x _
      rw [← sub_mul, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hf x)

/-- Mixing approximate conditional laws incurs at most the weighted sum
of their L1 errors. -/
theorem mixture_stability (a : I → ℝ) (p q : I → Ω → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    l1 (fun x => ∑ i, a i * p i x) (fun x => ∑ i, a i * q i x)
      ≤ ∑ i, a i * l1 (p i) (q i) := by
  unfold l1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i, (a i * p i x - a i * q i x)| ≤
        ∑ i, |a i * p i x - a i * q i x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, a i * |p i x - q i x| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_sub, abs_mul, abs_of_nonneg (ha i)]

/-- Changing selection probabilities incurs no larger L1 error after
sampling from a family of normalised conditional distributions. -/
theorem selection_stability (a b : I → ℝ) (p : I → Ω → ℝ)
    (hp : ∀ i x, 0 ≤ p i x) (hs : ∀ i, ∑ x, p i x = 1) :
    l1 (fun x => ∑ i, a i * p i x) (fun x => ∑ i, b i * p i x) ≤ l1 a b := by
  calc
    l1 (fun x => ∑ i, a i * p i x) (fun x => ∑ i, b i * p i x)
      ≤ ∑ x, ∑ i, |a i - b i| * p i x := by
        unfold l1
        apply Finset.sum_le_sum
        intro x _
        rw [← Finset.sum_sub_distrib]
        calc
          |∑ i, (a i * p i x - b i * p i x)| ≤
              ∑ i, |a i * p i x - b i * p i x| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i, |a i - b i| * p i x := by
            apply Finset.sum_congr rfl
            intro i _
            rw [← sub_mul, abs_mul, abs_of_nonneg (hp i x)]
    _ = l1 a b := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hs, mul_one]
      rfl

/-- Relative error in positive weights survives normalisation with error
at most 4 alpha, for alpha ≤ 1/2. This is the numerical conditional-branch lemma. -/
theorem normalise_error {a b A B α : ℝ}
    (ha : 0 ≤ a) (hA : 0 < A)
    (hα : 0 ≤ α) (hαhalf : α ≤ 1 / 2)
    (hab : |b - a| ≤ α * a) (hAB : |B - A| ≤ α * A) :
    |b / B - a / A| ≤ 4 * α * (a / A) := by
  have hBlo : (1 - α) * A ≤ B := by
    have := (abs_le.mp hAB).1
    linarith
  have hB : 0 < B := by nlinarith
  have hnum : |b * A - a * B| ≤ 2 * α * a * A := by
    calc
      |b * A - a * B| = |(b - a) * A + a * (A - B)| := by ring_nf
      _ ≤ |(b - a) * A| + |a * (A - B)| := abs_add_le _ _
      _ = |b - a| * A + a * |B - A| := by
        rw [abs_mul, abs_mul, abs_of_pos hA, abs_of_nonneg ha, abs_sub_comm A B]
      _ ≤ (α * a) * A + a * (α * A) :=
        add_le_add (mul_le_mul_of_nonneg_right hab hA.le)
          (mul_le_mul_of_nonneg_left hAB ha)
      _ = 2 * α * a * A := by ring
  have heq : b / B - a / A = (b * A - a * B) / (B * A) := by field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos hB hA)]
  apply (div_le_iff₀ (mul_pos hB hA)).mpr
  have hcancel : 4 * α * (a / A) * (B * A) = 4 * α * a * B := by
    field_simp
  rw [hcancel]
  have hcoef : 0 ≤ 4 * α * a := by positivity
  have hhalf : A / 2 ≤ B := by nlinarith
  have := mul_le_mul_of_nonneg_left hhalf hcoef
  nlinarith

/-- Relative pointwise estimates of nonnegative weights induce a close
normalised distribution, including zero-weight alternatives. -/
theorem normalised_weights_l1 (a b : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    {α : ℝ} (hα : 0 ≤ α) (hαhalf : α ≤ 1 / 2)
    (hA : 0 < ∑ i, a i) (hest : ∀ i, |b i - a i| ≤ α * a i) :
    l1 (fun i => b i / ∑ j, b j) (fun i => a i / ∑ j, a j) ≤ 4 * α := by
  have htotal : |(∑ i, b i) - ∑ i, a i| ≤ α * ∑ i, a i := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hest i)
  calc
    _ ≤ ∑ i, 4 * α * (a i / ∑ j, a j) := by
      apply Finset.sum_le_sum
      intro i _
      exact normalise_error (ha i) hA hα hαhalf (hest i) htotal
    _ = 4 * α := by
      rw [← Finset.mul_sum, ← Finset.sum_div, div_self (ne_of_gt hA), mul_one]

end
end DirectedCycleFPRAS
