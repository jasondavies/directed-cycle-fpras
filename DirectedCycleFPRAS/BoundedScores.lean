module

public import DirectedCycleFPRAS.IndependentSamples

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
noncomputable section
namespace Law
variable {Ω : Type} [Fintype Ω]

/-- The second moment of a bounded nonnegative score costs its mean, rather
than one. This gives linear dependence on the number of witnesses. -/
theorem variance_le_mean (p : Law Ω) (f : Ω → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    p.expectation (fun x => (f x - p.expectation f)^2) ≤ p.expectation f := by
  have identity : p.expectation (fun x => (f x - p.expectation f)^2) =
      p.expectation (fun x => (f x)^2) - (p.expectation f)^2 := by
    have he (x : Ω) : p.value x * (f x - p.expectation f)^2 =
        p.value x*(f x)^2 - (2*p.expectation f)*(p.value x*f x) +
          p.value x*(p.expectation f)^2 := by ring
    change (∑ x, p.value x * (f x - p.expectation f)^2) =
      (∑ x, p.value x * (f x)^2) - (p.expectation f)^2
    simp only [he, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, p.sum_one, one_mul]
    change p.expectation (fun x => (f x)^2) - (2*p.expectation f)*p.expectation f +
      (p.expectation f)^2 = p.expectation (fun x => (f x)^2) - (p.expectation f)^2
    ring
  rw [identity]
  have hsecond : p.expectation (fun x => (f x)^2) ≤ p.expectation f := by
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (p.nonneg x)
    nlinarith [hf0 x, hf1 x]
  nlinarith [sq_nonneg (p.expectation f)]

theorem average_tail_sharp (p : Law Ω) (f : Ω → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    {n : ℕ} (hn : 0 < n) {a : ℝ} (ha : 0 < a) :
    (∑ xs, if a ≤ |sampleAverage f n xs - p.expectation f|
      then (p.samples n).value xs else 0) ≤ p.expectation f / ((n : ℝ)*a^2) := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ht := (p.samples n).chebyshev (centeredSum f (p.expectation f) n) 0 (mul_pos hn' ha)
  simp only [sub_zero] at ht
  rw [p.centeredSum_secondMoment] at ht
  have heq (xs : Samples Ω n) :
      (a ≤ |sampleAverage f n xs - p.expectation f|) ↔
        (n : ℝ)*a ≤ |centeredSum f (p.expectation f) n xs| := by
    rw [average_sub_mean f _ hn, abs_div, abs_of_pos hn', le_div_iff₀ hn', mul_comm]
  simp_rw [heq]
  calc
    _ ≤ (n : ℝ)*p.expectation (fun x => (f x-p.expectation f)^2)/((n : ℝ)*a)^2 := ht
    _ ≤ (n : ℝ)*p.expectation f/((n : ℝ)*a)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left (p.variance_le_mean f hf0 hf1) hn'.le
    _ = p.expectation f / ((n : ℝ)*a^2) := by field_simp

/-- The paper's 64k/eps² budget gives failure at most 1/16 whenever the
acceptance mean is at least 1/(4k). -/
theorem relative_average_tail (p : Law Ω) (f : Ω → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    {k : ℕ} (hk : 0 < k) {eps : ℝ} (heps : 0 < eps)
    (hmean : 1 / (4*(k : ℝ)) ≤ p.expectation f)
    {n : ℕ} (hbudget : 64*(k : ℝ)/eps^2 ≤ n) :
    (∑ xs, if eps*p.expectation f ≤ |sampleAverage f n xs - p.expectation f|
      then (p.samples n).value xs else 0) ≤ 1/16 := by
  classical
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hm : 0 < p.expectation f := lt_of_lt_of_le (by positivity) hmean
  have hn' : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hbudget
  have hn : 0 < n := by exact_mod_cast hn'
  have hden : 0 < (n : ℝ)*(eps*p.expectation f)^2 := by positivity
  have hne : (p.expectation f) ≠ 0 := ne_of_gt hm
  apply (p.average_tail_sharp f hf0 hf1 hn (mul_pos heps hm)).trans
  apply (div_le_iff₀ hden).mpr
  have hb : 64*(k : ℝ) ≤ (n : ℝ)*eps^2 := (div_le_iff₀ (sq_pos_of_pos heps)).mp hbudget
  have hmk : 1 ≤ 4*(k : ℝ)*p.expectation f := by
    have := (div_le_iff₀ (show 0 < 4*(k : ℝ) by positivity)).mp hmean
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hb (sq_nonneg (p.expectation f))
  nlinarith [mul_nonneg hm.le (sub_nonneg.mpr hmk)]

end Law
end
end DirectedCycleFPRAS
