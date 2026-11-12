module

public import DirectedCycleFPRAS.FiniteLaw

@[expose] public section

/-! # Independent finite samples and a proved second-moment bound -/

namespace DirectedCycleFPRAS

open scoped BigOperators
noncomputable section

/-- Nested products provide an explicit finite space of independent samples. -/
def Samples (Ω : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => Ω × Samples Ω n

instance samplesFintype {Ω : Type} [Fintype Ω] : (n : ℕ) → Fintype (Samples Ω n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => @instFintypeProd Ω (Samples Ω n) _ (samplesFintype n)

namespace Law
variable {Ω : Type} [Fintype Ω]

def samples (p : Law Ω) : (n : ℕ) → Law (Samples Ω n)
  | 0 => { value := fun _ => 1, nonneg := fun _ => zero_le_one, sum_one := by change (∑ _ : Unit, (1 : ℝ)) = 1; simp }
  | n + 1 => {
      value := fun xs => p.value xs.1 * (p.samples n).value xs.2
      nonneg := fun xs => mul_nonneg (p.nonneg _) ((p.samples n).nonneg _)
      sum_one := by
        change (∑ xs : Ω × Samples Ω n, p.value xs.1 * (p.samples n).value xs.2) = 1
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum, Law.sum_one, mul_one]
        exact p.sum_one }

/-- Sum of the centered scores, without dividing by the sample count. -/
def centeredSum (f : Ω → ℝ) (c : ℝ) : (n : ℕ) → Samples Ω n → ℝ
  | 0, _ => 0
  | n + 1, xs => f xs.1 - c + centeredSum f c n xs.2

/-- Finite expectation is additive. -/
theorem expectation_add (p : Law Ω) (f g : Ω → ℝ) :
    p.expectation (fun x => f x + g x) = p.expectation f + p.expectation g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_centered (p : Law Ω) (f : Ω → ℝ) :
    p.expectation (fun x => f x - p.expectation f) = 0 := by
  simp_rw [expectation, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [p.sum_one, one_mul, sub_self]

theorem centeredSum_mean (p : Law Ω) (f : Ω → ℝ) (n : ℕ) :
    (p.samples n).expectation (centeredSum f (p.expectation f) n) = 0 := by
  induction n with
  | zero => simp [samples, centeredSum, expectation, Samples]
  | succ n ih =>
    change (∑ xs : Ω × Samples Ω n,
      (p.value xs.1 * (p.samples n).value xs.2) *
        (f xs.1 - p.expectation f + centeredSum f (p.expectation f) n xs.2)) = 0
    rw [Fintype.sum_prod_type]
    have expand (x : Ω) (xs : Samples Ω n) :
        (p.value x * (p.samples n).value xs) *
          (f x - p.expectation f + centeredSum f (p.expectation f) n xs) =
        (p.value x * (f x - p.expectation f)) * (p.samples n).value xs +
          p.value x * ((p.samples n).value xs * centeredSum f (p.expectation f) n xs) := by ring
    simp_rw [expand, Finset.sum_add_distrib, ← Finset.mul_sum, (p.samples n).sum_one,
      mul_one]
    change p.expectation (fun x => f x - p.expectation f) +
      ∑ x, p.value x * (p.samples n).expectation (centeredSum f (p.expectation f) n) = 0
    rw [p.expectation_centered, ih]
    simp

/-- Variance of a sum of n independent copies, proved by finite sums. -/
theorem centeredSum_secondMoment (p : Law Ω) (f : Ω → ℝ) (n : ℕ) :
    (p.samples n).expectation (fun xs => (centeredSum f (p.expectation f) n xs)^2) =
      n * p.expectation (fun x => (f x - p.expectation f)^2) := by
  induction n with
  | zero => simp [samples, centeredSum, expectation, Samples]
  | succ n ih =>
    change (∑ xs : Ω × Samples Ω n,
      (p.value xs.1 * (p.samples n).value xs.2) *
        (f xs.1 - p.expectation f + centeredSum f (p.expectation f) n xs.2)^2) = _
    rw [Fintype.sum_prod_type]
    have expand (x : Ω) (xs : Samples Ω n) :
        (p.value x * (p.samples n).value xs) *
          (f x - p.expectation f + centeredSum f (p.expectation f) n xs)^2 =
        (p.value x * (f x - p.expectation f)^2) * (p.samples n).value xs +
        (2 * p.value x * (f x - p.expectation f)) *
          ((p.samples n).value xs * centeredSum f (p.expectation f) n xs) +
        p.value x * ((p.samples n).value xs * (centeredSum f (p.expectation f) n xs)^2) := by ring
    simp_rw [expand, Finset.sum_add_distrib, ← Finset.mul_sum, (p.samples n).sum_one,
      mul_one]
    change p.expectation (fun x => (f x - p.expectation f)^2) +
      (∑ x, (2 * p.value x * (f x - p.expectation f)) *
        (p.samples n).expectation (centeredSum f (p.expectation f) n)) +
      (∑ x, p.value x * (p.samples n).expectation
        (fun xs => (centeredSum f (p.expectation f) n xs)^2)) = _
    rw [p.centeredSum_mean, ih]
    simp only [mul_zero, Finset.sum_const_zero, add_zero, ← Finset.sum_mul, p.sum_one,
      one_mul, Nat.cast_add, Nat.cast_one]
    ring

/-- A score in [0,1] has variance at most one. -/
theorem bounded_variance (p : Law Ω) (f : Ω → ℝ)
    (hlo : ∀ x, 0 ≤ f x) (hhi : ∀ x, f x ≤ 1) :
    p.expectation (fun x => (f x - p.expectation f)^2) ≤ 1 := by
  have hc0 : 0 ≤ p.expectation f :=
    Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) (hlo x)
  have hc1 : p.expectation f ≤ 1 := by
    calc
      p.expectation f ≤ ∑ x, p.value x * 1 :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hhi x) (p.nonneg x)
      _ = 1 := by simp [p.sum_one]
  calc
    p.expectation (fun x => (f x - p.expectation f)^2) ≤ ∑ x, p.value x * 1 := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (p.nonneg x)
      have h0 := hlo x
      have h1 := hhi x
      nlinarith [mul_nonneg (sub_nonneg.mpr (hhi x)) (hlo x)]
    _ = 1 := by simp [p.sum_one]

/-- Sample-average error bound. The left side is expressed as a bound on the
centered sum, avoiding a special convention for the empty average. -/
theorem sample_mean_tail (p : Law Ω) (f : Ω → ℝ)
    (hlo : ∀ x, 0 ≤ f x) (hhi : ∀ x, f x ≤ 1)
    {n : ℕ} (hn : 0 < n) {a : ℝ} (ha : 0 < a) :
    (∑ xs, if (n : ℝ) * a ≤ |centeredSum f (p.expectation f) n xs|
      then (p.samples n).value xs else 0) ≤ 1 / ((n : ℝ) * a^2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ht := (p.samples n).chebyshev (centeredSum f (p.expectation f) n) 0 (mul_pos hn' ha)
  simp only [sub_zero] at ht
  rw [p.centeredSum_secondMoment] at ht
  calc
    _ ≤ (n : ℝ) * p.expectation (fun x => (f x - p.expectation f)^2) / ((n : ℝ) * a)^2 := ht
    _ ≤ (n : ℝ) * 1 / ((n : ℝ) * a)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left (p.bounded_variance f hlo hhi) hn'.le
    _ = 1 / ((n : ℝ) * a^2) := by field_simp

/-- Uncentered sample sum. -/
def sampleSum (f : Ω → ℝ) : (n : ℕ) → Samples Ω n → ℝ
  | 0, _ => 0
  | n + 1, xs => f xs.1 + sampleSum f n xs.2

/-- The sample average; the statistical theorems require a positive sample count. -/
def sampleAverage (f : Ω → ℝ) (n : ℕ) (xs : Samples Ω n) : ℝ :=
  sampleSum f n xs / n

omit [Fintype Ω] in
theorem centeredSum_eq (f : Ω → ℝ) (c : ℝ) (n : ℕ) (xs : Samples Ω n) :
    centeredSum f c n xs = sampleSum f n xs - n * c := by
  induction n with
  | zero => simp [centeredSum, sampleSum]
  | succ n ih =>
    simp only [centeredSum, sampleSum, ih, Nat.cast_add, Nat.cast_one]
    ring

omit [Fintype Ω] in
theorem average_sub_mean (f : Ω → ℝ) (c : ℝ) {n : ℕ} (hn : 0 < n)
    (xs : Samples Ω n) :
    sampleAverage f n xs - c = centeredSum f c n xs / n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [sampleAverage, centeredSum_eq]
  field_simp

theorem average_tail (p : Law Ω) (f : Ω → ℝ)
    (hlo : ∀ x, 0 ≤ f x) (hhi : ∀ x, f x ≤ 1)
    {n : ℕ} (hn : 0 < n) {a : ℝ} (ha : 0 < a) :
    (∑ xs, if a ≤ |sampleAverage f n xs - p.expectation f|
      then (p.samples n).value xs else 0) ≤ 1 / ((n : ℝ) * a^2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have heq (xs : Samples Ω n) :
      (a ≤ |sampleAverage f n xs - p.expectation f|) ↔
        (n : ℝ) * a ≤ |centeredSum f (p.expectation f) n xs| := by
    rw [average_sub_mean f _ hn, abs_div, abs_of_pos hn', le_div_iff₀ hn', mul_comm]
  simp_rw [heq]
  exact p.sample_mean_tail f hlo hhi hn ha

end Law
end
end DirectedCycleFPRAS
