module

public import DirectedCycleFPRAS.IndependentSamples

@[expose] public section

/-!
# The robust witness estimator

This file proves a probability-of-failure bound for the explicit finite product
law of independent samples from an approximately correct mixture. It does not
assume a concentration inequality: that bound is proved in IndependentSamples.
The construction of the approximate mixture from a randomized reliability
oracle and a bit-cost model are separate obligations.
-/

namespace DirectedCycleFPRAS

open scoped BigOperators
noncomputable section

/-- Safe multiplication of relative approximations. -/
theorem product_relative_error {W θ w s ε : ℝ}
    (hW : 0 ≤ W) (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hw : |w - W| ≤ (ε / 4) * W) (hs : |s - θ| ≤ (ε / 4) * θ) :
    |w * s - W * θ| ≤ ε * (W * θ) := by
  have habw : |w| ≤ (1 + ε / 4) * W := by
    calc
      |w| = |(w - W) + W| := by ring_nf
      _ ≤ |w - W| + |W| := abs_add_le _ _
      _ ≤ (ε / 4) * W + W := by simpa [abs_of_nonneg hW] using add_le_add_right hw W
      _ = (1 + ε / 4) * W := by ring
  calc
    |w * s - W * θ| = |w * (s - θ) + (w - W) * θ| := by ring_nf
    _ ≤ |w| * |s - θ| + |w - W| * θ := by
      simpa [abs_mul, abs_of_nonneg hθ] using abs_add_le (w * (s - θ)) ((w - W) * θ)
    _ ≤ ((1 + ε / 4) * W) * ((ε / 4) * θ) + ((ε / 4) * W) * θ := by
      exact add_le_add (mul_le_mul habw hs (abs_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_right hw hθ)
    _ ≤ ε * (W * θ) := by
      have he : (1 + ε / 4) * (ε / 4) + ε / 4 ≤ ε := by nlinarith
      have := mul_le_mul_of_nonneg_right he (mul_nonneg hW hθ)
      nlinarith

variable {Ω I : Type} [Fintype Ω] [Fintype I]

/-- A complete statistical guarantee for the approximate witness-mixture
estimator. Its inputs explicitly specify the remaining sampling-law and
weight-estimation contracts. -/
theorem approximate_mixture_estimator
    (μ : Mass Ω) (A : I → Ω → Prop) [∀ i, DecidablePred (A i)]
    (p : Law Ω) {w ε : ℝ} {n : ℕ}
    (hW : 0 < μ.totalWeight A) (hε : 0 < ε) (hε1 : ε ≤ 1) (hn : 0 < n)
    (hw : |w - μ.totalWeight A| ≤ (ε / 4) * μ.totalWeight A)
    (hp : l1 p.value (μ.mixture A) ≤ ε / (16 * Fintype.card I)) :
    (∑ xs, if ε * μ.unionMass A <
        |w * Law.sampleAverage (Mass.score A) n xs - μ.unionMass A|
      then (p.samples n).value xs else 0) ≤
      1 / ((n : ℝ) * (ε / (16 * Fintype.card I))^2) := by
  classical
  let θ := μ.unionMass A / μ.totalWeight A
  let m : ℝ := Fintype.card I
  let a := ε / (16 * m)
  have hb := μ.totalWeight_le_card_mul_unionMass A
  have hm : 0 < m := by
    by_contra h
    have hz : m = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
    change μ.totalWeight A ≤ m * μ.unionMass A at hb
    rw [hz, zero_mul] at hb
    linarith
  have ha : 0 < a := div_pos hε (mul_pos (by norm_num) hm)
  have hθ : 0 ≤ θ := div_nonneg (μ.unionMass_nonneg A) hW.le
  have hscore : ∀ x, |Mass.score A x| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (Mass.score_nonneg A x)]
    exact Mass.score_le_one A x
  have hmean : |p.expectation (Mass.score A) - θ| ≤ a := by
    have h := expectation_stability p.value (μ.mixture A) (Mass.score A) hscore
    rw [μ.mixture_score A hW] at h
    exact h.trans hp
  have hscale : 2 * a ≤ (ε / 4) * θ := by
    have hi := μ.inverse_card_le_mean A hW
    change m⁻¹ ≤ θ at hi
    calc
      2 * a = (ε / 8) * m⁻¹ := by dsimp [a]; ring
      _ ≤ (ε / 8) * θ := mul_le_mul_of_nonneg_left hi (by positivity)
      _ ≤ (ε / 4) * θ := by nlinarith
  have hgood (xs : Samples Ω n)
      (hx : |Law.sampleAverage (Mass.score A) n xs - p.expectation (Mass.score A)| < a) :
      |w * Law.sampleAverage (Mass.score A) n xs - μ.unionMass A| ≤ ε * μ.unionMass A := by
    have hs : |Law.sampleAverage (Mass.score A) n xs - θ| ≤ (ε / 4) * θ := by
      calc
        _ ≤ |Law.sampleAverage (Mass.score A) n xs - p.expectation (Mass.score A)| +
            |p.expectation (Mass.score A) - θ| := abs_sub_le _ _ _
        _ ≤ a + a := add_le_add hx.le hmean
        _ ≤ (ε / 4) * θ := by linarith
    have h := product_relative_error hW.le hθ hε.le hε1 hw hs
    have hc : μ.totalWeight A * θ = μ.unionMass A := by dsimp [θ]; field_simp
    simpa [hc] using h
  calc
    _ ≤ ∑ xs, if a ≤ |Law.sampleAverage (Mass.score A) n xs - p.expectation (Mass.score A)|
        then (p.samples n).value xs else 0 := by
      apply Finset.sum_le_sum
      intro xs _
      split_ifs with hbad hlarge
      · rfl
      · exact False.elim (not_lt_of_ge (hgood xs (lt_of_not_ge hlarge)) hbad)
      · exact (p.samples n).nonneg xs
      · rfl
    _ ≤ 1 / ((n : ℝ) * a^2) :=
      p.average_tail _ (Mass.score_nonneg A) (Mass.score_le_one A) hn ha

/-- Constant-confidence sample budget; Chebyshev suffices for the FPRAS
constant-success requirement. Confidence amplification is a separate layer. -/
def sampleBudget (m : ℕ) (ε : ℝ) : ℕ := ⌈1024 * (m : ℝ)^2 / ε^2⌉₊

theorem sampleBudget_pos {m : ℕ} {ε : ℝ} (hm : 0 < m) (hε : 0 < ε) :
    0 < sampleBudget m ε := by
  unfold sampleBudget
  apply Nat.ceil_pos.mpr
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  positivity

theorem sampleBudget_failure {m : ℕ} {ε : ℝ} (hm : 0 < m) (hε : 0 < ε) :
    1 / ((sampleBudget m ε : ℝ) * (ε / (16 * m))^2) ≤ 1 / 4 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hbound := Nat.le_ceil (1024 * (m : ℝ)^2 / ε^2)
  change 1024 * (m : ℝ)^2 / ε^2 ≤ (sampleBudget m ε : ℝ) at hbound
  have hmult := mul_le_mul_of_nonneg_right hbound (sq_nonneg (ε / (16 * m)))
  have heq : (1024 * (m : ℝ)^2 / ε^2) * (ε / (16 * m))^2 = 4 := by
    field_simp
    norm_num
  rw [heq] at hmult
  have hden : 0 < (sampleBudget m ε : ℝ) * (ε / (16 * m))^2 := by linarith
  apply (div_le_iff₀ hden).mpr
  linarith

/-- With the explicit sample budget, the failure probability is at most 1/4.
This is conditional only on the two displayed approximation contracts. -/
theorem approximate_mixture_success
    (μ : Mass Ω) (A : I → Ω → Prop) [∀ i, DecidablePred (A i)]
    (p : Law Ω) {w ε : ℝ}
    (hW : 0 < μ.totalWeight A) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hw : |w - μ.totalWeight A| ≤ (ε / 4) * μ.totalWeight A)
    (hp : l1 p.value (μ.mixture A) ≤ ε / (16 * Fintype.card I)) :
    (∑ xs, if ε * μ.unionMass A <
        |w * Law.sampleAverage (Mass.score A) (sampleBudget (Fintype.card I) ε) xs - μ.unionMass A|
      then (p.samples (sampleBudget (Fintype.card I) ε)).value xs else 0) ≤ 1 / 4 := by
  have hm : 0 < Fintype.card I := by
    by_contra h
    have hz : Fintype.card I = 0 := Nat.eq_zero_of_not_pos h
    have hb := μ.totalWeight_le_card_mul_unionMass A
    rw [hz, Nat.cast_zero, zero_mul] at hb
    linarith
  exact (approximate_mixture_estimator μ A p hW hε hε1
    (sampleBudget_pos hm hε) hw hp).trans (sampleBudget_failure hm hε)

end
end DirectedCycleFPRAS
