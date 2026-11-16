module

public import DirectedCycleFPRAS.RecordedRejection
public import DirectedCycleFPRAS.Confidence

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {Q Ω I : Type} [Fintype Ω] [Fintype I]

/-- The estimator accumulates acceptance bits and scales their average. -/
def rejectionCount (proposal : Prog Q (Option Ω)) (W : ℝ) (n : ℕ) : Prog Q ℝ :=
  (proposal.replicate n).bind fun xs =>
    .ret (2*W*Law.sampleAverage (acceptedTest (fun _ => 1)) n xs)

/-- A weight sum at most `2kZ` guarantees acceptance at least `1/(4k)`. -/
theorem acceptance_lower {W Z : ℝ} {k : ℕ} (hW : 0 < W) (_hZ : 0 < Z)
    (hupper : W ≤ 2*(k : ℝ)*Z) : 0 < k ∧ 1/(4*(k : ℝ)) ≤ Z/(2*W) := by
  have hk : (0 : ℝ) < k := by
    by_contra hn
    have : (k : ℝ) = 0 := le_antisymm (not_lt.mp hn) (Nat.cast_nonneg k)
    simp [this] at hupper
    linarith
  refine ⟨by exact_mod_cast hk, ?_⟩
  apply (div_le_div_iff₀ (by positivity : 0 < 4*(k : ℝ)) (by positivity : 0 < 2*W)).mpr
  nlinarith

/-- The paper's constant-confidence counting theorem, conditional on any
accurate initial weight estimates. -/
theorem rejectionCount_ideal (O : Oracle Q) (proposal : Prog Q (Option Ω))
    {W Z : ℝ} (hW : 0 < W) (hZ : 0 < Z) {k : ℕ} (hupper : W ≤ 2*(k : ℝ)*Z)
    (hmean : proposal.exp O (acceptedTest (fun _ => 1)) = Z/(2*W))
    {eps : ℝ} (heps : 0 < eps) {n : ℕ} (hn : 64*(k : ℝ)/eps^2 ≤ n) :
    (rejectionCount proposal W n).exp O (fun z => if eps*Z ≤ |z-Z| then 1 else 0) ≤ 1/16 := by
  let f : Option Ω → ℝ := acceptedTest (fun _ => 1)
  have hf0 : ∀ x, 0 ≤ f x := by intro x; cases x <;> norm_num [f, acceptedTest]
  have hf1 : ∀ x, f x ≤ 1 := by intro x; cases x <;> norm_num [f, acceptedTest]
  have he : (proposal.law O).expectation f = Z/(2*W) := by
    rw [← hmean, Prog.exp_eq_sum_law]; rfl
  have hl := acceptance_lower hW hZ hupper
  have ht := (proposal.law O).relative_average_tail f hf0 hf1 hl.1 heps (by rw [he]; exact hl.2) hn
  have equiv (xs : Samples (Option Ω) n) :
      (eps*Z ≤ |2*W*Law.sampleAverage f n xs-Z|) ↔
        (eps*(proposal.law O).expectation f ≤ |Law.sampleAverage f n xs-(proposal.law O).expectation f|) := by
    rw [he]
    have hz : 2*W*Law.sampleAverage f n xs-Z =
        (2*W)*(Law.sampleAverage f n xs-Z/(2*W)) := by field_simp
    rw [hz, abs_mul, abs_of_pos (show 0 < 2*W by positivity)]
    rw [← div_le_iff₀' (show 0 < 2*W by positivity)]
    ring
  unfold rejectionCount
  rw [Prog.exp_bind, Prog.exp_replicate]
  change (∑ xs, _ * (if eps*Z ≤ |2*W*Law.sampleAverage f n xs-Z| then (1 : ℝ) else 0)) ≤ _
  simp_rw [equiv, mul_ite, mul_one, mul_zero]
  exact ht

/-- Accuracy of initial weights gives the required overlap-dependent upper bound. -/
theorem estimatedWeight_upper (μ : Mass Ω) (A : I → Ω → Prop) (w : I → ℝ)
    {a : ℝ} (ha : a ≤ 1) (hw : ∀ i, |w i-μ.weight A i| ≤ a*μ.weight A i) :
    (∑ i, w i) ≤ 2*(Fintype.card I : ℝ)*μ.unionMass A := by
  calc
    (∑ i, w i) ≤ 2*μ.totalWeight A := by
      unfold Mass.totalWeight
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have h := (abs_le.mp (hw i)).2
      have hm := μ.weight_nonneg A i
      nlinarith [mul_le_mul_of_nonneg_right ha hm]
    _ ≤ 2*((Fintype.card I : ℝ)*μ.unionMass A) :=
      mul_le_mul_of_nonneg_left (μ.totalWeight_le_card_mul_unionMass A) (by norm_num)
    _ = _ := by ring

/-- The corrected rejection program has the claimed `64k/eps²` sample budget. -/
theorem correctedCount_ideal (O : Oracle Q) (μ : Mass Ω) (A : I → Ω → Prop)
    (w : I → ℝ) (proposal : I → Prog Q (Ω × ℝ)) (d : I)
    (H : RejectionSpec O μ A w proposal) (hZ : 0 < μ.unionMass A)
    {a : ℝ} (ha : a ≤ 1) (hw : ∀ i, |w i-μ.weight A i| ≤ a*μ.weight A i)
    {eps : ℝ} (heps : 0 < eps) {n : ℕ} (hn : 64*(Fintype.card I : ℝ)/eps^2 ≤ n) :
    (rejectionCount (correctedProposal μ A w proposal d) (∑ i, w i) n).exp O
      (fun z => if eps*μ.unionMass A ≤ |z-μ.unionMass A| then 1 else 0) ≤ 1/16 :=
  rejectionCount_ideal O _ H.total_pos hZ (estimatedWeight_upper μ A w ha hw)
    (correctedProposal_acceptance O μ A w proposal d H) heps hn

end
end DirectedCycleFPRAS
