module

public import DirectedCycleFPRAS.RecordedExposure
public import DirectedCycleFPRAS.BoundedScores

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
variable {Q Ω I : Type} [Fintype Ω] [Fintype I]

/-- A bounded acceptance probability on every execution, including oracle failures. -/
def rejectionProbability (μ : Mass Ω) (A : I → Ω → Prop) (w : I → ℝ)
    (i : I) (r : Ω × ℝ) : ℝ :=
  if A i r.1 ∧ 0 < μ.value r.1 ∧ 0 < w i ∧ 0 < r.2 then
    max 0 (min 1 (μ.value r.1 / (2 * Mass.multiplicity A r.1 * w i * r.2))) else 0

theorem rejectionProbability_bounds (μ : Mass Ω) (A : I → Ω → Prop) (w : I → ℝ)
    (i : I) (r : Ω × ℝ) :
    0 ≤ rejectionProbability μ A w i r ∧ rejectionProbability μ A w i r ≤ 1 := by
  unfold rejectionProbability
  split_ifs
  · exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  · norm_num

/-- Rejection with its nominal, unrounded bias. -/
def rejectionDraw (h : ℝ) (x : Ω) : Prog Q (Option Ω) :=
  .choose (normLaw (fun b : Bool => if b then h else 1-h) false)
    (fun b => .ret (if b then some x else none))

def acceptedTest (f : Ω → ℝ) : Option Ω → ℝ := fun x => x.elim 0 f

theorem rejectionDraw_exp {h : ℝ} (hh : 0 ≤ h ∧ h ≤ 1) (x : Ω) (f : Ω → ℝ)
    (O : Oracle Q) : (rejectionDraw h x).exp O (acceptedTest f) = h*f x := by
  have hn (b : Bool) : 0 ≤ (if b then h else 1-h) := by cases b <;> simp_all
  have hs : 0 < ∑ b : Bool, (if b then h else 1-h) := by simp
  simp [rejectionDraw, Prog.exp, acceptedTest, normLaw_value _ _ hn hs]

/-- The two properties needed from a recorded conditional proposal. Both are
proved for reliability self-reduction in `recordedRejectionSpec`. -/
structure RejectionSpec (O : Oracle Q) (μ : Mass Ω) (A : I → Ω → Prop)
    (w : I → ℝ) (proposal : I → Prog Q (Ω × ℝ)) : Prop where
  nonneg : ∀ i, 0 ≤ w i
  total_pos : 0 < ∑ i, w i
  support : ∀ i x, A i x → 0 < μ.value x → 0 < w i
  envelope : ∀ i, 0 < w i → Prog.Holds O
    (fun r => A i r.1 ∧ 0 < μ.value r.1 ∧ 0 < r.2 ∧ μ.value r.1 ≤ 2*w i*r.2)
    (proposal i)
  inverse : ∀ i, 0 < w i → ∀ f : Ω → ℝ,
    (proposal i).exp O (fun r => f r.1/r.2) =
      ∑ x, if A i x ∧ 0 < μ.value x then f x else 0

/-- One proposal, returning `none` on rejection and the full configuration on acceptance. -/
def correctedProposal (μ : Mass Ω) (A : I → Ω → Prop) (w : I → ℝ)
    (proposal : I → Prog Q (Ω × ℝ)) (d : I) : Prog Q (Option Ω) :=
  .choose (normLaw w d) fun i => (proposal i).bind fun r =>
    rejectionDraw (rejectionProbability μ A w i r) r.1

theorem rejectionProbability_exact (μ : Mass Ω) (A : I → Ω → Prop) (w : I → ℝ)
    {i : I} {r : Ω × ℝ} (hi : 0 < w i)
    (hr : A i r.1 ∧ 0 < μ.value r.1 ∧ 0 < r.2 ∧ μ.value r.1 ≤ 2*w i*r.2) :
    rejectionProbability μ A w i r = μ.value r.1/(2*Mass.multiplicity A r.1*w i*r.2) := by
  have ht := Mass.one_le_multiplicity hr.1
  have htpos : 0 < Mass.multiplicity A r.1 := lt_of_lt_of_le zero_lt_one ht
  have hg := hr.2.2.1
  have hm := hr.2.1
  have hd : 0 < 2*Mass.multiplicity A r.1*w i*r.2 := by positivity
  have hlo : 0 ≤ μ.value r.1/(2*Mass.multiplicity A r.1*w i*r.2) := by positivity
  have hhi : μ.value r.1/(2*Mass.multiplicity A r.1*w i*r.2) ≤ 1 := by
    apply (div_le_one hd).mpr
    have := mul_le_mul_of_nonneg_right ht (show 0 ≤ 2*w i*r.2 by positivity)
    nlinarith [hr.2.2.2]
  simp [rejectionProbability, hr.1, hr.2.1, hi, hr.2.2.1, min_eq_right hhi, max_eq_right hlo]

/-- Exact cancellation for a single witness, including the oracle transcript. -/
theorem correctedWitness_exp (O : Oracle Q) (μ : Mass Ω) (A : I → Ω → Prop)
    (w : I → ℝ) (proposal : I → Prog Q (Ω × ℝ))
    (H : RejectionSpec O μ A w proposal) {i : I} (hi : 0 < w i) (f : Ω → ℝ) :
    ((proposal i).bind fun r => rejectionDraw (rejectionProbability μ A w i r) r.1).exp O
      (acceptedTest f) =
      ∑ x, if A i x ∧ 0 < μ.value x then
        μ.value x*f x/(2*Mass.multiplicity A x*w i) else 0 := by
  rw [Prog.exp_bind]
  simp_rw [rejectionDraw_exp (rejectionProbability_bounds μ A w _ _)]
  calc
    _ = (proposal i).exp O (fun r =>
        (μ.value r.1*f r.1/(2*Mass.multiplicity A r.1*w i))/r.2) := by
      apply (H.envelope i hi).exp_congr
      intro r hr
      rw [rejectionProbability_exact μ A w hi hr]
      ring
    _ = _ := H.inverse i hi (fun x => μ.value x*f x/(2*Mass.multiplicity A x*w i))

/-- The central identity: the accepted subdistribution is the product law
restricted to the union, scaled by `1/(2 Ŵ)`. -/
theorem correctedProposal_exp (O : Oracle Q) (μ : Mass Ω) (A : I → Ω → Prop)
    (w : I → ℝ) (proposal : I → Prog Q (Ω × ℝ)) (d : I)
    (H : RejectionSpec O μ A w proposal) (f : Ω → ℝ) :
    (correctedProposal μ A w proposal d).exp O (acceptedTest f) =
      (∑ x, if 0 < Mass.multiplicity A x then μ.value x*f x else 0)/(2*∑ i, w i) := by
  unfold correctedProposal
  simp only [Prog.exp, normLaw_value w d H.nonneg H.total_pos]
  have term (i : I) : w i/(∑ j, w j) *
      ((proposal i).bind fun r => rejectionDraw (rejectionProbability μ A w i r) r.1).exp O
        (acceptedTest f) =
      ∑ x, if A i x ∧ 0 < μ.value x then
        μ.value x*f x/(2*Mass.multiplicity A x*(∑ j, w j)) else 0 := by
    by_cases hi : 0 < w i
    · rw [correctedWitness_exp O μ A w proposal H hi f, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs
      · field_simp
      · ring
    · have hz : w i = 0 := le_antisymm (not_lt.mp hi) (H.nonneg i)
      simp only [hz, zero_div, zero_mul]
      symm
      apply Finset.sum_eq_zero
      intro x _
      exact ite_eq_right (fun h => hi (H.support i x h.1 h.2))
  simp_rw [term]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : 0 < Mass.multiplicity A x
  · simp only [ite_eq_left hx]
    by_cases hm : 0 < μ.value x
    · have he : ∀ i, (if A i x ∧ 0 < μ.value x then
          μ.value x*f x/(2*Mass.multiplicity A x*(∑ j, w j)) else 0) =
          (if A i x then (1 : ℝ) else 0) *
            (μ.value x*f x/(2*Mass.multiplicity A x*(∑ j, w j))) := by
        intro i; by_cases h : A i x <;> simp [h, hm]
      simp_rw [he]
      rw [← Finset.sum_mul]
      change Mass.multiplicity A x * _ = _
      field_simp
    · have hz : μ.value x = 0 := le_antisymm (not_lt.mp hm) (μ.nonneg x)
      simp [hz]
  · have hn : ∀ i, ¬ A i x := by
      intro i hi; exact hx ((Mass.multiplicity_pos_iff x).mpr ⟨i, hi⟩)
    simp [hx, hn]

/-- In particular, acceptance probability is `Z/(2 Ŵ)`. -/
theorem correctedProposal_acceptance (O : Oracle Q) (μ : Mass Ω) (A : I → Ω → Prop)
    (w : I → ℝ) (proposal : I → Prog Q (Ω × ℝ)) (d : I)
    (H : RejectionSpec O μ A w proposal) :
    (correctedProposal μ A w proposal d).exp O (acceptedTest (fun _ => 1)) =
      μ.unionMass A/(2*∑ i, w i) := by
  simpa [Mass.unionMass] using correctedProposal_exp O μ A w proposal d H (fun _ => 1)

end
end DirectedCycleFPRAS
