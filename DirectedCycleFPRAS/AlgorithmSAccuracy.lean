module

public import DirectedCycleFPRAS.AlgorithmSRounds

@[expose] public section

/-! Feng--Fu--Guo Theorem 9 for the concrete Algorithm S transcription.
No reliability-accuracy or DFS-correspondence hypothesis is assumed. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [ArcEnumeration E] [DecidableEq E]
variable (G : Digraph V E) (p : E → ℝ)

/-- Theorem 9's relative-error bound with an arbitrary sufficient sample
budget, directly on the unreduced graph and the actual `algS` program. -/
theorem algS_accuracy (hp : Prob01 p) (s t : V) {M : ℕ} (hM : 0<M)
    (hq : 0<G.reliability p s t) {α δ : ℝ} (hα : 0<α)
    (hgrowth : 2*(Fintype.card V : ℝ)^2*Fintype.card E≤M)
    (hbudget : 2*(Fintype.card V : ℝ)^3*Fintype.card E≤δ*α^2*M) :
    (G.algS (Q := Empty) p s t M).exp noOracle
      (fun z => if |z-G.reliability p s t|≤α*G.reliability p s t then 0 else 1) ≤ δ := by
  let n := Fintype.card V
  let m := Fintype.card E
  let q := G.reliability p s t
  let K := G.roundStep p (s := s) (M := M) t
  let F := G.roundPrediction p (s := s) (M := M) t
  let Ψ := G.roundTotal p (s := s) (M := M)
  let a := G.initialRound p s hM
  have hMr : (0 : ℝ)<M := by exact_mod_cast hM
  have hc : 0≤(n : ℝ)*m/M := by positivity
  have hd : 0≤((m : ℝ)/M)*q^2 := by positivity
  have hn : (n : ℝ)*((n : ℝ)*m/M)≤1/2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
    have he : (n : ℝ)*(n*m/M)*2=(2*n^2*m)/M := by ring
    rw [he]
    exact (div_le_one hMr).mpr hgrowth
  have hmeanF : ∀ b, (K b).exp noOracle F = F b :=
    fun b => (G.roundStep_mean p hp hM t t b).1
  have hmeanΨ : ∀ b, (K b).exp noOracle Ψ = Ψ b :=
    fun b => (G.roundStep_mean p hp hM t t b).2
  have hvF : ∀ b, (K b).exp noOracle (fun c => (F c-F b)^2) ≤ ((m : ℝ)/M)*q^2*(Ψ b)^2 :=
    fun b => (G.roundStep_variance p hp hM t hq b).1
  have hvΨ : ∀ b, (K b).exp noOracle (fun c => (Ψ c-Ψ b)^2) ≤ ((n : ℝ)*m/M)*(Ψ b)^2 :=
    fun b => (G.roundStep_variance p hp hM t hq b).2
  have hFa : F a=q := G.prediction_initial p hp s t
  have hΨ0 : 0≤Ψ a := G.totalPrediction_nonneg p hp s _ _ _ a.property.1.nonneg
  have hΨn : Ψ a≤n := G.totalPrediction_initial p hp s
  have hsq : (Ψ a)^2≤(n : ℝ)^2 := by nlinarith
  have hv := Prog.steps_variance_le noOracle K F Ψ hc hd hmeanF hmeanΨ hvF hvΨ n hn a
  rw [hFa] at hv
  have hv' : (Prog.steps K n a).exp noOracle (fun b => (F b-q)^2) ≤
      2*((m : ℝ)/M)*q^2*n*(n : ℝ)^2 := by
    apply hv.trans
    have h := mul_le_mul_of_nonneg_left hsq (show 0≤2*(((m : ℝ)/M)*q^2)*n by positivity)
    convert h using 1; ring
  rw [G.algS_steps_law p hp s t hM]
  apply (Prog.chebyshev noOracle (Prog.steps K n a) F q (mul_pos hα hq)).trans
  apply (div_le_iff₀ (sq_pos_of_pos (mul_pos hα hq))).mpr
  apply hv'.trans
  have hb := mul_le_mul_of_nonneg_right hbudget (sq_nonneg q)
  apply (mul_le_mul_iff_left₀ hMr).mp
  convert hb using 1 <;> dsimp [n,m,q] <;> field_simp

end Digraph

/-- The concrete Algorithm S accuracy contract is a theorem for positive
accuracy at most one. Its sample budget is computed on the ambient graph. -/
theorem algSAccurate {α : ℝ} (hα : 0<α) (hα1 : α≤1) : AlgSAccurate α := by
  intro V E _ _ _ G p s t hp hq
  let : DecidableEq V := Classical.decEq V
  have hp01 : Prob01 p := fun e => ⟨(hp e).1.le,(hp e).2⟩
  by_cases hst : s=t
  · subst t
    rw [G.algS_self,G.reliability_self]
    simp [Prog.exp,hα.le]
  · have hpath := (G.reliability_pos_iff hp01 s t).mp hq
    have hE : Nonempty E := by
      rcases Relation.ReflTransGen.cases_tail hpath with heq | ⟨u,_,hedge⟩
      · exact False.elim (hst heq.symm)
      · obtain ⟨e,_,_,_⟩ := hedge
        exact ⟨e⟩
    have hn : 0<Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
    have hm : 0<Fintype.card E := Fintype.card_pos_iff.mpr hE
    have hMr : (0 : ℝ)<algSSamples (Fintype.card V) (Fintype.card E) α := by
      have hb : 16*(Fintype.card V : ℝ)^3*Fintype.card E/α^2 ≤
          algSSamples (Fintype.card V) (Fintype.card E) α := Nat.le_ceil _
      exact lt_of_lt_of_le (by positivity) hb
    have hM : 0<algSSamples (Fintype.card V) (Fintype.card E) α := by exact_mod_cast hMr
    have hb := Prog.algSSamples_bounds hn (le_refl (Fintype.card V)) (le_refl (Fintype.card E)) hα hα1
    exact G.algS_accuracy p hp01 s t hM hq hα hb.1 hb.2

/-- The finite-bit Algorithm S estimator satisfies the reliability contract. -/
theorem algSEstimator_correct {α : ℝ} (hα : 0<α) (hα1 : α≤1) :
    (algSEstimator α).Correct α :=
  algSEstimator_correct_of_accurate (algSAccurate hα hα1)

end
end DirectedCycleFPRAS
