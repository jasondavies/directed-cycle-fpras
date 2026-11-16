module

public import DirectedCycleFPRAS.ConcreteVertex

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
variable {Q E I Ω : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype Ω]

theorem acceptance_average_height (n : ℕ) (xs : Samples (Option Ω) n) :
    Height (max 1 n) (Law.sampleAverage (acceptedTest (fun _ => 1)) n xs) := by
  obtain ⟨C,hC,havg⟩ := sampleSum_common_denominator (acceptedTest (fun _ : Ω => 1)) 1
    (fun x => by
      cases x
      · exact ⟨0, by decide, by simp [acceptedTest]⟩
      · exact ⟨1, by decide, by simp [acceptedTest]⟩) n xs
  unfold Law.sampleAverage
  rw [havg]
  simp only [Nat.cast_one, div_one, Nat.mul_one] at *
  by_cases hn : n = 0
  · simp [hn, height_zero]
  · refine ⟨(C : ℤ), n, Nat.pos_of_ne_zero hn, by simp, ?_, le_max_right _ _⟩
    simpa using hC.trans (le_max_right 1 n)

def countHeight (k n H : ℕ) : ℕ := (2*(2*H)^k)*max 1 n

theorem rejection_count_height (w : I → ℝ) {H : ℕ} (hw : ∀ i, Height H (w i))
    (n : ℕ) (xs : Samples (Option Ω) n) :
    Height (countHeight (Fintype.card I) n H)
      (2*(∑ i, w i)*Law.sampleAverage (acceptedTest (fun _ => 1)) n xs) := by
  have htwo : Height 2 (2 : ℝ) := ⟨2,1,by norm_num,by norm_num,by norm_num,by norm_num⟩
  have hs := height_sum Finset.univ w (fun i _ => hw i)
  simpa [countHeight] using (htwo.mul hs).mul (acceptance_average_height n xs)

theorem initialWeights_sat (mk : I → (E → ℝ) → Q) (feas : I → (E → ℝ) → Prop)
    (p : E → ℝ) (Qp : Q → Prop) (hquery : ∀ i, feas i p → Qp (mk i p))
    {H : ℕ} (hH : 1 ≤ H) (l : List I) :
    Prog.Sat (Height H) Qp (fun w => ∀ i, Height H (w i)) (initialWeights mk feas p l) := by
  induction l with
  | nil => exact .ret _ (fun _ => height_zero hH)
  | cons i l ih =>
    apply Prog.Sat.guarded (hquery i) (height_zero hH)
    intro r hr
    apply ih.bind
    intro w hw
    refine .ret _ ?_
    intro j
    by_cases he : j = i
    · subst j; simpa using hr
    · rw [Function.update_of_ne he]; exact hw j

theorem recordedExpose_sat (mk : (E → ℝ) → Q) (feas : (E → ℝ) → Prop)
    (Inv : (E → ℝ) → Prop) (Qp : Q → Prop) (A : ℝ → Prop) (h0 : A 0)
    (hpin : ∀ q e b, Inv q → Inv (pin q e b))
    (hquery : ∀ q, Inv q → feas q → Qp (mk q))
    (l : List E) (p : E → ℝ) (hp : Inv p) :
    Prog.Sat A Qp (fun _ => True) (recordedExpose mk feas l p) := by
  induction l generalizing p with
  | nil => exact .ret _ trivial
  | cons e l ih =>
    apply Prog.Sat.guarded (hquery _ (hpin p e true hp)) h0
    intro r₁ _
    apply Prog.Sat.guarded (hquery _ (hpin p e false hp)) h0
    intro r₀ _
    apply Prog.Sat.choose
    intro b
    exact (ih _ (hpin p e b hp)).bind fun r _ => .ret _ trivial

/-- All queries remain residual instances, and every counting output has a
polynomial-length fraction even on inaccurate-oracle executions. -/
theorem witnessCount_sat (B : I → (E → Bool) → Prop)
    (mk : I → (E → ℝ) → Q) (feas : I → (E → ℝ) → Prop)
    (Inv : (E → ℝ) → Prop) (Qp : Q → Prop)
    (hpin : ∀ q e b, Inv q → Inv (pin q e b))
    (hquery : ∀ i q, Inv q → feas i q → Qp (mk i q))
    (p : E → ℝ) (hp : Prob01 p) (hpI : Inv p)
    (vertices : List I) (edges : List E) (d : I) (n : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    Prog.Sat (Height H) Qp (Height (countHeight (Fintype.card I) n H))
      (witnessCount B mk feas p hp vertices edges d n) := by
  unfold witnessCount rejectionCount
  apply (initialWeights_sat mk feas p Qp (fun i => hquery i p hpI) hH vertices).bind
  intro w hw
  have hproposal : Prog.Sat (Height H) Qp (fun _ => True)
      (correctedProposal (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass B w
        (fun i => recordedExpose (mk i) (feas i) edges p) d) := by
    apply Prog.Sat.choose
    intro i
    apply (recordedExpose_sat (mk i) (feas i) Inv Qp (Height H) (height_zero hH)
      hpin (hquery i) edges p hpI).bind
    intro r _
    exact .choose _ _ fun _ => .ret _ trivial
  apply (hproposal.replicate n).bind
  intro xs _
  exact .ret _ (rejection_count_height w hw n xs)

namespace Digraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V E) (U : Finset V)

def VertexValid (p : E → ℝ) (x : VertexQuery (E := E) U) : Prop :=
  Derived p x.2 ∧ G.vertexFeasible U x.1 x.2

theorem vertexAlgorithm_sat (p : E → ℝ) (hp : Prob01 p) (n : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    Prog.Sat (Height H) (G.VertexValid U p) (Height (countHeight U.card n H))
      (G.vertexAlgorithm U p hp n) := by
  have hheight : 1 ≤ countHeight U.card n H := by
    unfold countHeight
    have hp : 1 ≤ (2*H)^U.card := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    have hn := le_max_left 1 n
    nlinarith
  unfold vertexAlgorithm
  split_ifs
  · simpa [vertexCore] using witnessCount_sat (G.vertexEvents U) (fun i q => (i,q))
      (G.vertexFeasible U) (Derived p) (G.VertexValid U p) (fun _ e b h => derived_pin h e b)
      (fun _ _ hd hf => ⟨hd,hf⟩) p hp (derived_self p) Finset.univ.toList Finset.univ.toList _ n hH
  · exact .ret _ (height_zero hheight)
  · exact .ret _ (height_zero hheight)

/-- Output-size bound for the same call-free counting program used by the
accuracy and random-bit theorems. -/
theorem concreteVertex_height {p : E → ℝ} (hp01 : Prob01 p) (n b inner outer : ℕ)
    (num den : E → ℕ) {H : ℕ} (hH : 1 ≤ H) (hd : ∀ e, 0 < den e)
    (hn : ∀ e, num e ≤ den e) (hden : ∀ e, den e ≤ H)
    (hp : ∀ e, p e = (num e : ℝ)/den e) :
    Prog.Sat (fun _ => True) (fun _ => True)
      (Height (countHeight U.card n (oracleHeight (Fintype.card (Option V)) (Fintype.card E) H
        (rejectionAccuracy (Fintype.card E))))) (G.concreteVertex U p hp01 n b inner outer) := by
  let Ho := oracleHeight (Fintype.card (Option V)) (Fintype.card E) H (rejectionAccuracy (Fintype.card E))
  have ho : 1 ≤ Ho := by dsimp [Ho,oracleHeight]; omega
  have hc : 1 ≤ countHeight U.card n Ho := by
    unfold countHeight
    have : 1 ≤ (2*Ho)^U.card := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    have := le_max_left 1 n
    nlinarith
  apply (((G.vertexAlgorithm_sat U p hp01 n ho).discretise b).medianOf (height_zero hc) outer).inline
  intro x hx
  exact ((G.splitVertex x.1.val).algSQuery_height (rejectionAccuracy (Fintype.card E))
    num den hH hd hn hden hp (x.2,some x.1.val,none) hx.1).medianOf (height_zero ho) inner

end Digraph
end
end DirectedCycleFPRAS
