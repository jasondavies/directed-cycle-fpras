module

public import DirectedCycleFPRAS.RejectionSampling

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
variable {Q E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

namespace Prog
variable {α : Type}
theorem Holds.exp_le {O : Oracle Q} {P : α → Prop} {m : Prog Q α}
    (h : Holds O P m) (f : α → ℝ) {c : ℝ} (hf : ∀ x, P x → f x ≤ c) : m.exp O f ≤ c := by
  have he := h.exp_congr (f := f) (g := fun x => min (f x) c)
    (fun x hx => (min_eq_left (hf x hx)).symm)
  rw [he]
  exact exp_le_of_le O m fun x => min_le_right _ _
end Prog

/-- Initial witness weights use exact feasibility guards, so zero weights stay zero. -/
def initialWeights (mk : I → (E → ℝ) → Q) (feas : I → (E → ℝ) → Prop) (p : E → ℝ) :
    List I → Prog Q (I → ℝ)
  | [] => .ret (fun _ => 0)
  | i :: l => Prog.guarded (feas i p) (mk i p) fun r =>
      (initialWeights mk feas p l).bind fun w => .ret (Function.update w i r)

theorem initialWeights_accurate (O : Oracle Q) (B : I → (E → Bool) → Prop)
    (mk : I → (E → ℝ) → Q) (feas : I → (E → ℝ) → Prop)
    (p : E → ℝ) (hp : Prob01 p) {a : ℝ}
    (hfeas : ∀ i, feas i p ↔ 0 < eventMass p (B i))
    (hacc : ∀ i, 0 < eventMass p (B i) → ∀ s,
      |O.answer (mk i p) s-eventMass p (B i)| ≤ a*eventMass p (B i)) (l : List I) :
    Prog.Holds O (fun w => ∀ i ∈ l, |w i-eventMass p (B i)| ≤ a*eventMass p (B i))
      (initialWeights mk feas p l) := by
  induction l with
  | nil => exact .ret _ (by simp)
  | cons i l ih =>
    unfold initialWeights
    apply Prog.Holds.guarded
    intro s
    have hr : |(if feas i p then O.answer (mk i p) s else 0)-eventMass p (B i)| ≤ a*eventMass p (B i) := by
      by_cases hf : feas i p
      · simpa [hf] using hacc i ((hfeas i).mp hf) s
      · have hz : eventMass p (B i) = 0 := le_antisymm
          (not_lt.mp (fun h => hf ((hfeas i).mpr h))) (eventMass_nonneg hp _)
        simp [hf, hz]
    apply ih.bind
    intro w hw
    refine .ret _ ?_
    intro j hj
    by_cases he : j = i
    · subst j; simpa using hr
    · rw [Function.update_of_ne he]
      exact hw j (List.mem_cons.mp hj |>.resolve_left he)

/-- The full counting program: initialize the cover weights, then run corrected
rejection with those same recorded weights for every proposal. -/
def witnessCount (B : I → (E → Bool) → Prop)
    (mk : I → (E → ℝ) → Q) (feas : I → (E → ℝ) → Prop)
    (p : E → ℝ) (hp : Prob01 p) (vertices : List I) (edges : List E) (d : I) (n : ℕ) : Prog Q ℝ :=
  (initialWeights mk feas p vertices).bind fun w =>
    rejectionCount (correctedProposal
      (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass B w
      (fun i => recordedExpose (mk i) (feas i) edges p) d) (∑ i, w i) n

/-- Accuracy for the full program, including randomized initial weights and
fresh adaptive oracle calls in every recorded proposal. -/
theorem witnessCount_ideal (O : Oracle Q) (B : I → (E → Bool) → Prop)
    (mk : I → (E → ℝ) → Q) (feas : I → (E → ℝ) → Prop)
    (Inv : (E → ℝ) → Prop) (hInv : ∀ q, Inv q → Prob01 q)
    (hpin : ∀ q e b, Inv q → Inv (pin q e b))
    (hfeas : ∀ i q, Inv q → (feas i q ↔ 0 < eventMass q (B i)))
    (p : E → ℝ) (hp : Inv p) (vertices : List I) (hv : ∀ i, i ∈ vertices)
    (edges : List E) (he : ∀ e, e ∈ edges) (d : I)
    (hacc : ∀ i q, Inv q → 0 < eventMass q (B i) → ∀ s,
      |O.answer (mk i q) s-eventMass q (B i)| ≤ rejectionAccuracy edges.length*eventMass q (B i))
    (hZ : 0 < (edgeLaw p (fun e => (hInv p hp e).1) (fun e => (hInv p hp e).2)).toMass.unionMass B)
    {eps : ℝ} (heps : 0 < eps) {n : ℕ} (hn : 64*(Fintype.card I : ℝ)/eps^2 ≤ n) :
    let μ := (edgeLaw p (fun e => (hInv p hp e).1) (fun e => (hInv p hp e).2)).toMass
    (witnessCount B mk feas p (hInv p hp) vertices edges d n).exp O
      (fun z => if eps*μ.unionMass B ≤ |z-μ.unionMass B| then 1 else 0) ≤ 1/16 := by
  let μ := (edgeLaw p (fun e => (hInv p hp e).1) (fun e => (hInv p hp e).2)).toMass
  have hW : 0 < ∑ i, eventMass p (B i) :=
    lt_of_lt_of_le hZ (μ.unionMass_le_totalWeight B)
  dsimp only
  unfold witnessCount
  rw [Prog.exp_bind]
  apply (initialWeights_accurate O B mk feas p (hInv p hp)
    (fun i => hfeas i p hp) (fun i => hacc i p hp) vertices).exp_le
  intro w hw
  have hw' := fun i => hw i (hv i)
  have H := recordedRejectionSpec O B mk feas Inv hInv hpin hfeas p hp edges he w hW hw' hacc
  apply correctedCount_ideal O μ B w _ d H hZ (a := rejectionAccuracy edges.length)
    (by have := (rejectionAccuracy_bounds edges.length).2; linarith) _ heps hn
  intro i
  exact hw' i

end
end DirectedCycleFPRAS
