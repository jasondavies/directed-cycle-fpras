module

public import DirectedCycleFPRAS.WitnessAlgorithm

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {Q E I Ω : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype Ω]

namespace Prog
variable {α : Type}
theorem ChoiceBound.guarded {c : Prop} {x : Q} {k : ℝ → Prog Q α} {n : ℕ}
    (h : ∀ r, ChoiceBound (k r) n) : ChoiceBound (Prog.guarded c x k) n := by
  unfold Prog.guarded
  refine .work _ _ _ ?_
  split_ifs
  · exact .query _ _ _ h
  · exact h 0

theorem ChoiceBound.replicate {m : Prog Q α} {a : ℕ} (h : ChoiceBound m a) (n : ℕ) :
    ChoiceBound (m.replicate n) (n*a) := by
  induction n with
  | zero => exact .ret _ _
  | succ n ih =>
    exact (h.bind fun x => ih.bind fun xs => .ret _ 0).mono (by rw [Nat.succ_mul]; omega)

/-- Coupling is applied to bounded losses without conditioning on the event
that every oracle answer was accurate. -/
theorem finiteBit_failure (O : Oracle Q) (good : Q → ℝ → Prop) (fix : Q → ℝ)
    {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : ∀ x, (∑ s, if good x (O.answer x s) then 0 else (O.law x).value s) ≤ γ)
    (m : Prog Q α) {T A : ℕ} (hT : QueryBound m T) (hA : ChoiceBound m A)
    (b : ℕ) (f : α → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    {β : ℝ} (hideal : m.exp (O.repair good fix) f ≤ β) :
    (m.discretise b).exp O f ≤ β+(T : ℝ)*γ+(A : ℝ)/(2 : ℝ)^b := by
  have hr := exp_le_repair O good fix hγ0 hγ hf0 hf1 hT
  have hd := (abs_le.mp (exp_discretise_le O b hf0 hf1 hA)).2
  linarith
end Prog

theorem initialWeights_queryBound (mk : I → (E → ℝ) → Q) (feas : I → (E → ℝ) → Prop)
    (p : E → ℝ) (l : List I) : Prog.QueryBound (initialWeights mk feas p l) l.length := by
  induction l with
  | nil => exact .ret _ _
  | cons i l ih =>
    exact .guarded fun r => (ih.bind fun w => .ret _ 0).mono (by simp)

theorem initialWeights_choiceBound (mk : I → (E → ℝ) → Q) (feas : I → (E → ℝ) → Prop)
    (p : E → ℝ) (l : List I) : Prog.ChoiceBound (initialWeights mk feas p l) 0 := by
  induction l with
  | nil => exact .ret _ _
  | cons i l ih => exact .guarded fun r => ih.bind fun w => .ret _ 0

theorem recordedExpose_queryBound (mk : (E → ℝ) → Q) (feas : (E → ℝ) → Prop)
    (l : List E) (p : E → ℝ) : Prog.QueryBound (recordedExpose mk feas l p) (2*l.length) := by
  induction l generalizing p with
  | nil => exact .ret _ _
  | cons e l ih =>
    have h : Prog.QueryBound (recordedExpose mk feas (e::l) p) ((2*l.length+1)+1) :=
      .guarded fun r₁ => .guarded fun r₀ => .choose _ _ _ fun b =>
        ((ih (pin p e b)).bind fun r => .ret _ 0).mono (by simp)
    exact h.mono (by simp; omega)

theorem recordedExpose_choiceBound (mk : (E → ℝ) → Q) (feas : (E → ℝ) → Prop)
    (l : List E) (p : E → ℝ) : Prog.ChoiceBound (recordedExpose mk feas l p) (2*l.length) := by
  induction l generalizing p with
  | nil => exact .ret _ _
  | cons e l ih =>
    have h : Prog.ChoiceBound (recordedExpose mk feas (e::l) p) (Fintype.card Bool+2*l.length) :=
      .guarded fun r₁ => .guarded fun r₀ => .choose _ _ _ fun b =>
        ((ih (pin p e b)).bind fun r => .ret _ 0).mono (by simp)
    exact h.mono (by simp; omega)

theorem correctedProposal_queryBound (μ : Mass Ω) (B : I → Ω → Prop) (w : I → ℝ)
    (proposal : I → Prog Q (Ω × ℝ)) (d : I) {T : ℕ}
    (hT : ∀ i, Prog.QueryBound (proposal i) T) :
    Prog.QueryBound (correctedProposal μ B w proposal d) T := by
  apply Prog.QueryBound.choose
  intro i
  exact ((hT i).bind fun r => Prog.QueryBound.choose _ _ 0 fun _ => .ret _ _).mono (by simp)

theorem correctedProposal_choiceBound (μ : Mass Ω) (B : I → Ω → Prop) (w : I → ℝ)
    (proposal : I → Prog Q (Ω × ℝ)) (d : I) {A : ℕ}
    (hA : ∀ i, Prog.ChoiceBound (proposal i) A) :
    Prog.ChoiceBound (correctedProposal μ B w proposal d) (Fintype.card I+A+2) := by
  have h : Prog.ChoiceBound (correctedProposal μ B w proposal d) (Fintype.card I+(A+2)) := by
    apply Prog.ChoiceBound.choose
    intro i
    apply (hA i).bind
    intro r
    exact Prog.ChoiceBound.choose _ _ 0 fun _ => .ret _ _
  exact h.mono (by omega)

theorem witnessCount_queryBound (B : I → (E → Bool) → Prop)
    (mk : I → (E → ℝ) → Q) (feas : I → (E → ℝ) → Prop)
    (p : E → ℝ) (hp : Prob01 p) (vertices : List I) (edges : List E) (d : I) (n : ℕ) :
    Prog.QueryBound (witnessCount B mk feas p hp vertices edges d n)
      (vertices.length+2*edges.length*n) := by
  unfold witnessCount rejectionCount
  apply (initialWeights_queryBound mk feas p vertices).bind
  intro w
  have h := correctedProposal_queryBound (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass B w _ d (fun i => recordedExpose_queryBound (mk i) (feas i) edges p)
  exact ((h.replicate n).bind fun xs => .ret _ 0).mono (by simp [Nat.mul_comm])

theorem witnessCount_choiceBound (B : I → (E → Bool) → Prop)
    (mk : I → (E → ℝ) → Q) (feas : I → (E → ℝ) → Prop)
    (p : E → ℝ) (hp : Prob01 p) (vertices : List I) (edges : List E) (d : I) (n : ℕ) :
    Prog.ChoiceBound (witnessCount B mk feas p hp vertices edges d n)
      (n*(Fintype.card I+2*edges.length+2)) := by
  unfold witnessCount rejectionCount
  have hi := initialWeights_choiceBound mk feas p vertices
  have h : Prog.ChoiceBound ((initialWeights mk feas p vertices).bind fun w =>
      ((correctedProposal (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass B w
        (fun i => recordedExpose (mk i) (feas i) edges p) d).replicate n).bind
        fun xs => .ret (2*(∑ i, w i)*Law.sampleAverage (acceptedTest (fun _ => 1)) n xs))
      (0+n*(Fintype.card I+2*edges.length+2)) := by
    apply hi.bind
    intro w
    have h := correctedProposal_choiceBound (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass B w _ d
      (fun i => recordedExpose_choiceBound (mk i) (feas i) edges p)
    exact ((h.replicate n).bind fun xs => .ret _ 0).mono (by simp)
  exact h.mono (by simp)

end
end DirectedCycleFPRAS
