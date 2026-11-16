module

public import DirectedCycleFPRAS.RejectionResources

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
variable {Q E I Ω : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype Ω]

namespace Prog
variable {α : Type}
theorem exp_complement (O : Oracle Q) (m : Prog Q α) (f : α → ℝ) :
    m.exp O (fun x => 1-f x) = 1-m.exp O f := by
  have he : (fun x => 1-f x) = fun x => (1 : ℝ)+(-1)*f x := by funext x; ring
  rw [he, exp_add, exp_const, exp_mul_left]
  ring

theorem exp_repair_abs (O : Oracle Q) (good : Q → ℝ → Prop) (fix : Q → ℝ)
    {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : ∀ x, (∑ s, if good x (O.answer x s) then 0 else (O.law x).value s) ≤ γ)
    (m : Prog Q α) {T : ℕ} (hT : QueryBound m T)
    (f : α → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    |m.exp O f-m.exp (O.repair good fix) f| ≤ (T : ℝ)*γ := by
  have hu := exp_le_repair O good fix hγ0 hγ hf0 hf1 hT
  have hl := exp_le_repair O good fix hγ0 hγ
    (fun x => sub_nonneg.mpr (hf1 x)) (fun x => by linarith [hf0 x]) hT
  simp only [exp_complement] at hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem finiteBit_error (O : Oracle Q) (good : Q → ℝ → Prop) (fix : Q → ℝ)
    {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : ∀ x, (∑ s, if good x (O.answer x s) then 0 else (O.law x).value s) ≤ γ)
    (m : Prog Q α) {T A : ℕ} (hT : QueryBound m T) (hA : ChoiceBound m A)
    (b : ℕ) (f : α → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    {β target : ℝ} (hideal : |m.exp (O.repair good fix) f-target| ≤ β) :
    |(m.discretise b).exp O f-target| ≤ β+(T : ℝ)*γ+(A : ℝ)/(2 : ℝ)^b := by
  have hr := exp_repair_abs O good fix hγ0 hγ m hT f hf0 hf1
  have hd := exp_discretise_le O b hf0 hf1 hA
  have h₁ := abs_sub_le ((m.discretise b).exp O f) (m.exp O f) target
  have h₂ := abs_sub_le (m.exp O f) (m.exp (O.repair good fix) f) target
  linarith

theorem Holds.exp_abs_le {O : Oracle Q} {P : α → Prop} {m : Prog Q α}
    (h : Holds O P m) (f : α → ℝ) {c β : ℝ}
    (hf : ∀ x, P x → |f x-c| ≤ β) : |m.exp O f-c| ≤ β := by
  have hu := h.exp_le f (c := c+β) (fun x hx => by have := (abs_le.mp (hf x hx)).2; linarith)
  have hl := h.exp_le (fun x => (-1)*f x) (c := β-c)
    (fun x hx => by have := (abs_le.mp (hf x hx)).1; linarith)
  rw [exp_mul_left] at hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩
end Prog

def witnessSample (B : I → (E → Bool) → Prop)
    (mk : I → (E → ℝ) → Q) (feas : I → (E → ℝ) → Prop)
    (p : E → ℝ) (hp : Prob01 p) (vertices : List I) (edges : List E)
    (d : I) (fallback : E → Bool) (L : ℕ) : Prog Q (E → Bool) :=
  (initialWeights mk feas p vertices).bind fun w =>
    cappedSample (correctedProposal
      (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass B w
      (fun i => recordedExpose (mk i) (feas i) edges p) d) fallback L

/-- Full conditional sampling theorem, including initialization. The bound
holds for every `[0,1]` test function, hence for total variation. -/
theorem witnessSample_ideal (O : Oracle Q) (B : I → (E → Bool) → Prop)
    (mk : I → (E → ℝ) → Q) (feas : I → (E → ℝ) → Prop)
    (Inv : (E → ℝ) → Prop) (hInv : ∀ q, Inv q → Prob01 q)
    (hpin : ∀ q e b, Inv q → Inv (pin q e b))
    (hfeas : ∀ i q, Inv q → (feas i q ↔ 0 < eventMass q (B i)))
    (p : E → ℝ) (hp : Inv p) (vertices : List I) (hv : ∀ i, i ∈ vertices)
    (edges : List E) (he : ∀ e, e ∈ edges) (d : I)
    (hacc : ∀ i q, Inv q → 0 < eventMass q (B i) → ∀ s,
      |O.answer (mk i q) s-eventMass q (B i)| ≤ rejectionAccuracy edges.length*eventMass q (B i))
    (hZ : 0 < (edgeLaw p (fun e => (hInv p hp e).1) (fun e => (hInv p hp e).2)).toMass.unionMass B)
    (fallback : E → Bool) (r : ℕ) (f : (E → Bool) → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    let μ := (edgeLaw p (fun e => (hInv p hp e).1) (fun e => (hInv p hp e).2)).toMass
    |(witnessSample B mk feas p (hInv p hp) vertices edges d fallback (4*Fintype.card I*r)).exp O f-
      (unionLaw μ B hZ).expectation f| ≤ (1/2 : ℝ)^r := by
  dsimp only
  let μ := (edgeLaw p (fun e => (hInv p hp e).1) (fun e => (hInv p hp e).2)).toMass
  have hW : 0 < ∑ i, eventMass p (B i) := lt_of_lt_of_le hZ (μ.unionMass_le_totalWeight B)
  unfold witnessSample
  rw [Prog.exp_bind]
  apply (initialWeights_accurate O B mk feas p (hInv p hp)
    (fun i => hfeas i p hp) (fun i => hacc i p hp) vertices).exp_abs_le
  intro w hw
  have hw' := fun i => hw i (hv i)
  have H := recordedRejectionSpec O B mk feas Inv hInv hpin hfeas p hp edges he w hW hw' hacc
  let P := correctedProposal μ B w (fun i => recordedExpose (mk i) (feas i) edges p) d
  let q := μ.unionMass B/(2*∑ i, w i)
  have hmean : P.exp O (acceptedTest (fun _ => 1)) = q := correctedProposal_acceptance O μ B w _ d H
  have hq0 : 0 ≤ q := by
    rw [← hmean]
    exact Prog.exp_nonneg O P (fun x => by cases x <;> norm_num [acceptedTest])
  have hq1 : q ≤ 1 := by
    rw [← hmean]
    exact Prog.exp_le_of_le O P (fun x => by cases x <;> norm_num [acceptedTest])
  have hupper := estimatedWeight_upper μ B w
    (show rejectionAccuracy edges.length ≤ 1 by have := (rejectionAccuracy_bounds edges.length).2; linarith)
    hw'
  have hk := acceptance_lower H.total_pos hZ hupper
  have hqd : 1 ≤ ((4*Fintype.card I : ℕ) : ℝ)*q := by
    have hk' : (0 : ℝ) < Fintype.card I := by exact_mod_cast hk.1
    have hh := (div_le_iff₀ (show 0 < 4*(Fintype.card I : ℝ) by positivity)).mp hk.2
    simpa [Nat.cast_mul, mul_comm, q, μ] using hh
  exact (cappedSample_error O P fallback (unionLaw μ B hZ) ⟨hq0,hq1⟩
    (correctedProposal_conditional O μ B w _ d H hZ) _ f hf0 hf1).trans
      (rejection_timeout hq0 hq1 (by omega) hqd r)

theorem cappedSample_queryBound (proposal : Prog Q (Option Ω)) (fallback : Ω)
    {T : ℕ} (hT : Prog.QueryBound proposal T) (L : ℕ) :
    Prog.QueryBound (cappedSample proposal fallback L) (L*T) := by
  induction L with
  | zero => exact .ret _ _
  | succ L ih =>
    have h : Prog.QueryBound (cappedSample proposal fallback (L+1)) (T+L*T) := by
      apply hT.bind
      intro x
      cases x
      · exact ih
      · exact .ret _ _
    exact h.mono (by rw [Nat.succ_mul]; omega)

theorem cappedSample_choiceBound (proposal : Prog Q (Option Ω)) (fallback : Ω)
    {A : ℕ} (hA : Prog.ChoiceBound proposal A) (L : ℕ) :
    Prog.ChoiceBound (cappedSample proposal fallback L) (L*A) := by
  induction L with
  | zero => exact .ret _ _
  | succ L ih =>
    have h : Prog.ChoiceBound (cappedSample proposal fallback (L+1)) (A+L*A) := by
      apply hA.bind
      intro x
      cases x
      · exact ih
      · exact .ret _ _
    exact h.mono (by rw [Nat.succ_mul]; omega)

theorem witnessSample_queryBound (B : I → (E → Bool) → Prop)
    (mk : I → (E → ℝ) → Q) (feas : I → (E → ℝ) → Prop)
    (p : E → ℝ) (hp : Prob01 p) (vertices : List I) (edges : List E)
    (d : I) (fallback : E → Bool) (L : ℕ) :
    Prog.QueryBound (witnessSample B mk feas p hp vertices edges d fallback L)
      (vertices.length+2*edges.length*L) := by
  unfold witnessSample
  apply (initialWeights_queryBound mk feas p vertices).bind
  intro w
  have h := correctedProposal_queryBound (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass B w _ d
    (fun i => recordedExpose_queryBound (mk i) (feas i) edges p)
  exact (cappedSample_queryBound _ fallback h L).mono (by simp [Nat.mul_comm])

theorem witnessSample_choiceBound (B : I → (E → Bool) → Prop)
    (mk : I → (E → ℝ) → Q) (feas : I → (E → ℝ) → Prop)
    (p : E → ℝ) (hp : Prob01 p) (vertices : List I) (edges : List E)
    (d : I) (fallback : E → Bool) (L : ℕ) :
    Prog.ChoiceBound (witnessSample B mk feas p hp vertices edges d fallback L)
      (L*(Fintype.card I+2*edges.length+2)) := by
  unfold witnessSample
  have h : Prog.ChoiceBound ((initialWeights mk feas p vertices).bind fun w =>
      cappedSample (correctedProposal (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass B w
        (fun i => recordedExpose (mk i) (feas i) edges p) d) fallback L)
      (0+L*(Fintype.card I+2*edges.length+2)) := by
    apply (initialWeights_choiceBound mk feas p vertices).bind
    intro w
    apply cappedSample_choiceBound
    exact correctedProposal_choiceBound _ B w _ d
      (fun i => recordedExpose_choiceBound (mk i) (feas i) edges p)
  simpa using h

end
end DirectedCycleFPRAS
