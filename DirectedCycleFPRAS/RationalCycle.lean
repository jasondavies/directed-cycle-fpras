module

public import DirectedCycleFPRAS.RationalExposure
public import DirectedCycleFPRAS.RationalRejection
public import DirectedCycleFPRAS.VertexSampling

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
set_option linter.unusedSectionVars false

namespace RatProg
variable {Q α : Type}

def replicate (m : RatProg α) : (n : ℕ) → RatProg (Samples α n)
  | 0 => .ret ()
  | n+1 => m.bind fun a => (m.replicate n).bind fun xs => .ret (a,xs)

theorem Refines.replicate_id {O : Oracle Q} {m : RatProg α} {M : Prog Q α}
    (h : Refines O m M id) (n : ℕ) : Refines O (m.replicate n) (M.replicate n) id := by
  induction n with
  | zero => exact Refines.ret O () id
  | succ n ih =>
    unfold RatProg.replicate Prog.replicate
    apply h.bind
    intro a
    apply ih.bind
    intro xs
    exact Refines.ret O (a,xs) id

end RatProg

variable {E I Ω : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

def rationalAcceptanceCount : (n : ℕ) → Samples (Option Ω) n → ℕ
  | 0, _ => 0
  | n+1, xs => (if xs.1.isSome then 1 else 0)+rationalAcceptanceCount n xs.2

theorem rationalAcceptanceCount_cast [Fintype Ω] (n : ℕ) (xs : Samples (Option Ω) n) :
    (rationalAcceptanceCount n xs : ℝ) = Law.sampleSum (acceptedTest (fun _ => 1)) n xs := by
  induction n with
  | zero => simp [rationalAcceptanceCount,Law.sampleSum]
  | succ n ih =>
    simp only [rationalAcceptanceCount,Nat.cast_add,Law.sampleSum,← ih]
    cases xs.1 <;> simp [acceptedTest]

def rationalRejectionCount (proposal : RatProg (Option Ω)) (W : ℚ) (n : ℕ) : RatProg ℚ :=
  (proposal.replicate n).bind fun xs => .ret (2*W*(rationalAcceptanceCount n xs/n))

def rationalCappedSample (proposal : RatProg (Option Ω)) (fallback : Ω) : ℕ → RatProg Ω
  | 0 => .ret fallback
  | n+1 => proposal.bind fun x => x.elim (rationalCappedSample proposal fallback n) RatProg.ret

namespace RatProg
variable {Q : Type} {O : Oracle Q}

theorem rationalRejectionCount_refines [Fintype Ω]
    {proposal : RatProg (Option Ω)} {P : Prog Q (Option Ω)} (h : Refines O proposal P id)
    (W : ℚ) (n : ℕ) :
    Refines O (rationalRejectionCount proposal W n) (rejectionCount P (W : ℝ) n) Rat.cast := by
  unfold rationalRejectionCount rejectionCount
  apply (h.replicate_id n).bind
  intro xs
  have he : ((2*W*(rationalAcceptanceCount n xs/n) : ℚ) : ℝ) =
      2*(W : ℝ)*Law.sampleAverage (acceptedTest (fun _ => 1)) n xs := by
    simp [Law.sampleAverage,rationalAcceptanceCount_cast]
  intro f
  change f ((2*W*(rationalAcceptanceCount n xs/n) : ℚ) : ℝ) = _
  rw [he]
  rfl

theorem rationalCappedSample_refines [Fintype Ω]
    {proposal : RatProg (Option Ω)} {P : Prog Q (Option Ω)} (h : Refines O proposal P id)
    (fallback : Ω) (n : ℕ) :
    Refines O (rationalCappedSample proposal fallback n) (cappedSample P fallback n) id := by
  induction n with
  | zero => exact Refines.ret O fallback id
  | succ n ih =>
    unfold rationalCappedSample cappedSample
    apply h.bind
    intro x
    cases x with
    | none => exact ih
    | some x => exact Refines.ret O x id

end RatProg

def rationalInitialWeights (feas : I → (E → ℚ) → Bool)
    (oracle : I → (E → ℚ) → RatProg ℚ) (p : E → ℚ) : List I → RatProg (I → ℚ)
  | [] => .ret (fun _ => 0)
  | i::l => (rationalGuard (feas i) (oracle i) p).bind fun r =>
    (rationalInitialWeights feas oracle p l).bind fun w => .ret (Function.update w i r)

theorem rationalUpdate_cast {α : Type} [DecidableEq α] (w : α → ℚ) (i : α) (r : ℚ) :
    (fun j => ((Function.update w i r) j : ℝ)) = Function.update (fun j => (w j : ℝ)) i (r : ℝ) := by
  funext j
  by_cases h : j=i <;> simp [h]

namespace RatProg
variable {Q : Type} (O : Oracle Q) (mk : I → (E → ℝ) → Q)
    (feas : I → (E → ℚ) → Bool) (F : I → (E → ℝ) → Prop)
    (oracle : I → (E → ℚ) → RatProg ℚ)

theorem rationalInitialWeights_refines
    (hf : ∀ i p, feas i p = true ↔ F i (fun e => (p e : ℝ)))
    (ho : ∀ i p, Refines O (oracle i p) (.query (mk i (fun e => (p e : ℝ))) Prog.ret) Rat.cast)
    (p : E → ℚ) (l : List I) :
    Refines O (rationalInitialWeights feas oracle p l)
      (initialWeights mk F (fun e => (p e : ℝ)) l) (fun w i => (w i : ℝ)) := by
  induction l with
  | nil =>
    simpa only [rationalInitialWeights,initialWeights,Rat.cast_zero] using
      Refines.ret O (fun _ : I => (0 : ℚ)) (fun w i => (w i : ℝ))
  | cons i l ih =>
    unfold rationalInitialWeights initialWeights
    have hg := rationalGuard_refines O (mk i) (feas i) (F i) (oracle i) (hf i) (ho i) p
    have he (c : Prop) (q : Q) (k : ℝ → Prog Q (I → ℝ)) :
        Prog.guarded c q k = (Prog.guarded c q Prog.ret).bind k := by
      classical
      by_cases h : c <;> simp [Prog.guarded,h,Prog.bind]
    rw [he]
    apply hg.bind
    intro r
    apply ih.bind
    intro w
    simpa only [rationalUpdate_cast] using
      Refines.ret O (Function.update w i r) (fun w j => (w j : ℝ))

end RatProg

namespace Digraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V E)
    (U : Finset V) {k : ℕ} (order : Fin k ≃ U)

def rationalVertexProposal (p : E → ℚ) (w : U → ℚ)
    (oracle : U → (E → ℚ) → RatProg ℚ) (edges : List E) (d : U) : RatProg (Option (E → Bool)) :=
  RatProg.weightedEquiv order w d fun i =>
    (rationalRecordedExpose (G.rationalFeasible i.val) (oracle i) edges p).bind fun r =>
      let a := G.rationalReject U p w i r.1 r.2
      RatProg.weightedEquiv finTwoEquiv (fun b => if b then a else 1-a) false
        (fun b => .ret (if b then some r.1 else none))

theorem rationalVertexProposal_refines (O : Oracle (VertexQuery (E := E) U))
    (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ))) (w : U → ℚ)
    (oracle : U → (E → ℚ) → RatProg ℚ)
    (ho : ∀ i q, RatProg.Refines O (oracle i q) (.query (i,fun e => (q e : ℝ)) Prog.ret) Rat.cast)
    (edges : List E) (d : U) :
    RatProg.Refines O (G.rationalVertexProposal U order p w oracle edges d)
      (correctedProposal (edgeLaw (fun e => (p e : ℝ)) (fun e => (hp e).1)
        (fun e => (hp e).2)).toMass (G.vertexEvents U) (fun i => (w i : ℝ))
        (fun i => recordedExpose (fun q => (i,q)) (G.vertexFeasible U i) edges (fun e => (p e : ℝ))) d) id := by
  unfold rationalVertexProposal correctedProposal
  apply RatProg.Refines.weightedEquiv
  intro i
  apply (RatProg.rationalRecordedExpose_refines O (fun q => (i,q)) (G.rationalFeasible i.val)
    (G.vertexFeasible U i) (oracle i) (G.rationalFeasible_correct U i) (ho i) edges p).bind
  intro r
  dsimp only
  have ha := G.rationalReject_cast U p hp w i r.1 r.2
  unfold rejectionDraw
  have hw : (fun b : Bool => ((if b then G.rationalReject U p w i r.1 r.2 else
      1-G.rationalReject U p w i r.1 r.2 : ℚ) : ℝ)) =
      (fun b : Bool => if b then (G.rationalReject U p w i r.1 r.2 : ℝ) else
        1-(G.rationalReject U p w i r.1 r.2 : ℝ)) := by funext b; cases b <;> simp
  rw [← ha,← hw]
  apply RatProg.Refines.weightedEquiv
  intro b
  exact RatProg.Refines.ret O _ id

/-- The rational constant-confidence counting run with supplied finite orders. -/
def rationalVertexCount (p : E → ℚ) (oracle : U → (E → ℚ) → RatProg ℚ)
    (vertices : List U) (edges : List E) (d : U) (n : ℕ) : RatProg ℚ :=
  (rationalInitialWeights (fun i => G.rationalFeasible i.val) oracle p vertices).bind fun w =>
    rationalRejectionCount (G.rationalVertexProposal U order p w oracle edges d) (∑ i, w i) n

/-- The rational conditional sampler, with a supplied deterministic fallback. -/
def rationalVertexSample (p : E → ℚ) (oracle : U → (E → ℚ) → RatProg ℚ)
    (vertices : List U) (edges : List E) (d : U) (fallback : E → Bool) (n : ℕ) :
    RatProg (E → Bool) :=
  (rationalInitialWeights (fun i => G.rationalFeasible i.val) oracle p vertices).bind fun w =>
    rationalCappedSample (G.rationalVertexProposal U order p w oracle edges d) fallback n

theorem rationalVertexCount_refines (O : Oracle (VertexQuery (E := E) U))
    (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ)))
    (oracle : U → (E → ℚ) → RatProg ℚ)
    (ho : ∀ i q, RatProg.Refines O (oracle i q) (.query (i,fun e => (q e : ℝ)) Prog.ret) Rat.cast)
    (vertices : List U) (edges : List E) (d : U) (n : ℕ) :
    RatProg.Refines O (G.rationalVertexCount U order p oracle vertices edges d n)
      (witnessCount (G.vertexEvents U) (fun i q => (i,q)) (G.vertexFeasible U)
        (fun e => (p e : ℝ)) hp vertices edges d n) Rat.cast := by
  unfold rationalVertexCount witnessCount
  apply (RatProg.rationalInitialWeights_refines O (fun i q => (i,q))
    (fun i => G.rationalFeasible i.val) (G.vertexFeasible U) oracle
    (G.rationalFeasible_correct U) ho p vertices).bind
  intro w
  have h := RatProg.rationalRejectionCount_refines
    (G.rationalVertexProposal_refines U order O p hp w oracle ho edges d) (∑ i, w i) n
  simpa only [Rat.cast_sum] using h

theorem rationalVertexSample_refines (O : Oracle (VertexQuery (E := E) U))
    (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ)))
    (oracle : U → (E → ℚ) → RatProg ℚ)
    (ho : ∀ i q, RatProg.Refines O (oracle i q) (.query (i,fun e => (q e : ℝ)) Prog.ret) Rat.cast)
    (vertices : List U) (edges : List E) (d : U) (fallback : E → Bool) (n : ℕ) :
    RatProg.Refines O (G.rationalVertexSample U order p oracle vertices edges d fallback n)
      (witnessSample (G.vertexEvents U) (fun i q => (i,q)) (G.vertexFeasible U)
        (fun e => (p e : ℝ)) hp vertices edges d fallback n) id := by
  unfold rationalVertexSample witnessSample
  apply (RatProg.rationalInitialWeights_refines O (fun i q => (i,q))
    (fun i => G.rationalFeasible i.val) (G.vertexFeasible U) oracle
    (G.rationalFeasible_correct U) ho p vertices).bind
  intro w
  exact RatProg.rationalCappedSample_refines
    (G.rationalVertexProposal_refines U order O p hp w oracle ho edges d) fallback n

end Digraph
end DirectedCycleFPRAS
