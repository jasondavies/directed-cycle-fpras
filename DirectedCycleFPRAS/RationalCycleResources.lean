module

public import DirectedCycleFPRAS.RationalCounting
public import DirectedCycleFPRAS.RationalProgramBounds

@[expose] public section

/-! Composed choice and fair-bit bounds for the executable rational counting
and sampling programs, with all reliability callbacks included. -/
namespace DirectedCycleFPRAS
set_option linter.unusedSectionVars false

namespace RatProg
variable {α : Type}

theorem ChoiceBound.replicate {m : RatProg α} {C : ℕ}
    (h : ChoiceBound m C) (n : ℕ) : ChoiceBound (m.replicate n) (n*C) := by
  induction n with
  | zero => exact .ret _ _
  | succ n ih =>
    have ht := h.bind (fun a => ih.bind (fun xs => ChoiceBound.ret (a,xs) 0))
    simpa [Samples,RatProg.replicate,Nat.succ_mul,Nat.add_comm] using ht

theorem ChoiceBound.medianOf {m : RatProg ℚ} {C : ℕ}
    (h : ChoiceBound m C) (n : ℕ) : ChoiceBound (m.medianOf n) (n*C) := by
  simpa [RatProg.medianOf] using (h.replicate n).bind
    (fun xs => ChoiceBound.ret (rationalMedian (samplesToFn n xs)) 0)

end RatProg

variable {E I Ω : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem rationalGuard_choiceBound (feas : (E → ℚ) → Bool)
    (oracle : (E → ℚ) → RatProg ℚ) {C : ℕ}
    (ho : ∀ q, RatProg.ChoiceBound (oracle q) C) (q : E → ℚ) :
    RatProg.ChoiceBound (rationalGuard feas oracle q) C := by
  unfold rationalGuard
  split_ifs
  · exact ho q
  · exact .ret _ _

theorem rationalRecordedExpose_choiceBound (feas : (E → ℚ) → Bool)
    (oracle : (E → ℚ) → RatProg ℚ) {C : ℕ}
    (ho : ∀ q, RatProg.ChoiceBound (oracle q) C) (l : List E) (p : E → ℚ) :
    RatProg.ChoiceBound (rationalRecordedExpose feas oracle l p) (l.length*(2*C+2)) := by
  induction l generalizing p with
  | nil => exact .ret _ _
  | cons e l ih =>
    have h := (rationalGuard_choiceBound feas oracle ho (rationalPin p e true)).bind fun r₁ =>
      (rationalGuard_choiceBound feas oracle ho (rationalPin p e false)).bind fun r₀ =>
        RatProg.ChoiceBound.weightedEquiv finTwoEquiv
          (fun b : Bool => if b then p e*r₁ else (1-p e)*r₀) true
          (fun b => (rationalRecordedExpose feas oracle l (rationalPin p e b)).bind
            fun r => .ret (r.1,rationalNormValue
              (fun b : Bool => if b then p e*r₁ else (1-p e)*r₀) true b*r.2))
          (fun b => (ih (rationalPin p e b)).bind (fun r => RatProg.ChoiceBound.ret _ 0))
    exact h.mono (by simp only [List.length_cons,Nat.succ_mul]; omega)

theorem rationalInitialWeights_choiceBound (feas : I → (E → ℚ) → Bool)
    (oracle : I → (E → ℚ) → RatProg ℚ) {C : ℕ}
    (ho : ∀ i q, RatProg.ChoiceBound (oracle i q) C) (p : E → ℚ) (l : List I) :
    RatProg.ChoiceBound (rationalInitialWeights feas oracle p l) (l.length*C) := by
  induction l with
  | nil => exact .ret _ _
  | cons i l ih =>
    have h := (rationalGuard_choiceBound (feas i) (oracle i) (ho i) p).bind fun r =>
      ih.bind fun w => RatProg.ChoiceBound.ret (Function.update w i r) 0
    simpa [rationalInitialWeights,Nat.succ_mul,Nat.add_comm] using h

theorem rationalRejectionCount_choiceBound (proposal : RatProg (Option Ω)) {C : ℕ}
    (hp : RatProg.ChoiceBound proposal C) (W : ℚ) (n : ℕ) :
    RatProg.ChoiceBound (rationalRejectionCount proposal W n) (n*C) := by
  simpa [rationalRejectionCount] using (hp.replicate n).bind
    (fun xs => RatProg.ChoiceBound.ret (2*W*(rationalAcceptanceCount n xs/n)) 0)

theorem rationalCappedSample_choiceBound (proposal : RatProg (Option Ω)) {C : ℕ}
    (hp : RatProg.ChoiceBound proposal C) (fallback : Ω) (n : ℕ) :
    RatProg.ChoiceBound (rationalCappedSample proposal fallback n) (n*C) := by
  induction n with
  | zero => exact .ret _ _
  | succ n ih =>
    have h := hp.bind (fun o => show RatProg.ChoiceBound
        (o.elim (rationalCappedSample proposal fallback n) RatProg.ret) (n*C) from by
      cases o with
      | none => exact ih
      | some x => exact .ret _ _)
    simpa [rationalCappedSample,Nat.succ_mul,Nat.add_comm] using h

/-- All reliability calls plus witness, exposure, and acceptance choices. -/
def rationalCycleChoices (k m C D : ℕ) : ℕ := k*C+D*(k+2+m*(2*C+2))

/-- The bound separates amplified oracle invocations from the reduction's
own finite-choice alternatives, agreeing with the paper's accounting. -/
theorem rationalCycleChoices_eq (k m C D : ℕ) :
    rationalCycleChoices k m C D = (k+2*m*D)*C+D*(k+2*m+2) := by
  unfold rationalCycleChoices
  ring

namespace Digraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V E)
    (U : Finset V) {k : ℕ} (order : Fin k ≃ U)

theorem rationalVertexProposal_choiceBound (p : E → ℚ) (w : U → ℚ)
    (oracle : U → (E → ℚ) → RatProg ℚ) {C : ℕ}
    (ho : ∀ i q, RatProg.ChoiceBound (oracle i q) C) (edges : List E) (d : U) :
    RatProg.ChoiceBound (G.rationalVertexProposal U order p w oracle edges d)
      (k+2+edges.length*(2*C+2)) := by
  unfold rationalVertexProposal
  have h := RatProg.ChoiceBound.weightedEquiv order w d _ (fun i =>
    (rationalRecordedExpose_choiceBound (G.rationalFeasible i.val) (oracle i) (ho i) edges p).bind
      (fun r => RatProg.ChoiceBound.weightedEquiv finTwoEquiv
        (fun b : Bool => if b then G.rationalReject U p w i r.1 r.2 else
          1-G.rationalReject U p w i r.1 r.2) false
        (fun b => .ret (if b then some r.1 else none)) (fun b => RatProg.ChoiceBound.ret _ 0)))
  exact h.mono (by omega)

theorem rationalVertexCount_choiceBound (p : E → ℚ)
    (oracle : U → (E → ℚ) → RatProg ℚ) {C : ℕ}
    (ho : ∀ i q, RatProg.ChoiceBound (oracle i q) C)
    (vertices : List U) (edges : List E) (d : U) (n : ℕ) :
    RatProg.ChoiceBound (G.rationalVertexCount U order p oracle vertices edges d n)
      (vertices.length*C+n*(k+2+edges.length*(2*C+2))) := by
  unfold rationalVertexCount
  exact (rationalInitialWeights_choiceBound (fun i => G.rationalFeasible i.val) oracle ho p vertices).bind
    fun w => rationalRejectionCount_choiceBound _
      (G.rationalVertexProposal_choiceBound U order p w oracle ho edges d) _ n

theorem rationalVertexSample_choiceBound (p : E → ℚ)
    (oracle : U → (E → ℚ) → RatProg ℚ) {C : ℕ}
    (ho : ∀ i q, RatProg.ChoiceBound (oracle i q) C)
    (vertices : List U) (edges : List E) (d : U) (fallback : E → Bool) (n : ℕ) :
    RatProg.ChoiceBound (G.rationalVertexSample U order p oracle vertices edges d fallback n)
      (vertices.length*C+n*(k+2+edges.length*(2*C+2))) := by
  unfold rationalVertexSample
  exact (rationalInitialWeights_choiceBound (fun i => G.rationalFeasible i.val) oracle ho p vertices).bind
    fun w => rationalCappedSample_choiceBound _
      (G.rationalVertexProposal_choiceBound U order p w oracle ho edges d) fallback n

/-- Fixed fair-bit budget after compiling the entire counting program once,
including all oracle callbacks and outer median repetitions. -/
theorem rationalVertexCount_bits (p : E → ℚ)
    (oracle : U → (E → ℚ) → RatProg ℚ) {C : ℕ}
    (ho : ∀ i q, RatProg.ChoiceBound (oracle i q) C)
    (vertices : List U) (edges : List E) (d : U) (n outer b : ℕ) :
    BitProg.Bits (((G.rationalVertexCount U order p oracle vertices edges d n).medianOf outer).compile b)
      (b*(outer*(vertices.length*C+n*(k+2+edges.length*(2*C+2))))) :=
  ((G.rationalVertexCount_choiceBound U order p oracle ho vertices edges d n).medianOf outer).compile b

/-- Fixed fair-bit budget for the complete capped conditional sampler. -/
theorem rationalVertexSample_bits (p : E → ℚ)
    (oracle : U → (E → ℚ) → RatProg ℚ) {C : ℕ}
    (ho : ∀ i q, RatProg.ChoiceBound (oracle i q) C)
    (vertices : List U) (edges : List E) (d : U) (fallback : E → Bool) (n b : ℕ) :
    BitProg.Bits ((G.rationalVertexSample U order p oracle vertices edges d fallback n).compile b)
      (b*(vertices.length*C+n*(k+2+edges.length*(2*C+2)))) :=
  (G.rationalVertexSample_choiceBound U order p oracle ho vertices edges d fallback n).compile b

/-- Uniform error bound when compiling the complete amplified counting run. -/
theorem rationalVertexCount_compile_error (p : E → ℚ)
    (oracle : U → (E → ℚ) → RatProg ℚ) {C : ℕ}
    (ho : ∀ i q, RatProg.ChoiceBound (oracle i q) C)
    (vertices : List U) (edges : List E) (d : U) (n outer b : ℕ)
    (f : ℚ → ℝ) (hf0 : ∀ x, 0≤f x) (hf1 : ∀ x, f x≤1) :
    |((((G.rationalVertexCount U order p oracle vertices edges d n).medianOf outer).compile b).toProg.exp
        noOracle f)-
      ((G.rationalVertexCount U order p oracle vertices edges d n).medianOf outer).nominal.exp noOracle f| ≤
        (outer*(vertices.length*C+n*(k+2+edges.length*(2*C+2))) : ℕ)/(2 : ℝ)^b :=
  RatProg.compile_error b
    ((G.rationalVertexCount_choiceBound U order p oracle ho vertices edges d n).medianOf outer) f hf0 hf1

/-- Uniform error bound when compiling the complete capped sampler. -/
theorem rationalVertexSample_compile_error (p : E → ℚ)
    (oracle : U → (E → ℚ) → RatProg ℚ) {C : ℕ}
    (ho : ∀ i q, RatProg.ChoiceBound (oracle i q) C)
    (vertices : List U) (edges : List E) (d : U) (fallback : E → Bool) (n b : ℕ)
    (f : (E → Bool) → ℝ) (hf0 : ∀ x, 0≤f x) (hf1 : ∀ x, f x≤1) :
    |((G.rationalVertexSample U order p oracle vertices edges d fallback n).compile b).toProg.exp noOracle f-
      (G.rationalVertexSample U order p oracle vertices edges d fallback n).nominal.exp noOracle f| ≤
        (vertices.length*C+n*(k+2+edges.length*(2*C+2)) : ℕ) / (2 : ℝ)^b :=
  RatProg.compile_error b
    (G.rationalVertexSample_choiceBound U order p oracle ho vertices edges d fallback n) f hf0 hf1

end Digraph
end DirectedCycleFPRAS
