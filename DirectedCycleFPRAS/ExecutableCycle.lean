module

public import DirectedCycleFPRAS.RationalEndToEnd
public import DirectedCycleFPRAS.BitTapeLaw

@[expose] public section

/-! Executable frontends. Finite enumerations and natural budgets are explicit
inputs; zero detection runs before choosing a witness or invoking the oracle. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E) (U : Finset V)

def executableCount {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (witnesses : Fin k ≃ U) (p : E → ℚ) (D inner outer b : ℕ) : BitProg ℚ :=
  if G.hasCycle (fun e => decide (0 < p e)) then
    if h : 0 < k then
      ((G.rationalVertexCount U witnesses p
        (G.rationalCycleCallback U vertices edges (List.ofFn edges) inner)
        (List.ofFn witnesses) (List.ofFn edges) (witnesses ⟨0,h⟩) D).medianOf outer).compile b
    else .ret 0
  else .ret 0

/-- Sampling is defined for a nonempty cover; its accuracy theorem requires
positive cyclicity probability. On timeout it returns the positive support. -/
def executableSample {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (witnesses : Fin k ≃ U) (hk : 0 < k) (p : E → ℚ) (D inner b : ℕ) : BitProg (E → Bool) :=
  (G.rationalVertexSample U witnesses p
    (G.rationalCycleCallback U vertices edges (List.ofFn edges) inner)
    (List.ofFn witnesses) (List.ofFn edges) (witnesses ⟨0,hk⟩)
    (fun e => decide (0 < p e)) D).compile b

/-- Choice alternatives for one complete run with all callbacks included. -/
def executableChoices (n m k D inner : ℕ) : ℕ :=
  rationalCycleChoices k m (rationalCycleCallbackChoices n m inner) D

open Classical
noncomputable section
set_option linter.unusedSectionVars false

theorem executableCount_zero {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (witnesses : Fin k ≃ U) (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ)))
    (D inner outer b : ℕ)
    (hz : eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω)) = 0) :
    G.executableCount U vertices edges witnesses p D inner outer b = .ret 0 := by
  have hn : ¬G.Cyclic {e | 0 < (p e : ℝ)} := by
    intro hc
    have hh := (G.cycleMass_pos_iff _ (fun e => (hp e).1) (fun e => (hp e).2)).mpr hc
    change 0 < eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω)) at hh
    rw [hz] at hh
    exact (lt_irrefl 0) hh
  have hc : G.hasCycle (fun e => decide (0 < p e)) ≠ true := by
    intro hh
    apply hn
    have ht := (G.hasCycle_eq_true _).mp hh
    simpa using ht
  simp only [executableCount, ite_eq_right hc]

theorem executableCount_zero_run {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (witnesses : Fin k ≃ U) (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ)))
    (D inner outer b : ℕ)
    (hz : eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω)) = 0)
    (tape : ℕ → Bool) (offset : ℕ) :
    (G.executableCount U vertices edges witnesses p D inner outer b).run tape offset = (0,offset) := by
  rw [G.executableCount_zero U vertices edges witnesses p hp D inner outer b hz]
  rfl

private theorem enum_mem {ι : Type} {k : ℕ} (e : Fin k ≃ ι) (x : ι) : x∈List.ofFn e :=
  List.mem_ofFn.mpr ⟨e.symm x,e.apply_symm_apply x⟩

private theorem witness_card {k : ℕ} (witnesses : Fin k ≃ U) : U.card=k := by
  simpa using (Fintype.card_congr witnesses).symm

theorem executableCount_bits {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (witnesses : Fin k ≃ U) (p : E → ℚ) (D inner outer b : ℕ) :
    BitProg.Bits (G.executableCount U vertices edges witnesses p D inner outer b)
      (b*(outer*executableChoices n m k D inner)) := by
  unfold executableCount
  split_ifs
  · simpa [executableChoices,rationalCycleChoices] using
      G.rationalVertexCount_bits U witnesses p
        (G.rationalCycleCallback U vertices edges (List.ofFn edges) inner)
        (G.rationalCycleCallback_choiceBound U vertices edges (List.ofFn edges) List.length_ofFn inner)
        (List.ofFn witnesses) (List.ofFn edges) _ D outer b
  · exact .ret _ _
  · exact .ret _ _

theorem executableSample_bits {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (witnesses : Fin k ≃ U) (hk : 0<k) (p : E → ℚ) (D inner b : ℕ) :
    BitProg.Bits (G.executableSample U vertices edges witnesses hk p D inner b)
      (b*executableChoices n m k D inner) := by
  simpa [executableSample,executableChoices,rationalCycleChoices] using
    G.rationalVertexSample_bits U witnesses p
      (G.rationalCycleCallback U vertices edges (List.ofFn edges) inner)
      (G.rationalCycleCallback_choiceBound U vertices edges (List.ofFn edges) List.length_ofFn inner)
      (List.ofFn witnesses) (List.ofFn edges) (witnesses ⟨0,hk⟩)
      (fun e => decide (0<p e)) D b

/-- Accuracy for every input, including empty covers and exact zero detection. -/
theorem executableCount_failure {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (witnesses : Fin k ≃ U) (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ)))
    (hU : G.Feedback U {e | 0<(p e : ℝ)}) (D inner outer b : ℕ)
    {eps : ℝ} (heps : 0<eps) (hD : 64*(k : ℝ)/eps^2 ≤ D)
    (hinner : (k+2*m*D : ℕ)*(7/8 : ℝ)^inner ≤ 1/16) :
    let Z := eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω))
    (G.executableCount U vertices edges witnesses p D inner outer b).toProg.exp noOracle
      (fun z => if eps*Z< |(z : ℝ)-Z| then 1 else 0) ≤
        (7/8 : ℝ)^outer+(outer*executableChoices n m k D inner : ℕ)/(2 : ℝ)^b := by
  dsimp only
  by_cases hZ : 0<eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω))
  · have hc := (G.cycleMass_pos_iff _ (fun e => (hp e).1) (fun e => (hp e).2)).mp hZ
    obtain ⟨v,hv,_⟩ := (G.feedback_cover U _ hU).mp hc
    have hk : 0<k := lt_of_le_of_lt (Nat.zero_le _) (witnesses.symm ⟨v,hv⟩).isLt
    have hb : G.hasCycle (fun e => decide (0<p e))=true := by
      rw [G.hasCycle_eq_true]
      simpa using hc
    have hm := G.vertex_unionMass U hp hU
    change (edgeLaw (fun e => (p e : ℝ)) (fun e => (hp e).1) (fun e => (hp e).2)).toMass.unionMass
      (G.vertexEvents U)=eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω)) at hm
    have hz := hm.symm ▸ hZ
    have ha := G.rationalVertexCount_compiled_failure U vertices edges (List.ofFn edges)
      (List.nodup_ofFn.mpr edges.injective) (enum_mem edges) witnesses (List.ofFn witnesses)
      (enum_mem witnesses) p hp (witnesses ⟨0,hk⟩) D inner outer b hz heps
      (by simpa only [witness_card U witnesses] using hD)
      (by simpa using hinner)
    dsimp only at ha
    rw [hm] at ha
    simp only [executableCount,ite_eq_left hb,dite_eq_left hk]
    apply (Prog.exp_mono noOracle _ (fun z : ℚ => show
      (if eps*eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω))<
        |(z : ℝ)-eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω))| then (1 : ℝ) else 0) ≤
      (if eps*eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω))≤
        |(z : ℝ)-eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω))| then (1 : ℝ) else 0) from by
          split_ifs with hlt hle <;> norm_num
          exact hle hlt.le)).trans
    simpa [executableChoices,rationalCycleChoices] using ha
  · have hz := le_antisymm (not_lt.mp hZ) (eventMass_nonneg hp _)
    rw [G.executableCount_zero U vertices edges witnesses p hp D inner outer b hz]
    simp only [BitProg.toProg,Prog.exp,hz,Rat.cast_zero,mul_zero,sub_zero,abs_zero,lt_self_iff_false,ite_false]
    positivity

/-- The accuracy guarantee is a statement about execution on a uniformly
random fixed-length fair-bit tape. -/
theorem executableCount_tape_failure {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (witnesses : Fin k ≃ U) (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ)))
    (hU : G.Feedback U {e | 0<(p e : ℝ)}) (D inner outer b : ℕ)
    {eps : ℝ} (heps : 0<eps) (hD : 64*(k : ℝ)/eps^2 ≤ D)
    (hinner : (k+2*m*D : ℕ)*(7/8 : ℝ)^inner ≤ 1/16) :
    let Z := eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω))
    let N := b*(outer*executableChoices n m k D inner)
    (∑ tape : Fin N → Bool, (1/(2 : ℝ)^N)*
      (if eps*Z< |(((G.executableCount U vertices edges witnesses p D inner outer b).run
        (BitProg.zeroExtend tape) 0).1 : ℝ)-Z| then 1 else 0)) ≤
        (7/8 : ℝ)^outer+(outer*executableChoices n m k D inner : ℕ)/(2 : ℝ)^b := by
  dsimp only
  rw [BitProg.run_uniform (G.executableCount_bits U vertices edges witnesses p D inner outer b)
    (fun z : ℚ => if eps*eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω)) <
      |(z : ℝ)-eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω))| then 1 else 0)]
  exact G.executableCount_failure U vertices edges witnesses p hp hU D inner outer b heps hD hinner

/-- Conditional-sampling accuracy for the actual compiled program. -/
theorem executableSample_error {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (witnesses : Fin k ≃ U) (hk : 0<k) (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ)))
    (hU : G.Feedback U {e | 0<(p e : ℝ)})
    (hZ : 0<eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω)))
    (r inner b : ℕ) (f : (E → Bool) → ℝ) (hf0 : ∀ x, 0≤f x) (hf1 : ∀ x, f x≤1) :
    |(G.executableSample U vertices edges witnesses hk p (4*k*r) inner b).toProg.exp noOracle f-
      (∑ ω, if G.Cyclic (retained ω) then edgeWeight (fun e => (p e : ℝ)) ω*f ω else 0)/
        eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω))| ≤
      (1/2 : ℝ)^r+(k+2*m*(4*k*r) : ℕ)*(7/8 : ℝ)^inner+
        (executableChoices n m k (4*k*r) inner : ℝ)/(2 : ℝ)^b := by
  have hm := G.vertex_unionMass U hp hU
  change (edgeLaw (fun e => (p e : ℝ)) (fun e => (hp e).1) (fun e => (hp e).2)).toMass.unionMass
    (G.vertexEvents U)=eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω)) at hm
  have hz := hm.symm ▸ hZ
  have h := G.rationalVertexSample_compiled_error U vertices edges (List.ofFn edges)
    (List.nodup_ofFn.mpr edges.injective) (enum_mem edges) witnesses (List.ofFn witnesses)
    (enum_mem witnesses) p hp (witnesses ⟨0,hk⟩) (fun e => decide (0<p e)) r inner b hz f hf0 hf1
  dsimp only at h
  rw [G.vertex_conditional_expectation U (fun e => (p e : ℝ)) hp hU hz f] at h
  simpa [executableSample,executableChoices,rationalCycleChoices,witness_card U witnesses] using h

/-- Sampling variation error on a uniformly random fixed-length fair-bit tape. -/
theorem executableSample_tape_error {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (witnesses : Fin k ≃ U) (hk : 0<k) (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ)))
    (hU : G.Feedback U {e | 0<(p e : ℝ)})
    (hZ : 0<eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω)))
    (r inner b : ℕ) (f : (E → Bool) → ℝ) (hf0 : ∀ x, 0≤f x) (hf1 : ∀ x, f x≤1) :
    let N := b*executableChoices n m k (4*k*r) inner
    |(∑ tape : Fin N → Bool, (1/(2 : ℝ)^N)*f
        ((G.executableSample U vertices edges witnesses hk p (4*k*r) inner b).run
          (BitProg.zeroExtend tape) 0).1)-
      (∑ ω, if G.Cyclic (retained ω) then edgeWeight (fun e => (p e : ℝ)) ω*f ω else 0)/
        eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω))| ≤
      (1/2 : ℝ)^r+(k+2*m*(4*k*r) : ℕ)*(7/8 : ℝ)^inner+
        (executableChoices n m k (4*k*r) inner : ℝ)/(2 : ℝ)^b := by
  dsimp only
  rw [BitProg.run_uniform (G.executableSample_bits U vertices edges witnesses hk p (4*k*r) inner b) f]
  exact G.executableSample_error U vertices edges witnesses hk p hp hU hZ r inner b f hf0 hf1

end
end Digraph
end DirectedCycleFPRAS
