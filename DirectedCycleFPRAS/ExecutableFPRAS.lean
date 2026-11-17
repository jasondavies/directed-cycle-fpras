module

public import DirectedCycleFPRAS.ExecutableCycle
public import DirectedCycleFPRAS.ExecutableParameters

@[expose] public section

/-! Executable counting and conditional sampling with natural input budgets.
The conclusions concern the actual interpreter on a fixed-length fair-bit tape.
Counting uses relative error `1/r`, and both programs use error target `2⁻ᵈ`. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E) (U : Finset V)

def executableFPRAS {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (witnesses : Fin k ≃ U) (p : E → ℚ) (r d : ℕ) : BitProg ℚ :=
  G.executableCount U vertices edges witnesses p (execCountSamples k r)
    (execCountInner m k r) (execCountOuter d) (execCountWidth n m k r d)

def executableFPRASBits (n m k r d : ℕ) : ℕ :=
  execCountWidth n m k r d*execCountChoices n m k r d

def executableConditionalSampler {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (witnesses : Fin k ≃ U) (hk : 0<k) (p : E → ℚ) (d : ℕ) : BitProg (E → Bool) :=
  G.executableSample U vertices edges witnesses hk p (execSampleProposals k d)
    (execSampleInner m k d) (execSampleWidth n m k d)

def executableSamplerBits (n m k d : ℕ) : ℕ :=
  execSampleWidth n m k d*execSampleChoices n m k d

theorem executableCount_choices_eq (n m k r d : ℕ) :
    execCountOuter d*executableChoices n m k (execCountSamples k r) (execCountInner m k r) =
      execCountChoices n m k r d := by
  unfold executableChoices execCountChoices execCountQueries execOracleChoices rationalCycleCallbackChoices
  rw [rationalCycleChoices_eq]

theorem executableSample_choices_eq (n m k d : ℕ) :
    executableChoices n m k (execSampleProposals k d) (execSampleInner m k d) =
      execSampleChoices n m k d := by
  unfold executableChoices execSampleChoices execSampleQueries execOracleChoices rationalCycleCallbackChoices
  rw [rationalCycleChoices_eq]

theorem executableFPRAS_bits {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (witnesses : Fin k ≃ U) (p : E → ℚ) (r d : ℕ) :
    BitProg.Bits (G.executableFPRAS U vertices edges witnesses p r d) (executableFPRASBits n m k r d) := by
  simpa only [executableFPRAS,executableFPRASBits,executableCount_choices_eq] using
    G.executableCount_bits U vertices edges witnesses p (execCountSamples k r)
      (execCountInner m k r) (execCountOuter d) (execCountWidth n m k r d)

theorem executableConditionalSampler_bits {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (witnesses : Fin k ≃ U) (hk : 0<k) (p : E → ℚ) (d : ℕ) :
    BitProg.Bits (G.executableConditionalSampler U vertices edges witnesses hk p d)
      (executableSamplerBits n m k d) := by
  simpa only [executableConditionalSampler,executableSamplerBits,executableSample_choices_eq] using
    G.executableSample_bits U vertices edges witnesses hk p (execSampleProposals k d)
      (execSampleInner m k d) (execSampleWidth n m k d)

open Classical
noncomputable section
set_option linter.unusedSectionVars false

/-- End-to-end counting correctness on a uniform finite fair-bit tape, with
relative error `1/r` and failure at most `2⁻ᵈ`. -/
theorem executableFPRAS_correct {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (witnesses : Fin k ≃ U) (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ)))
    (hU : G.Feedback U {e | 0<(p e : ℝ)}) (r d : ℕ) (hr : 0<r) :
    let Z := eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω))
    let N := executableFPRASBits n m k r d
    (∑ tape : Fin N → Bool, (1/(2 : ℝ)^N)*
      (if (1/(r : ℝ))*Z < |(((G.executableFPRAS U vertices edges witnesses p r d).run
        (BitProg.zeroExtend tape) 0).1 : ℝ)-Z| then 1 else 0)) ≤ (1/2 : ℝ)^d := by
  have h := G.executableCount_tape_failure U vertices edges witnesses p hp hU
    (execCountSamples k r) (execCountInner m k r) (execCountOuter d) (execCountWidth n m k r d)
    (by positivity : 0<(1/(r : ℝ))) (execCountSamples_bound k r hr)
    (execCountInner_bound m k r)
  dsimp only at h ⊢
  rw [executableCount_choices_eq] at h
  exact h.trans (execCount_error n m k r d)

/-- Exact zero output on every tape, without invoking Algorithm S. -/
theorem executableFPRAS_zero {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (witnesses : Fin k ≃ U) (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ))) (r d : ℕ)
    (hz : eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω)) = 0) :
    G.executableFPRAS U vertices edges witnesses p r d = .ret 0 :=
  G.executableCount_zero U vertices edges witnesses p hp _ _ _ _ hz

/-- End-to-end conditional sampling on a uniform finite fair-bit tape. The
bounded-test guarantee is total variation on the finite output space. -/
theorem executableConditionalSampler_correct {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (witnesses : Fin k ≃ U) (hk : 0<k) (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ)))
    (hU : G.Feedback U {e | 0<(p e : ℝ)})
    (hZ : 0<eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω)))
    (d : ℕ) (f : (E → Bool) → ℝ) (hf0 : ∀ x, 0≤f x) (hf1 : ∀ x, f x≤1) :
    let N := executableSamplerBits n m k d
    |(∑ tape : Fin N → Bool, (1/(2 : ℝ)^N)*f
        ((G.executableConditionalSampler U vertices edges witnesses hk p d).run
          (BitProg.zeroExtend tape) 0).1)-
      (∑ ω, if G.Cyclic (retained ω) then edgeWeight (fun e => (p e : ℝ)) ω*f ω else 0)/
        eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω))| ≤ (1/2 : ℝ)^d := by
  dsimp only
  rw [BitProg.run_uniform
    (G.executableConditionalSampler_bits U vertices edges witnesses hk p d) f]
  have h := G.executableSample_error U vertices edges witnesses hk p hp hU hZ
    (execSampleBlocks d) (execSampleInner m k d) (execSampleWidth n m k d) f hf0 hf1
  have he : (1/2 : ℝ)^(execSampleBlocks d)+
      (k+2*m*(4*k*execSampleBlocks d) : ℕ)*(7/8 : ℝ)^(execSampleInner m k d)+
      (executableChoices n m k (4*k*execSampleBlocks d) (execSampleInner m k d) : ℝ)/
        (2 : ℝ)^(execSampleWidth n m k d) ≤ (1/2 : ℝ)^d := by
    simpa only [←executableSample_choices_eq,execSampleProposals,execSampleQueries] using
      execSample_error n m k d
  exact h.trans he

end
end Digraph
end DirectedCycleFPRAS
