module

public import DirectedCycleFPRAS.ExecutableFPRAS

@[expose] public section

set_option linter.unusedSectionVars false

/-! Public conditional sampling with an explicit undefined case. The support
check precedes construction of the positive-mass sampling program. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E) (U : Finset V)

/-- Return `none` when the positive support is acyclic. A valid feedback cover
is nonempty whenever that support is cyclic; an empty invalid cover also
returns `none`. The positive branch uses the existing finite-bit sampler. -/
def checkedConditionalSampler {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (witnesses : Fin k ≃ U) (p : E → ℚ) (d : ℕ) : BitProg (Option (E → Bool)) :=
  if G.hasCycle (fun e => decide (0 < p e)) then
    if hk : 0 < k then
      (G.executableConditionalSampler U vertices edges witnesses hk p d).bind
        (fun ω => .ret (some ω))
    else .ret none
  else .ret none

theorem checkedConditionalSampler_bits {n m k : ℕ}
    (vertices : Fin n ≃ V) (edges : Fin m ≃ E) (witnesses : Fin k ≃ U)
    (p : E → ℚ) (d : ℕ) :
    BitProg.Bits (G.checkedConditionalSampler U vertices edges witnesses p d)
      (executableSamplerBits n m k d) := by
  unfold checkedConditionalSampler
  split_ifs with hc hk
  · simpa only [Nat.add_zero] using
      (G.executableConditionalSampler_bits U vertices edges witnesses hk p d).bind
        (K := 0) (fun ω => BitProg.Bits.ret (some ω) 0)
  · exact .ret _ _
  · exact .ret _ _

open Classical
noncomputable section

/-- The computable support test detects exactly positive cyclicity probability. -/
theorem supportCycle_iff_pos (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ))) :
    G.hasCycle (fun e => decide (0 < p e)) = true ↔
      0 < eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω)) := by
  rw [G.hasCycle_eq_true]
  have h : (0 < eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω))) ↔
      G.Cyclic {e | 0 < (p e : ℝ)} :=
    G.cycleMass_pos_iff _ (fun e => (hp e).1) (fun e => (hp e).2)
  simpa using h.symm

/-- A valid feedback cover has a witness whenever cyclicity has positive mass. -/
theorem positive_cover_card {k : ℕ} (witnesses : Fin k ≃ U)
    (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ)))
    (hU : G.Feedback U {e | 0 < (p e : ℝ)})
    (hZ : 0 < eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω))) : 0 < k := by
  have hc := (G.cycleMass_pos_iff _ (fun e => (hp e).1) (fun e => (hp e).2)).mp hZ
  obtain ⟨v, hv, _⟩ := (G.feedback_cover U _ hU).mp hc
  exact lt_of_le_of_lt (Nat.zero_le _) (witnesses.symm ⟨v,hv⟩).isLt

/-- Zero mass is reported before any sampling program is constructed. -/
theorem checkedConditionalSampler_zero {n m k : ℕ}
    (vertices : Fin n ≃ V) (edges : Fin m ≃ E) (witnesses : Fin k ≃ U)
    (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ))) (d : ℕ)
    (hZ : eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω)) = 0) :
    G.checkedConditionalSampler U vertices edges witnesses p d = .ret none := by
  have hc : G.hasCycle (fun e => decide (0 < p e)) ≠ true := by
    intro hc
    have hz := (G.supportCycle_iff_pos p hp).mp hc
    rw [hZ] at hz
    exact (lt_irrefl 0) hz
  simp only [checkedConditionalSampler, ite_eq_right hc]

/-- Positive executions return the core sampler's output and consume exactly
its bits; the wrapper introduces no additional random choice. -/
theorem checkedConditionalSampler_run_positive {n m k : ℕ}
    (vertices : Fin n ≃ V) (edges : Fin m ≃ E) (witnesses : Fin k ≃ U) (hk : 0 < k)
    (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ))) (d : ℕ)
    (hZ : 0 < eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω)))
    (tape : ℕ → Bool) (offset : ℕ) :
    (G.checkedConditionalSampler U vertices edges witnesses p d).run tape offset =
      let r := (G.executableConditionalSampler U vertices edges witnesses hk p d).run tape offset
      (some r.1, r.2) := by
  have hc := (G.supportCycle_iff_pos p hp).mpr hZ
  simp only [checkedConditionalSampler, ite_eq_left hc, dite_eq_left hk, BitProg.run_bind,
    BitProg.run]

/-- For valid probabilities and a feedback cover, the undefined status occurs
exactly at zero mass, on every tape and from every offset. -/
theorem checkedConditionalSampler_none_iff {n m k : ℕ}
    (vertices : Fin n ≃ V) (edges : Fin m ≃ E) (witnesses : Fin k ≃ U)
    (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ)))
    (hU : G.Feedback U {e | 0 < (p e : ℝ)}) (d : ℕ) (tape : ℕ → Bool) (offset : ℕ) :
    ((G.checkedConditionalSampler U vertices edges witnesses p d).run tape offset).1 = none ↔
      eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω)) = 0 := by
  by_cases hz : eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω)) = 0
  · rw [G.checkedConditionalSampler_zero U vertices edges witnesses p hp d hz]
    simp [BitProg.run, hz]
  · have hpZ := lt_of_le_of_ne (eventMass_nonneg hp _) (Ne.symm hz)
    rw [G.checkedConditionalSampler_run_positive U vertices edges witnesses
      (G.positive_cover_card U witnesses p hp hU hpZ) p hp d hpZ tape offset]
    simp [hz]

/-- The checked frontend has the same conditional-sampling accuracy on
positive inputs, with no nonempty-cover hypothesis supplied by the caller. -/
theorem checkedConditionalSampler_correct {n m k : ℕ}
    (vertices : Fin n ≃ V) (edges : Fin m ≃ E) (witnesses : Fin k ≃ U)
    (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ)))
    (hU : G.Feedback U {e | 0 < (p e : ℝ)})
    (hZ : 0 < eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω)))
    (d : ℕ) (f : (E → Bool) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    let N := executableSamplerBits n m k d
    |(∑ tape : Fin N → Bool, (1/(2 : ℝ)^N)*
        (((G.checkedConditionalSampler U vertices edges witnesses p d).run
          (BitProg.zeroExtend tape) 0).1.elim 0 f))-
      (∑ ω, if G.Cyclic (retained ω) then edgeWeight (fun e => (p e : ℝ)) ω*f ω else 0)/
        eventMass (fun e => (p e : ℝ)) (fun ω => G.Cyclic (retained ω))| ≤ (1/2 : ℝ)^d := by
  have hk := G.positive_cover_card U witnesses p hp hU hZ
  dsimp only
  simp_rw [G.checkedConditionalSampler_run_positive U vertices edges witnesses hk p hp d hZ]
  exact G.executableConditionalSampler_correct U vertices edges witnesses hk p hp hU hZ d f hf0 hf1

end
end Digraph
end DirectedCycleFPRAS
