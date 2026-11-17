module

public import DirectedCycleFPRAS.ExecutableGraph
public import DirectedCycleFPRAS.VertexAlgorithm

@[expose] public section

/-! Executable rational arithmetic and graph predicates for corrected rejection.
The casts below identify the actual computations with the real-valued model,
including invalid-oracle histories and the clipping convention. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
set_option linter.unusedSectionVars false

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def rationalEdgeWeight (p : E → ℚ) (ω : E → Bool) : ℚ :=
  ∏ e, if ω e then p e else 1-p e

theorem rationalEdgeWeight_cast (p : E → ℚ) (ω : E → Bool) :
    (rationalEdgeWeight p ω : ℝ) = edgeWeight (fun e => (p e : ℝ)) ω := by
  simp [rationalEdgeWeight, edgeWeight, Rat.cast_prod, apply_ite]

namespace Digraph
variable (G : Digraph V E)

/-- Number of compatible vertex witnesses, computed by finite searches. -/
def rationalMultiplicity (U : Finset V) (ω : E → Bool) : ℕ :=
  ∑ v : U, if G.onCycle ω v.val then 1 else 0

open Classical in
theorem rationalMultiplicity_cast (U : Finset V) (ω : E → Bool) :
    (G.rationalMultiplicity U ω : ℝ) = Mass.multiplicity (G.vertexEvents U) ω := by
  classical
  unfold rationalMultiplicity Mass.multiplicity
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro v _
  change ((if G.onCycle ω v.val then 1 else 0 : ℕ) : ℝ) =
    if G.VertexWitness {e | ω e = true} v.val then 1 else 0
  by_cases h : G.onCycle ω v.val = true
  · rw [ite_eq_left h, ite_eq_left ((G.onCycle_eq_true ω v.val).mp h)]
    norm_num
  · rw [ite_eq_right h, ite_eq_right (fun hh => h ((G.onCycle_eq_true ω v.val).mpr hh))]
    norm_num

/-- Computable support test for each residual reliability query. -/
def rationalFeasible (v : V) (q : E → ℚ) : Bool :=
  G.onCycle (fun e => decide (0 < q e)) v

theorem rationalFeasible_correct (U : Finset V) (v : U) (q : E → ℚ) :
    G.rationalFeasible v q = true ↔ G.vertexFeasible U v (fun e => (q e : ℝ)) := by
  rw [rationalFeasible, G.onCycle_eq_true, G.vertexWitness_iff_split]
  simp [vertexFeasible]

/-- The nominal rejection bias, computed entirely with rational arithmetic. -/
def rationalReject (U : Finset V) (p : E → ℚ) (w : U → ℚ)
    (i : U) (ω : E → Bool) (g : ℚ) : ℚ :=
  let μ := rationalEdgeWeight p ω
  if G.onCycle ω i.val && decide (0 < μ ∧ 0 < w i ∧ 0 < g) then
    max 0 (min 1 (μ / (2 * G.rationalMultiplicity U ω * w i * g))) else 0

theorem rationalReject_cast (U : Finset V) (p : E → ℚ)
    (hp : Prob01 (fun e => (p e : ℝ))) (w : U → ℚ) (i : U) (ω : E → Bool) (g : ℚ) :
    (G.rationalReject U p w i ω g : ℝ) =
      rejectionProbability (edgeLaw (fun e => (p e : ℝ)) (fun e => (hp e).1)
        (fun e => (hp e).2)).toMass (G.vertexEvents U) (fun i => (w i : ℝ)) i (ω, (g : ℝ)) := by
  classical
  have hv : (edgeLaw (fun e => (p e : ℝ)) (fun e => (hp e).1)
      (fun e => (hp e).2)).toMass.value ω = edgeWeight (fun e => (p e : ℝ)) ω := rfl
  simp only [rationalReject, rejectionProbability, hv]
  have hμ := rationalEdgeWeight_cast p ω
  have ht := G.rationalMultiplicity_cast U ω
  have hcond : (G.onCycle ω i.val && decide (0 < rationalEdgeWeight p ω ∧ 0 < w i ∧ 0 < g)) = true ↔
      G.vertexEvents U i ω ∧ 0 < edgeWeight (fun e => (p e : ℝ)) ω ∧
        0 < (w i : ℝ) ∧ 0 < (g : ℝ) := by
    rw [Bool.and_eq_true, decide_eq_true_eq, G.onCycle_eq_true]
    rw [← hμ]
    simp [vertexEvents, retained]
  simp only [Bool.and_eq_true, decide_eq_true_eq, G.onCycle_eq_true] at hcond ⊢
  by_cases h : G.VertexWitness {e | ω e = true} i.val ∧
      0 < rationalEdgeWeight p ω ∧ 0 < w i ∧ 0 < g
  · simp only [h, hcond.mp h, and_self, ite_true]
    push_cast
    rw [hμ, ht]
  · simp only [h, mt hcond.mpr h, ite_false, Rat.cast_zero]

end Digraph
end DirectedCycleFPRAS
