module

public import DirectedCycleFPRAS.VertexSampling
public import DirectedCycleFPRAS.RejectionHeight

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section

/-- Uniform choice precision for a total coupling budget `β`. -/
def choiceWidth (A : ℕ) (β : ℝ) : ℕ := Nat.clog 2 ⌈(A : ℝ)/β⌉₊

theorem choiceWidth_bound (A : ℕ) {β : ℝ} (hβ : 0 < β) :
    (A : ℝ)/(2 : ℝ)^choiceWidth A β ≤ β := by
  have hceil : (A : ℝ)/β ≤ (⌈(A : ℝ)/β⌉₊ : ℝ) := Nat.le_ceil _
  have hpow := Nat.le_pow_clog (b := 2) (by norm_num) ⌈(A : ℝ)/β⌉₊
  have hpow' : (⌈(A : ℝ)/β⌉₊ : ℝ) ≤ (2 : ℝ)^choiceWidth A β := by exact_mod_cast hpow
  apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ)^choiceWidth A β)).mpr
  have hh := (div_le_iff₀ hβ).mp (hceil.trans hpow')
  nlinarith

def oracleRepetitions (T : ℕ) (β : ℝ) : ℕ := confidenceRuns (β/(max 1 T : ℕ))

theorem oracleRepetitions_bound (T : ℕ) {β : ℝ} (hβ : 0 < β) :
    (T : ℝ)*(7/8 : ℝ)^oracleRepetitions T β ≤ β := by
  have hmax : (0 : ℝ) < (max 1 T : ℕ) := by exact_mod_cast (show 0 < max 1 T by omega)
  have h := confidenceRuns_bound (div_pos hβ hmax)
  have hT : (T : ℝ) ≤ (max 1 T : ℕ) := by exact_mod_cast le_max_right 1 T
  calc
    _ ≤ (T : ℝ)*(β/(max 1 T : ℕ)) := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg T)
    _ ≤ (max 1 T : ℕ)*(β/(max 1 T : ℕ)) := mul_le_mul_of_nonneg_right hT (by positivity)
    _ = β := by field_simp

def countingSamples (k : ℕ) (eps : ℝ) : ℕ := ⌈64*(k : ℝ)/eps^2⌉₊

def samplingBlocks (η : ℝ) : ℕ := choiceWidth 1 (η/3)

theorem samplingBlocks_bound {η : ℝ} (hη : 0 < η) :
    (1/2 : ℝ)^samplingBlocks η ≤ η/3 := by
  simpa [samplingBlocks, div_pow] using choiceWidth_bound 1 (show 0 < η/3 by positivity)

namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E) (U : Finset V)

/-- The paper's FPRAS with all sample, precision, and amplification budgets fixed. -/
def cycleFPRAS (p : E → ℝ) (hp : Prob01 p) (eps δ : ℝ) : Prog Empty ℝ :=
  let n := countingSamples U.card eps
  let T := U.card+2*Fintype.card E*n
  let A := n*(U.card+2*Fintype.card E+2)
  G.concreteVertex U p hp n (choiceWidth A (1/16)) (oracleRepetitions T (1/16)) (confidenceRuns δ)

/-- Main counting theorem for the current algorithm. -/
theorem cycleFPRAS_correct (p : E → ℝ) (hp : Prob01 p)
    (hU : G.Feedback U {e | 0 < p e})
    (hS : AlgSAccurate (rejectionAccuracy (Fintype.card E)))
    {eps δ : ℝ} (heps : 0 < eps) (hδ : 0 < δ) :
    (G.cycleFPRAS U p hp eps δ).exp noOracle
      (fun z => if eps*eventMass p (fun ω => G.Cyclic (retained ω)) <
        |z-eventMass p (fun ω => G.Cyclic (retained ω))| then 1 else 0) ≤ δ := by
  apply G.concreteVertex_correct U p hp hU hS heps hδ
  · exact Nat.le_ceil _
  · exact oracleRepetitions_bound _ (by norm_num)
  · exact choiceWidth_bound _ (by norm_num)

/-- Conditional sampling with the paper's logarithmic cap and three equal
error budgets. A positive union mass is required to define conditioning. -/
def cycleSampler (p : E → ℝ) (hp : Prob01 p) (d : U) (η : ℝ) : Prog Empty (E → Bool) :=
  let L := 4*U.card*samplingBlocks η
  let T := U.card+2*Fintype.card E*L
  let A := L*(U.card+2*Fintype.card E+2)
  G.concreteVertexSample U p hp d L (choiceWidth A (η/3)) (oracleRepetitions T (η/3))

/-- Main sampling theorem, in the bounded-test formulation of total variation. -/
theorem cycleSampler_correct (p : E → ℝ) (hp : Prob01 p) (d : U)
    (hZ : 0 < (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass.unionMass (G.vertexEvents U))
    (hS : AlgSAccurate (rejectionAccuracy (Fintype.card E)))
    {η : ℝ} (hη : 0 < η) (f : (E → Bool) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    |(G.cycleSampler U p hp d η).exp noOracle f-
      (unionLaw (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass (G.vertexEvents U) hZ).expectation f| ≤ η := by
  have ht := G.concreteVertexSample_error U p hp d hZ hS (samplingBlocks η)
    (choiceWidth ((4*U.card*samplingBlocks η)*(U.card+2*Fintype.card E+2)) (η/3))
    (oracleRepetitions (U.card+2*Fintype.card E*(4*U.card*samplingBlocks η)) (η/3)) f hf0 hf1
  have h₁ := samplingBlocks_bound hη
  have h₂ := oracleRepetitions_bound (U.card+2*Fintype.card E*(4*U.card*samplingBlocks η)) (show 0 < η/3 by positivity)
  have h₃ := choiceWidth_bound ((4*U.card*samplingBlocks η)*(U.card+2*Fintype.card E+2)) (show 0 < η/3 by positivity)
  unfold cycleSampler
  dsimp only
  linarith

/-- Sampling from the independent-edge law conditioned on a directed cycle. -/
theorem cycleSampler_cyclic_correct (p : E → ℝ) (hp : Prob01 p) (d : U)
    (hU : G.Feedback U {e | 0 < p e})
    (hZ : 0 < eventMass p (fun ω => G.Cyclic (retained ω)))
    (hS : AlgSAccurate (rejectionAccuracy (Fintype.card E)))
    {η : ℝ} (hη : 0 < η) (f : (E → Bool) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    |(G.cycleSampler U p hp d η).exp noOracle f-
      (∑ ω, if G.Cyclic (retained ω) then edgeWeight p ω*f ω else 0)/
        eventMass p (fun ω => G.Cyclic (retained ω))| ≤ η := by
  have hcover : 0 < (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass.unionMass (G.vertexEvents U) := by
    rw [show (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass.unionMass (G.vertexEvents U) =
      eventMass p (fun ω => G.Cyclic (retained ω)) from G.vertex_unionMass U hp hU]
    exact hZ
  have h := G.cycleSampler_correct U p hp d hcover hS hη f hf0 hf1
  rw [G.vertex_conditional_expectation U p hp hU hcover f] at h
  exact h

end Digraph
end
end DirectedCycleFPRAS
