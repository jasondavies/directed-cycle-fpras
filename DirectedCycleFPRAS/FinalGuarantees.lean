module

public import DirectedCycleFPRAS.Parameters

@[expose] public section

/-! Resource guarantees for the final programs, with every parameter fixed.
The budgets count fair bits and rational output height; they do not charge
machine operations. Dyadic bounds expose the logarithmic confidence dependence. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section

/-- Total counting bits, including the inner and outer median repetitions. -/
def countingBitBudget (n m k : ℕ) (eps δ : ℝ) : ℕ :=
  let D := countingSamples k eps
  let T := k + 2*m*D
  let A := D*(k + 2*m + 2)
  choiceWidth A (1/16)*(confidenceRuns δ*A) +
    (confidenceRuns δ*T)*(oracleRepetitions T (1/16)*
      oracleBitBudget (n+1) m (rejectionAccuracy m))

/-- Total conditional-sampling bits, including the capped proposals. -/
def samplingBitBudget (n m k : ℕ) (η : ℝ) : ℕ :=
  let D := 4*k*samplingBlocks η
  let T := k + 2*m*D
  let A := D*(k + 2*m + 2)
  choiceWidth A (η/3)*A + T*(oracleRepetitions T (η/3)*
    oracleBitBudget (n+1) m (rejectionAccuracy m))

/-- A polynomial bound on the number of proposals in reciprocal accuracy. -/
theorem countingSamples_le (k r : ℕ) {eps : ℝ} (heps : 0 < eps)
    (hr : 1/eps ≤ r) : countingSamples k eps ≤ 64*k*r^2 := by
  apply Nat.ceil_le.mpr
  push_cast
  have hs : (1/eps)^2 ≤ (r : ℝ)^2 := by
    exact pow_le_pow_left₀ (by positivity) hr 2
  have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 64*(k : ℝ) by positivity)
  simpa only [one_div,inv_pow,div_eq_mul_inv,one_mul] using hh

/-- A dyadic lower bound on the error budget bounds the draw width. -/
theorem choiceWidth_le (A b : ℕ) {β : ℝ} (hβ : 0 < β)
    (h : (A : ℝ) ≤ β*2^b) : choiceWidth A β ≤ b := by
  apply Nat.clog_le_of_le_pow
  apply Nat.ceil_le.mpr
  rw [Nat.cast_pow,Nat.cast_ofNat]
  exact (div_le_iff₀ hβ).mpr (by nlinarith)

theorem confidenceRuns_le (d : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (h : 1 ≤ δ*2^d) : confidenceRuns δ ≤ 6*d := by
  apply Nat.mul_le_mul_left
  simpa only [choiceWidth,Nat.cast_one] using choiceWidth_le 1 d hδ (by simpa using h)

theorem samplingBlocks_le (d : ℕ) {η : ℝ} (hη : 0 < η)
    (h : 3 ≤ η*2^d) : samplingBlocks η ≤ d := by
  apply choiceWidth_le 1 d (by positivity : 0 < η/3)
  norm_num
  nlinarith

namespace Prog
variable {Q : Type}

/-- Even an empty repetition of the constant zero program returns zero. -/
theorem medianOf_zero (k : ℕ) : (Prog.ret (Q := Q) (0 : ℝ)).medianOf k = .ret 0 := by
  have hrep (n : ℕ) : ∃ xs : Samples ℝ n,
      (Prog.ret (Q := Q) (0 : ℝ)).replicate n = .ret xs ∧
      ∀ i, samplesToFn n xs i = 0 := by
    induction n with
    | zero => exact ⟨(), rfl, fun i => i.elim0⟩
    | succ n ih =>
      obtain ⟨xs, hx, hz⟩ := ih
      refine ⟨(0,xs), ?_, ?_⟩
      · simp only [replicate,bind,hx]
      · intro i
        exact Fin.cases rfl (fun j => hz j) i
  obtain ⟨xs,hx,hz⟩ := hrep k
  rw [medianOf,hx,bind]
  congr 1
  exact median_property (P := fun x => x=0) rfl _ hz
end Prog

namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E) (U : Finset V)

theorem cycleFPRAS_bitCost (p : E → ℝ) (hp : Prob01 p) (eps δ : ℝ) :
    Prog.BitCost (fun _ : Empty => 0) (G.cycleFPRAS U p hp eps δ)
      (countingBitBudget (Fintype.card V) (Fintype.card E) U.card eps δ) := by
  simpa only [cycleFPRAS,countingBitBudget,Fintype.card_option] using
    G.concreteVertex_bitCost U p hp (countingSamples U.card eps)
      (choiceWidth (countingSamples U.card eps*(U.card+2*Fintype.card E+2)) (1/16))
      (oracleRepetitions (U.card+2*Fintype.card E*countingSamples U.card eps) (1/16))
      (confidenceRuns δ)

theorem cycleSampler_bitCost (p : E → ℝ) (hp : Prob01 p) (d : U) (η : ℝ) :
    Prog.BitCost (fun _ : Empty => 0) (G.cycleSampler U p hp d η)
      (samplingBitBudget (Fintype.card V) (Fintype.card E) U.card η) := by
  simpa only [cycleSampler,samplingBitBudget,Fintype.card_option] using
    G.concreteVertexSample_bitCost U p hp d (4*U.card*samplingBlocks η)
      (choiceWidth ((4*U.card*samplingBlocks η)*(U.card+2*Fintype.card E+2)) (η/3))
      (oracleRepetitions (U.card+2*Fintype.card E*(4*U.card*samplingBlocks η)) (η/3))

/-- Exact zero detection survives discretization, both amplifications, and
replacement of every reliability call by its concrete implementation. -/
theorem cycleFPRAS_zero (p : E → ℝ) (hp : Prob01 p) (eps δ : ℝ)
    (hz : eventMass p (fun ω => G.Cyclic (retained ω)) = 0) :
    G.cycleFPRAS U p hp eps δ = .ret 0 := by
  simp only [cycleFPRAS,concreteVertex,G.vertexAlgorithm_zero U p hp _ hz,
    Prog.discretise,Prog.medianOf_zero,Prog.inline]

/-- Rational output height of the fully parameterized counting program. -/
theorem cycleFPRAS_height {p : E → ℝ} (hp01 : Prob01 p) (eps δ : ℝ)
    (num den : E → ℕ) {H : ℕ} (hH : 1 ≤ H) (hd : ∀ e, 0 < den e)
    (hn : ∀ e, num e ≤ den e) (hden : ∀ e, den e ≤ H)
    (hp : ∀ e, p e = (num e : ℝ)/den e) :
    Prog.Sat (fun _ => True) (fun _ => True)
      (Height (countHeight U.card (countingSamples U.card eps)
        (oracleHeight (Fintype.card V+1) (Fintype.card E) H (rejectionAccuracy (Fintype.card E)))))
      (G.cycleFPRAS U p hp01 eps δ) := by
  simpa only [cycleFPRAS,Fintype.card_option] using
    G.concreteVertex_height U hp01 (countingSamples U.card eps)
      (choiceWidth (countingSamples U.card eps*(U.card+2*Fintype.card E+2)) (1/16))
      (oracleRepetitions (U.card+2*Fintype.card E*countingSamples U.card eps) (1/16))
      (confidenceRuns δ) num den hH hd hn hden hp

end Digraph
end
end DirectedCycleFPRAS
