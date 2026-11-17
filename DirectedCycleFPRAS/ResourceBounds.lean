module

public import DirectedCycleFPRAS.FinalGuarantees

@[expose] public section

/-! Explicit polynomial and logarithmic bounds for the final random-bit budgets.
`r` bounds reciprocal counting accuracy, and `d` bounds the binary logarithm
of reciprocal failure or sampling error. These are bit counts, not runtime. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section

/-- At the fixed rejection accuracy, the oracle sample budget is a polynomial. -/
theorem algSSamples_rejection (n j m : ℕ) :
    algSSamples n j (rejectionAccuracy m) = 4096*n^3*j*(m+1)^2 := by
  unfold algSSamples rejectionAccuracy
  have he : 16*(n : ℝ)^3*j/(1/(16*((m : ℝ)+1)))^2 =
      (4096*n^3*j*(m+1)^2 : ℕ) := by push_cast; field_simp; ring
  rw [he,Nat.ceil_natCast]

def oracleChoiceCap (n m : ℕ) : ℕ :=
  Digraph.algSChoices n m (4096*n^3*m*(m+1)^2)

def oracleBitCap (n m : ℕ) : ℕ :=
  (m+1)*(Nat.clog 2 (8*oracleChoiceCap n m)*oracleChoiceCap n m)

theorem oracleBitBudget_le (n m : ℕ) :
    oracleBitBudget n m (rejectionAccuracy m) ≤ oracleBitCap n m := by
  unfold oracleBitBudget oracleBitCap
  calc
    _ ≤ ∑ _j ∈ Finset.range (m+1),
        Nat.clog 2 (8*oracleChoiceCap n m)*oracleChoiceCap n m := by
      apply Finset.sum_le_sum
      intro j hj
      have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
      rw [algSBits,algSSamples_rejection]
      have hchoice : Digraph.algSChoices n j (4096*n^3*j*(m+1)^2) ≤ oracleChoiceCap n m := by
        unfold oracleChoiceCap Digraph.algSChoices Digraph.iterChoices
        gcongr
      exact Nat.mul_le_mul (Nat.clog_monotone 2 (Nat.mul_le_mul_left 8 hchoice)) hchoice
    _ = _ := by simp

/-- The fixed coupling budget contributes logarithmic choice precision. -/
theorem choiceWidth_sixteenth (A : ℕ) : choiceWidth A (1/16) = Nat.clog 2 (16*A) := by
  unfold choiceWidth
  have he : (A : ℝ)/(1/16) = (16*A : ℕ) := by push_cast; ring
  rw [he,Nat.ceil_natCast]

theorem oracleRepetitions_sixteenth (T : ℕ) :
    oracleRepetitions T (1/16) = 6*Nat.clog 2 (16*max 1 T) := by
  unfold oracleRepetitions confidenceRuns
  have he : (1 : ℝ)/((1/16)/(max 1 T : ℕ)) = ((16*max 1 T : ℕ) : ℝ) := by push_cast; simp [mul_comm]
  rw [he,Nat.ceil_natCast]

/-- A polynomial multiplied by logarithms in graph size and reciprocal error. -/
def countingBitCap (n m k r d : ℕ) : ℕ :=
  let D := 64*k*r^2
  let T := k+2*m*D
  let A := D*(k+2*m+2)
  Nat.clog 2 (16*A)*(6*d*A) +
    (6*d*T)*((6*Nat.clog 2 (16*max 1 T))*oracleBitCap (n+1) m)

theorem countingBitBudget_le (n m k r d : ℕ) {eps δ : ℝ}
    (heps : 0 < eps) (hr : 1/eps ≤ r) (hδ : 0 < δ) (hd : 1 ≤ δ*2^d) :
    countingBitBudget n m k eps δ ≤ countingBitCap n m k r d := by
  have hD := countingSamples_le k r heps hr
  have hout := confidenceRuns_le d hδ hd
  unfold countingBitBudget countingBitCap
  dsimp only
  rw [choiceWidth_sixteenth,oracleRepetitions_sixteenth]
  have hO := oracleBitBudget_le (n+1) m
  gcongr

/-- Choosing among `A` alternatives costs logarithmically many additional bits. -/
theorem choiceWidth_log_le (A d : ℕ) {β : ℝ} (hβ : 0 < β)
    (hd : 1 ≤ β*2^d) : choiceWidth A β ≤ Nat.clog 2 A+d := by
  apply choiceWidth_le A (Nat.clog 2 A+d) hβ
  have hA : (A : ℝ) ≤ 2^Nat.clog 2 A := by
    exact_mod_cast Nat.le_pow_clog (b := 2) (by norm_num) A
  rw [pow_add]
  have hh := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 2^Nat.clog 2 A by positivity)
  nlinarith

theorem oracleRepetitions_eq_choiceWidth (T : ℕ) (β : ℝ) :
    oracleRepetitions T β = 6*choiceWidth (max 1 T) β := by
  simp [oracleRepetitions,confidenceRuns,choiceWidth]

/-- Sampling bits are polynomial in the graph size and the logarithm of
reciprocal total-variation error. -/
def samplingBitCap (n m k d : ℕ) : ℕ :=
  let D := 4*k*d
  let T := k+2*m*D
  let A := D*(k+2*m+2)
  (Nat.clog 2 A+d)*A + T*((6*(Nat.clog 2 (max 1 T)+d))*oracleBitCap (n+1) m)

theorem samplingBitBudget_le (n m k d : ℕ) {η : ℝ} (hη : 0 < η)
    (hd : 3 ≤ η*2^d) : samplingBitBudget n m k η ≤ samplingBitCap n m k d := by
  have hD := samplingBlocks_le d hη hd
  have hβ : 0 < η/3 := by positivity
  have hβd : 1 ≤ (η/3)*2^d := by nlinarith
  unfold samplingBitBudget samplingBitCap
  dsimp only
  rw [oracleRepetitions_eq_choiceWidth]
  apply Nat.le_trans (Nat.add_le_add
    (Nat.mul_le_mul_right _ (choiceWidth_log_le _ d hβ hβd))
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left 6 (choiceWidth_log_le _ d hβ hβd)))))
  have hO := oracleBitBudget_le (n+1) m
  gcongr

namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E) (U : Finset V)

theorem cycleFPRAS_bitCost_cap (p : E → ℝ) (hp : Prob01 p) (r d : ℕ)
    {eps δ : ℝ} (heps : 0 < eps) (hr : 1/eps ≤ r) (hδ : 0 < δ) (hd : 1 ≤ δ*2^d) :
    Prog.BitCost (fun _ : Empty => 0) (G.cycleFPRAS U p hp eps δ)
      (countingBitCap (Fintype.card V) (Fintype.card E) U.card r d) :=
  (G.cycleFPRAS_bitCost U p hp eps δ).mono (countingBitBudget_le _ _ _ r d heps hr hδ hd)

theorem cycleSampler_bitCost_cap (p : E → ℝ) (hp : Prob01 p) (u : U) (d : ℕ)
    {η : ℝ} (hη : 0 < η) (hd : 3 ≤ η*2^d) :
    Prog.BitCost (fun _ : Empty => 0) (G.cycleSampler U p hp u η)
      (samplingBitCap (Fintype.card V) (Fintype.card E) U.card d) :=
  (G.cycleSampler_bitCost U p hp u η).mono (samplingBitBudget_le _ _ _ d hη hd)
end Digraph

end
end DirectedCycleFPRAS
