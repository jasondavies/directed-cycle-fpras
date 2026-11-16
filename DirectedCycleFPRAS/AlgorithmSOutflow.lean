module

public import DirectedCycleFPRAS.AlgorithmSPools
public import DirectedCycleFPRAS.HarrisReliability

@[expose] public section

/-! FFG Lemma 8 for the concrete first-open weights and argmax rule. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E) (p : E → ℝ)

omit [Fintype V] [DecidableEq V] in
theorem firstOpenWeight_le (hp : Prob01 p) (R : Finset V) (u : V) (e : E) :
    G.firstOpenWeight p R u e ≤ if G.cutAt R u e then p e else 0 := by
  unfold firstOpenWeight
  split_ifs
  · apply mul_le_of_le_one_right (hp e).1
    exact Finset.prod_le_one₀ (fun j _ => sub_nonneg.mpr (hp j).2)
      (fun j _ => by linarith [(hp j).1])
  · rfl

omit [Fintype V] [DecidableEq V] in
/-- The outgoing-cut probability is bounded by the sum of arc probabilities. -/
theorem gammaS_le_sum (hp : Prob01 p) (R : Finset V) (u : V) :
    G.gammaS p R u ≤ ∑ e, if G.cutAt R u e then p e else 0 :=
  Finset.sum_le_sum fun e _ => G.firstOpenWeight_le p hp R u e

/-- Charging the outflow to arcs counts each arc at its unique source. -/
theorem phiS_le_cut_sum (hp : Prob01 p) (R : Finset V) (qh : V → ℝ)
    (hq : ∀ u, 0 ≤ qh u) :
    G.phiS p R qh ≤ ∑ e, if G.source e ∈ R ∧ G.target e ∉ R
      then qh (G.source e)*p e else 0 := by
  calc
    _ ≤ ∑ u, if u ∈ R then qh u * (∑ e, if G.cutAt R u e then p e else 0) else 0 := by
      apply Finset.sum_le_sum
      intro u _
      split_ifs
      · exact mul_le_mul_of_nonneg_left (G.gammaS_le_sum p hp R u) (hq u)
      · rfl
    _ = _ := by
      have hi (u : V) : (if u ∈ R then qh u * (∑ e, if G.cutAt R u e then p e else 0) else 0) =
          ∑ e, if u ∈ R then qh u * (if G.cutAt R u e then p e else 0) else 0 := by
        by_cases hu : u ∈ R <;> simp [hu, Finset.mul_sum]
      simp_rw [hi]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_eq_single (G.source e)]
      · by_cases hs : G.source e ∈ R <;> by_cases ht : G.target e ∈ R <;>
          simp [cutAt, hs, ht]
      · intro u _ hu
        simp [cutAt, Ne.symm hu]
      · simp

/-- If `e` maximizes the cut score, total outflow is at most m times its
score. This statement also covers zero probabilities and estimates. -/
theorem phiS_le_max_score (hp : Prob01 p) (R : Finset V) (qh : V → ℝ)
    (hq : ∀ u, 0 ≤ qh u) (e : E)
    (hmax : ∀ j, G.source j ∈ R ∧ G.target j ∉ R →
      qh (G.source j)*p j ≤ qh (G.source e)*p e) :
    G.phiS p R qh ≤ Fintype.card E * (qh (G.source e)*p e) := by
  apply (G.phiS_le_cut_sum p hp R qh hq).trans
  calc
    _ ≤ ∑ _j : E, qh (G.source e)*p e := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs with h
      · exact hmax j h
      · exact mul_nonneg (hq _) (hp e).1
    _ = _ := by simp

/-- The actual argmax selected by Algorithm S satisfies the outflow bound. -/
theorem phiS_le_argmax (hp : Prob01 p) (R : Finset V) (qh : V → ℝ)
    (hq : ∀ u, 0 ≤ qh u) (e : E)
    (he : ((arcOrder E).filter fun j => G.source j ∈ R ∧ G.target j ∉ R).argmax
      (fun j => qh (G.source j)*p j) = some e) :
    G.phiS p R qh ≤ Fintype.card E * (qh (G.source e)*p e) := by
  apply G.phiS_le_max_score p hp R qh hq e
  intro j hj
  apply List.le_of_mem_argmax (f := fun j => qh (G.source j)*p j)
    (l := (arcOrder E).filter fun j => G.source j ∈ R ∧ G.target j ∉ R)
    (by simpa [arcOrder] using hj)
  rw [he]
  simp

/-- Approximate-estimate form of FFG Lemma 8. -/
theorem phiS_le_reliability_ratio (hp : Prob01 p) (s : V) (R : Finset V) (qh : V → ℝ)
    (hq : ∀ u, 0 ≤ qh u) (e : E)
    (hmax : ∀ j, G.source j ∈ R ∧ G.target j ∉ R →
      qh (G.source j)*p j ≤ qh (G.source e)*p e)
    (hu : 0 < G.reliability p s (G.source e)) :
    G.phiS p R qh ≤ Fintype.card E * qh (G.source e) *
      G.reliability p s (G.target e) / G.reliability p s (G.source e) := by
  apply (G.phiS_le_max_score p hp R qh hq e hmax).trans
  have harc := G.reliability_arc p hp s e
  have he : p e ≤ G.reliability p s (G.target e)/G.reliability p s (G.source e) := by
    apply (le_div_iff₀ hu).mpr
    simpa [mul_comm] using harc
  have hm := mul_le_mul_of_nonneg_left he
    (mul_nonneg (Nat.cast_nonneg (Fintype.card E)) (hq (G.source e)))
  simpa [mul_div_assoc, mul_assoc] using hm

end Digraph
end
end DirectedCycleFPRAS
