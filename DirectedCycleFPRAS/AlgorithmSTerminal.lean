module

public import DirectedCycleFPRAS.AlgorithmSVariance

@[expose] public section

/-! Accuracy of Algorithm S's early exits. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [ArcEnumeration E] [DecidableEq E]
variable (G : Digraph V E) (p : E → ℝ)

def bestArc (R : Finset V) (qh : V → ℝ) : Option E :=
  ((arcOrder E).filter fun e => G.source e∈R ∧ G.target e∉R).argmax
    (fun e => qh (G.source e)*p e)

theorem bestArc_mem (R : Finset V) (qh : V → ℝ) {e : E} (he : G.bestArc p R qh=some e) :
    G.source e∈R ∧ G.target e∉R := by
  unfold bestArc at he
  have h := List.argmax_mem (show e∈((arcOrder E).filter fun e => G.source e∈R ∧ G.target e∉R).argmax
    (fun e => qh (G.source e)*p e) by rw [he]; simp)
  exact (List.mem_filter.mp h).2 |> of_decide_eq_true

theorem bestArc_max (R : Finset V) (qh : V → ℝ) {e : E} (he : G.bestArc p R qh=some e) :
    ∀ j, G.source j∈R ∧ G.target j∉R → qh (G.source j)*p j ≤ qh (G.source e)*p e := by
  unfold bestArc at he
  intro j hj
  apply List.le_of_mem_argmax (f := fun j => qh (G.source j)*p j)
    (l := (arcOrder E).filter fun j => G.source j∈R ∧ G.target j∉R)
    (by simpa using hj)
  rw [he]
  simp

/-- The prediction of an unresolved target is precisely the outflow times
its record probability; this also covers zero outflow. -/
theorem prediction_unresolved (hp : Prob01 p) (R : Finset V) (qh : V → ℝ)
    (pools : V → List (Finset V)) (M : ℕ) (hpool : PoolInvariant R qh pools M)
    (v : V) (hv : v∉R) :
    G.prediction p R qh pools v = G.phiS p R qh *
      (G.sIter p R qh pools M v).exp noOracle (fun o => o.elim 0 (fun _ => 1)) := by
  rw [G.sIter_weighted_score p hp R qh pools M hpool v (fun _ => 1)]
  unfold prediction
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x∈R
  · simp only [ite_eq_left hx]
    congr 2
    apply congrArg List.sum
    apply List.map_congr_left
    intro A hA
    have hxv : x≠v := fun h => hv (h ▸ hx)
    rw [G.reachScore_split p hp R A x v v (hpool.contains x hx A hA) hxv,
      G.reachScore_resolved p (insert v R) A x v (by simp) hxv, zero_add]
    congr 1
    funext D
    exact G.reachScore_self p (insert v R) D v
  · simp [hx]

theorem prediction_zero_of_outflow_zero (hp : Prob01 p) (R : Finset V) (qh : V → ℝ)
    (pools : V → List (Finset V)) (M : ℕ) (hpool : PoolInvariant R qh pools M)
    (v : V) (hv : v∉R) (hΦ : G.phiS p R qh=0) : G.prediction p R qh pools v=0 := by
  rw [G.prediction_unresolved p hp R qh pools M hpool v hv,hΦ,zero_mul]

theorem phiS_zero_of_no_arc (hp : Prob01 p) (R : Finset V) (qh : V → ℝ)
    (hq : ∀ x,0≤qh x) (he : G.bestArc p R qh=none) : G.phiS p R qh=0 := by
  have hc : ∀ e, ¬(G.source e∈R ∧ G.target e∉R) := by
    have hnil := List.argmax_eq_none.mp he
    intro e he
    have hm : e∈(arcOrder E).filter (fun e => G.source e∈R ∧ G.target e∉R) := by simp [he]
    rw [hnil] at hm
    exact List.not_mem_nil hm
  apply le_antisymm _ (G.phiS_nonneg p hp R qh hq)
  simpa [hc] using G.phiS_le_cut_sum p hp R qh hq

theorem phiS_zero_of_nonpositive_best (hp : Prob01 p) (R : Finset V) (qh : V → ℝ)
    (hq : ∀ x,0≤qh x) (e : E) (he : G.bestArc p R qh=some e)
    (hz : qh (G.source e)*p e≤0) : G.phiS p R qh=0 := by
  apply le_antisymm _ (G.phiS_nonneg p hp R qh hq)
  have h := G.phiS_le_argmax p hp R qh hq e he
  have h' := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (Fintype.card E)) hz
  exact h.trans h'

end Digraph
end
end DirectedCycleFPRAS
