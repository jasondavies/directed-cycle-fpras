module

public import DirectedCycleFPRAS.RationalAlgorithmSAccuracy
public import DirectedCycleFPRAS.ResourceBounds
public import DirectedCycleFPRAS.VertexWitness

@[expose] public section

/-! The rational vertex-witness reliability callback. Zero-probability edges
are retained in the input representation: the accuracy theorem already covers
all probabilities in [0,1], so no noncomputable edge subtype is constructed. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E)

/-- The split graph with an executable equality test. -/
def rationalSplit (v : V) : Digraph (Option V) E where
  source e := some (G.source e)
  target e := if G.target e=v then none else some (G.target e)

/-- The oracle budget is a natural polynomial at the fixed rejection accuracy. -/
def rationalVertexSamples (n m : ℕ) : ℕ := 4096*(n+1)^3*m*(m+1)^2

/-- Nominal reliability callback before inner amplification. -/
def rationalVertexQuery {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (v : V) (p : E → ℚ) : RatProg ℚ :=
  (G.rationalSplit v).rationalAlgS p ((finSuccEquiv n).trans vertices.optionCongr) edges
    order (fun e => order.idxOf e) (some v) none (rationalVertexSamples n m)

open Classical
noncomputable section
set_option linter.unusedSectionVars false

theorem rationalSplit_eq (v : V) : G.rationalSplit v = G.splitVertex v := by
  unfold rationalSplit splitVertex
  congr 1

theorem rationalVertexQuery_law {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (v : V) (p : E → ℚ) (f : ℝ → ℝ) :
    (G.rationalVertexQuery vertices edges order v p).nominal.exp noOracle (fun q => f (q : ℝ)) =
      ((G.splitVertex v).orderedAlgS (fun e => (p e : ℝ)) order (fun e => order.idxOf e)
        (Fintype.card (Option V)+1) (Fintype.card (Option V)) (some v) none
        (rationalVertexSamples n m)).exp noOracle f := by
  unfold rationalVertexQuery
  rw [G.rationalSplit_eq]
  exact (G.splitVertex v).rationalAlgS_law p _ edges order _ (some v) none _ f

theorem rationalVertexQuery_accuracy {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (hnodup : order.Nodup) (hcomplete : ∀ e, e∈order)
    (v : V) (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ)))
    (hq : 0<(G.splitVertex v).reliability (fun e => (p e : ℝ)) (some v) none) :
    (G.rationalVertexQuery vertices edges order v p).nominal.exp noOracle
      (fun z => if |(z : ℝ)-(G.splitVertex v).reliability (fun e => (p e : ℝ)) (some v) none|≤
        rejectionAccuracy m*(G.splitVertex v).reliability (fun e => (p e : ℝ)) (some v) none then 0 else 1) ≤ 1/8 := by
  unfold rationalVertexQuery rationalVertexSamples
  rw [G.rationalSplit_eq,← algSSamples_rejection (n+1) m m]
  exact (G.splitVertex v).rationalAlgS_nominal_accuracy p hp
    ((finSuccEquiv n).trans vertices.optionCongr) edges order hnodup hcomplete (some v) none hq
    (rejectionAccuracy_bounds m).1 ((rejectionAccuracy_bounds m).2.trans (by norm_num))

end
end Digraph
end DirectedCycleFPRAS
