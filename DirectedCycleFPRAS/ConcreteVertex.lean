module

public import DirectedCycleFPRAS.VertexAlgorithm
public import DirectedCycleFPRAS.AlgorithmSOracle
public import DirectedCycleFPRAS.AlgorithmSAccuracy

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
namespace Prog
variable {Q α : Type}
theorem QueryBound.discretise {m : Prog Q α} {T : ℕ} (h : QueryBound m T) (b : ℕ) :
    QueryBound (m.discretise b) T := by
  induction h with
  | ret a n => exact .ret _ _
  | query x k n h ih => exact .query _ _ _ ih
  | choose p k n h ih => exact .draw ih
  | work c m n h ih => exact .work _ _ _ ih
end Prog
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E) (U : Finset V)

def vertexOracle (R : ReliabilityEstimator) : Oracle (VertexQuery (E := E) U) where
  Seed x := ((G.splitVertex x.1.val).oracleOfEstimator R).Seed (x.2, some x.1.val, none)
  law x := ((G.splitVertex x.1.val).oracleOfEstimator R).law (x.2, some x.1.val, none)
  answer x := ((G.splitVertex x.1.val).oracleOfEstimator R).answer (x.2, some x.1.val, none)

theorem vertexOracle_correct (R : ReliabilityEstimator) {a : ℝ} (hR : R.Correct a)
    (x : VertexQuery (E := E) U) :
    (∑ s, if G.VertexGood U a x ((G.vertexOracle U R).answer x s)
      then 0 else ((G.vertexOracle U R).law x).value s) ≤ 1/4 := by
  by_cases hq : Prob01 x.2
  · by_cases hpos : 0 < eventMass x.2 (G.vertexEvents U x.1)
    · have hrel := (G.splitVertex x.1.val).reliability_positivePart hq (some x.1.val) none
      have hid := G.vertex_weight_reliability x.2 x.1.val
      have h := hR (Option V) {e : E // 0 < x.2 e}
        ((G.splitVertex x.1.val).positivePart x.2) (fun e => x.2 e) (some x.1.val) none
        (fun e => ⟨e.property,(hq e.val).2⟩) (by rw [hrel, ← hid]; exact hpos)
      rw [hrel, ← hid] at h
      simp only [VertexGood, hq, hpos, true_implies]
      rw [show G.vertexEvents U x.1 = (fun ω => G.VertexWitness (retained ω) x.1.val) from rfl]
      exact h
    · simp [VertexGood, hpos]
  · simp [VertexGood, hq]

theorem vertexGood_interval (a : ℝ) (x : VertexQuery (E := E) U) (r s t : ℝ)
    (hr : G.VertexGood U a x r) (ht : G.VertexGood U a x t) (hrs : r ≤ s) (hst : s ≤ t) :
    G.VertexGood U a x s := by
  intro hq hp
  rcases abs_le.mp (hr hq hp) with ⟨hr₁,hr₂⟩
  rcases abs_le.mp (ht hq hp) with ⟨ht₁,ht₂⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem vertexOracle_amplified (R : ReliabilityEstimator) {a : ℝ} (hR : R.Correct a)
    (j : ℕ) (x : VertexQuery (E := E) U) :
    (∑ s, if G.VertexGood U a x (((G.vertexOracle U R).amplify j).answer x s)
      then 0 else (((G.vertexOracle U R).amplify j).law x).value s) ≤ (7/8 : ℝ)^j :=
  Oracle.amplify_failure _ j x (G.vertexGood_interval U a x) (G.vertexOracle_correct U R hR x)

/-- Each vertex query is implemented by Algorithm S on its split graph. -/
def vertexAlgSQuery (a : ℝ) (x : VertexQuery (E := E) U) : Prog Empty ℝ :=
  (G.splitVertex x.1.val).algSQuery a (x.2, some x.1.val, none)

/-- Call-free counting program, including both amplification stages. -/
def concreteVertex (p : E → ℝ) (hp : Prob01 p) (n b inner outer : ℕ) : Prog Empty ℝ :=
  (((G.vertexAlgorithm U p hp n).discretise b).medianOf outer).inline
    (fun x => (G.vertexAlgSQuery U (rejectionAccuracy (Fintype.card E)) x).medianOf inner)

theorem concreteVertex_law (p : E → ℝ) (hp : Prob01 p) (n b inner outer : ℕ) (f : ℝ → ℝ) :
    (G.concreteVertex U p hp n b inner outer).exp noOracle f =
      (((G.vertexAlgorithm U p hp n).discretise b).medianOf outer).exp
        ((G.vertexOracle U (algSEstimator (rejectionAccuracy (Fintype.card E)))).amplify inner) f :=
  Prog.exp_inline_amplify (G.vertexAlgSQuery U (rejectionAccuracy (Fintype.card E))) inner _ f

/-- Concrete counting accuracy, using the proved Algorithm S bound at a
precision independent of `eps` and `δ`. -/
theorem concreteVertex_correct (p : E → ℝ) (hp : Prob01 p)
    (hU : G.Feedback U {e | 0 < p e})
    {eps δ : ℝ} (heps : 0 < eps) (hδ : 0 < δ) {n b inner : ℕ}
    (hn : 64*(U.card : ℝ)/eps^2 ≤ n)
    (hqueries : (U.card+2*Fintype.card E*n : ℕ)*(7/8 : ℝ)^inner ≤ 1/16)
    (hbits : (n*(U.card+2*Fintype.card E+2) : ℕ)/(2 : ℝ)^b ≤ 1/16) :
    (G.concreteVertex U p hp n b inner (confidenceRuns δ)).exp noOracle
      (fun z => if eps*eventMass p (fun ω => G.Cyclic (retained ω)) <
        |z-eventMass p (fun ω => G.Cyclic (retained ω))| then 1 else 0) ≤ δ := by
  rw [concreteVertex_law]
  exact G.vertexAlgorithm_confidence U _ p hp hU (by positivity)
    (G.vertexOracle_amplified U _ (algSEstimator_correct (rejectionAccuracy_bounds _).1
      ((rejectionAccuracy_bounds _).2.trans (by norm_num))) inner)
    heps hδ hn hqueries hbits

theorem vertexAlgorithm_queryBound (p : E → ℝ) (hp : Prob01 p) (n : ℕ) :
    Prog.QueryBound (G.vertexAlgorithm U p hp n) (U.card+2*Fintype.card E*n) := by
  unfold vertexAlgorithm
  split_ifs
  · exact G.vertexCore_queryBound U p hp _ n
  · exact .ret _ _
  · exact .ret _ _

theorem vertexAlgorithm_choiceBound (p : E → ℝ) (hp : Prob01 p) (n : ℕ) :
    Prog.ChoiceBound (G.vertexAlgorithm U p hp n) (n*(U.card+2*Fintype.card E+2)) := by
  unfold vertexAlgorithm
  split_ifs
  · exact G.vertexCore_choiceBound U p hp _ n
  · exact .ret _ _
  · exact .ret _ _

/-- Total fair-bit cost includes all inner reliability runs and outer medians. -/
theorem concreteVertex_bitCost (p : E → ℝ) (hp : Prob01 p) (n b inner outer : ℕ) :
    Prog.BitCost (fun _ : Empty => 0) (G.concreteVertex U p hp n b inner outer)
      (b*(outer*(n*(U.card+2*Fintype.card E+2)))+
        (outer*(U.card+2*Fintype.card E*n))*(inner*
          oracleBitBudget (Fintype.card (Option V)) (Fintype.card E) (rejectionAccuracy (Fintype.card E)))) := by
  have hb := (Prog.discretise_bitBound b (G.vertexAlgorithm_choiceBound U p hp n)).medianOf outer
  have hq := Prog.medianOf_queryBound ((G.vertexAlgorithm_queryBound U p hp n).discretise b) outer
  apply (hb.bitCost hq).inline
  intro x
  exact ((G.splitVertex x.1.val).algSQuery_bitCost (rejectionAccuracy (Fintype.card E))
    (x.2,some x.1.val,none)).medianOf inner

end Digraph
end
end DirectedCycleFPRAS
