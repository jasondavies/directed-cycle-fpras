module

public import DirectedCycleFPRAS.ConcreteVertex
public import DirectedCycleFPRAS.WitnessSampling

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E) (U : Finset V)

/-- Conditional sampler with the entire positive support as its timeout fallback. -/
def vertexSample (p : E → ℝ) (hp : Prob01 p) (d : U) (L : ℕ) : Prog (VertexQuery (E := E) U) (E → Bool) :=
  witnessSample (G.vertexEvents U) (fun i q => (i,q)) (G.vertexFeasible U)
    p hp Finset.univ.toList Finset.univ.toList d (support p) L

/-- The reference sampler's error is bounded uniformly over all test functions. -/
theorem vertexSample_ideal (O : Oracle (VertexQuery (E := E) U)) (p : E → ℝ) (hp : Prob01 p)
    (d : U)
    (hZ : 0 < (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass.unionMass (G.vertexEvents U))
    (hacc : ∀ x s, G.VertexGood U (rejectionAccuracy (Fintype.card E)) x (O.answer x s))
    (r : ℕ) (f : (E → Bool) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    |(G.vertexSample U p hp d (4*U.card*r)).exp O f-
      (unionLaw (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass (G.vertexEvents U) hZ).expectation f|
      ≤ (1/2 : ℝ)^r := by
  simpa [vertexSample] using witnessSample_ideal O (G.vertexEvents U) (fun i q => (i,q))
    (G.vertexFeasible U) Prob01 (fun _ h => h) (fun _ e b h => prob01_pin h e b)
    (G.vertexFeasible_iff U) p hp Finset.univ.toList (fun i => by simp)
    Finset.univ.toList (fun e => by simp) d
    (fun i q hq hpos s => by simpa using hacc (i,q) s hq hpos)
    hZ (support p) r f hf0 hf1

theorem vertexSample_queryBound (p : E → ℝ) (hp : Prob01 p) (d : U) (L : ℕ) :
    Prog.QueryBound (G.vertexSample U p hp d L) (U.card+2*Fintype.card E*L) := by
  simpa [vertexSample] using witnessSample_queryBound (G.vertexEvents U) (fun i q => (i,q))
    (G.vertexFeasible U) p hp Finset.univ.toList Finset.univ.toList d (support p) L

theorem vertexSample_choiceBound (p : E → ℝ) (hp : Prob01 p) (d : U) (L : ℕ) :
    Prog.ChoiceBound (G.vertexSample U p hp d L) (L*(U.card+2*Fintype.card E+2)) := by
  simpa [vertexSample] using witnessSample_choiceBound (G.vertexEvents U) (fun i q => (i,q))
    (G.vertexFeasible U) p hp Finset.univ.toList Finset.univ.toList d (support p) L

/-- Sampling after oracle repair and finite-bit rounding. Taking `f` to be an
event indicator gives the total-variation guarantee. -/
theorem vertexSample_error (O : Oracle (VertexQuery (E := E) U)) (p : E → ℝ) (hp : Prob01 p)
    (d : U)
    (hZ : 0 < (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass.unionMass (G.vertexEvents U))
    {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : ∀ x, (∑ s, if G.VertexGood U (rejectionAccuracy (Fintype.card E)) x (O.answer x s)
      then 0 else (O.law x).value s) ≤ γ)
    (r b : ℕ) (f : (E → Bool) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    |((G.vertexSample U p hp d (4*U.card*r)).discretise b).exp O f-
      (unionLaw (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass (G.vertexEvents U) hZ).expectation f| ≤
      (1/2 : ℝ)^r+(U.card+2*Fintype.card E*(4*U.card*r) : ℕ)*γ+
        ((4*U.card*r)*(U.card+2*Fintype.card E+2) : ℕ)/(2 : ℝ)^b := by
  apply Prog.finiteBit_error O (G.VertexGood U (rejectionAccuracy (Fintype.card E)))
    (G.vertexExact U) hγ0 hγ _ (G.vertexSample_queryBound U p hp d _)
    (G.vertexSample_choiceBound U p hp d _) b f hf0 hf1
  exact G.vertexSample_ideal U _ p hp d hZ
    (O.repair_good _ _ (G.vertexExact_good U (rejectionAccuracy_bounds _).1.le)) r f hf0 hf1

/-- A call-free conditional sampler using the same Algorithm S oracle. -/
def concreteVertexSample (p : E → ℝ) (hp : Prob01 p) (d : U) (L b inner : ℕ) : Prog Empty (E → Bool) :=
  ((G.vertexSample U p hp d L).discretise b).inline
    (fun x => (G.vertexAlgSQuery U (rejectionAccuracy (Fintype.card E)) x).medianOf inner)

theorem concreteVertexSample_error (p : E → ℝ) (hp : Prob01 p) (d : U)
    (hZ : 0 < (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass.unionMass (G.vertexEvents U))
    (r b inner : ℕ) (f : (E → Bool) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    |(G.concreteVertexSample U p hp d (4*U.card*r) b inner).exp noOracle f-
      (unionLaw (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass (G.vertexEvents U) hZ).expectation f| ≤
      (1/2 : ℝ)^r+(U.card+2*Fintype.card E*(4*U.card*r) : ℕ)*(7/8 : ℝ)^inner+
        ((4*U.card*r)*(U.card+2*Fintype.card E+2) : ℕ)/(2 : ℝ)^b := by
  unfold concreteVertexSample
  rw [Prog.exp_inline_amplify]
  exact G.vertexSample_error U _ p hp d hZ (by positivity)
    (G.vertexOracle_amplified U _ (algSEstimator_correct (rejectionAccuracy_bounds _).1
      ((rejectionAccuracy_bounds _).2.trans (by norm_num))) inner) r b f hf0 hf1

theorem concreteVertexSample_bitCost (p : E → ℝ) (hp : Prob01 p) (d : U) (L b inner : ℕ) :
    Prog.BitCost (fun _ : Empty => 0) (G.concreteVertexSample U p hp d L b inner)
      (b*(L*(U.card+2*Fintype.card E+2))+(U.card+2*Fintype.card E*L)*
        (inner*oracleBitBudget (Fintype.card (Option V)) (Fintype.card E) (rejectionAccuracy (Fintype.card E)))) := by
  have hb := Prog.discretise_bitBound b (G.vertexSample_choiceBound U p hp d L)
  have hq := (G.vertexSample_queryBound U p hp d L).discretise b
  apply (hb.bitCost hq).inline
  intro x
  exact ((G.splitVertex x.1.val).algSQuery_bitCost (rejectionAccuracy (Fintype.card E))
    (x.2,some x.1.val,none)).medianOf inner

/-- Under a feedback cover, the target law is exactly conditioning on cyclicity. -/
theorem vertex_conditional_expectation (p : E → ℝ) (hp : Prob01 p)
    (hU : G.Feedback U {e | 0 < p e})
    (hZ : 0 < (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass.unionMass (G.vertexEvents U))
    (f : (E → Bool) → ℝ) :
    (unionLaw (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass (G.vertexEvents U) hZ).expectation f =
      (∑ ω, if G.Cyclic (retained ω) then edgeWeight p ω*f ω else 0)/
        eventMass p (fun ω => G.Cyclic (retained ω)) := by
  change (∑ ω, ((if 0 < Mass.multiplicity (G.vertexEvents U) ω then edgeWeight p ω else 0)/
    (edgeLaw p _ _).toMass.unionMass (G.vertexEvents U))*f ω) = _
  have hz := G.vertex_unionMass U hp hU
  change (edgeLaw p _ _).toMass.unionMass (G.vertexEvents U) = _ at hz
  rw [hz, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : 0 < edgeWeight p ω
  · have he := (Mass.multiplicity_pos_iff (A := G.vertexEvents U) ω).trans
      (G.feedback_cover_supported U hp hU hω).symm
    by_cases hc : G.Cyclic (retained ω)
    · rw [ite_eq_left (he.mpr hc), ite_eq_left hc]; ring
    · rw [ite_eq_right (fun h => hc (he.mp h)), ite_eq_right hc]; simp
  · have hz : edgeWeight p ω = 0 := le_antisymm (not_lt.mp hω) (edgeWeight_nonneg hp ω)
    simp [hz]

end Digraph
end
end DirectedCycleFPRAS
