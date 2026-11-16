module

public import DirectedCycleFPRAS.VertexWitness
public import DirectedCycleFPRAS.RejectionResources

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
namespace Digraph
variable {V E : Type} [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E) (U : Finset V)

abbrev VertexQuery := U × (E → ℝ)

def vertexEvents (v : U) (ω : E → Bool) : Prop := G.VertexWitness (retained ω) v.val

def vertexFeasible (v : U) (q : E → ℝ) : Prop :=
  Relation.ReflTransGen ((G.splitVertex v.val).Adj {e | 0 < q e}) (some v.val) none

theorem vertexFeasible_iff (v : U) (q : E → ℝ) (hq : Prob01 q) :
    G.vertexFeasible U v q ↔ 0 < eventMass q (G.vertexEvents U v) := by
  change G.vertexFeasible U v q ↔ 0 < eventMass q (fun ω => G.VertexWitness (retained ω) v.val)
  rw [G.vertex_weight_reliability]
  exact ((G.splitVertex v.val).reliability_pos_iff hq _ _).symm

/-- Only feasible probability vectors constrain the reliability oracle. -/
def VertexGood (a : ℝ) (x : VertexQuery (E := E) U) (r : ℝ) : Prop :=
  Prob01 x.2 → 0 < eventMass x.2 (G.vertexEvents U x.1) →
    |r-eventMass x.2 (G.vertexEvents U x.1)| ≤ a*eventMass x.2 (G.vertexEvents U x.1)

def vertexExact (x : VertexQuery (E := E) U) : ℝ := eventMass x.2 (G.vertexEvents U x.1)

theorem vertexExact_good {a : ℝ} (ha : 0 ≤ a) (x : VertexQuery (E := E) U) :
    G.VertexGood U a x (G.vertexExact U x) := by
  intro _ hp
  simpa [vertexExact] using mul_nonneg ha hp.le

/-- The nonzero branch, using every vertex in the supplied feedback set. -/
def vertexCore (p : E → ℝ) (hp : Prob01 p) (d : U) (n : ℕ) : Prog (VertexQuery (E := E) U) ℝ :=
  witnessCount (G.vertexEvents U) (fun i q => (i,q)) (G.vertexFeasible U)
    p hp Finset.univ.toList Finset.univ.toList d n

theorem vertexCore_ideal (O : Oracle (VertexQuery (E := E) U)) (p : E → ℝ) (hp : Prob01 p)
    (hU : G.Feedback U {e | 0 < p e}) (d : U)
    (hZ : 0 < eventMass p (fun ω => G.Cyclic (retained ω)))
    (hacc : ∀ x s, G.VertexGood U (rejectionAccuracy (Fintype.card E)) x (O.answer x s))
    {eps : ℝ} (heps : 0 < eps) {n : ℕ} (hn : 64*(U.card : ℝ)/eps^2 ≤ n) :
    (G.vertexCore U p hp d n).exp O
      (fun z => if eps*eventMass p (fun ω => G.Cyclic (retained ω)) <
        |z-eventMass p (fun ω => G.Cyclic (retained ω))| then 1 else 0) ≤ 1/16 := by
  have hz := G.vertex_unionMass U hp hU
  have hideal := witnessCount_ideal O (G.vertexEvents U) (fun i q => (i,q))
    (G.vertexFeasible U) Prob01 (fun _ h => h) (fun _ e b h => prob01_pin h e b)
    (G.vertexFeasible_iff U) p hp Finset.univ.toList (fun i => by simp)
    Finset.univ.toList (fun e => by simp) d
    (fun i q hq hpos s => by simpa using hacc (i,q) s hq hpos)
    (by simpa [vertexEvents] using hz.symm ▸ hZ) heps (by simpa using hn)
  dsimp only at hideal
  change (G.vertexCore U p hp d n).exp O
    (fun z => if eps*(edgeLaw p _ _).toMass.unionMass (G.vertexEvents U) ≤
      |z-(edgeLaw p _ _).toMass.unionMass (G.vertexEvents U)| then 1 else 0) ≤ 1/16 at hideal
  have hz' : (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass.unionMass (G.vertexEvents U) =
      eventMass p (fun ω => G.Cyclic (retained ω)) := hz
  rw [hz'] at hideal
  apply le_trans (Prog.exp_mono O _ _) hideal
  intro z
  split_ifs with h h' h'
  · rfl
  · exact False.elim (h' h.le)
  · norm_num
  · rfl

theorem vertexCore_queryBound (p : E → ℝ) (hp : Prob01 p) (d : U) (n : ℕ) :
    Prog.QueryBound (G.vertexCore U p hp d n) (U.card+2*Fintype.card E*n) := by
  simpa [vertexCore] using witnessCount_queryBound (G.vertexEvents U) (fun i q => (i,q))
    (G.vertexFeasible U) p hp Finset.univ.toList Finset.univ.toList d n

theorem vertexCore_choiceBound (p : E → ℝ) (hp : Prob01 p) (d : U) (n : ℕ) :
    Prog.ChoiceBound (G.vertexCore U p hp d n) (n*(U.card+2*Fintype.card E+2)) := by
  simpa [vertexCore] using witnessCount_choiceBound (G.vertexEvents U) (fun i q => (i,q))
    (G.vertexFeasible U) p hp Finset.univ.toList Finset.univ.toList d n

/-- Finite-bit implementation with fresh imperfect reliability calls. -/
theorem vertexCore_failure (O : Oracle (VertexQuery (E := E) U)) (p : E → ℝ) (hp : Prob01 p)
    (hU : G.Feedback U {e | 0 < p e}) (d : U)
    (hZ : 0 < eventMass p (fun ω => G.Cyclic (retained ω)))
    {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : ∀ x, (∑ s, if G.VertexGood U (rejectionAccuracy (Fintype.card E)) x (O.answer x s)
      then 0 else (O.law x).value s) ≤ γ)
    {eps : ℝ} (heps : 0 < eps) {n : ℕ} (hn : 64*(U.card : ℝ)/eps^2 ≤ n) (b : ℕ) :
    ((G.vertexCore U p hp d n).discretise b).exp O
      (fun z => if eps*eventMass p (fun ω => G.Cyclic (retained ω)) <
        |z-eventMass p (fun ω => G.Cyclic (retained ω))| then 1 else 0) ≤
      1/16+(U.card+2*Fintype.card E*n : ℕ)*γ+
        (n*(U.card+2*Fintype.card E+2) : ℕ)/(2 : ℝ)^b := by
  apply Prog.finiteBit_failure O (G.VertexGood U (rejectionAccuracy (Fintype.card E)))
    (G.vertexExact U) hγ0 hγ _ (G.vertexCore_queryBound U p hp d n)
    (G.vertexCore_choiceBound U p hp d n) b _
    (fun _ => by split_ifs <;> norm_num) (fun _ => by split_ifs <;> norm_num)
  apply G.vertexCore_ideal U _ p hp hU d hZ _ heps hn
  exact (O.repair_good _ _ (G.vertexExact_good U (rejectionAccuracy_bounds _).1.le))

/-- Exact support test precedes all counting queries. -/
def vertexAlgorithm (p : E → ℝ) (hp : Prob01 p) (n : ℕ) : Prog (VertexQuery (E := E) U) ℝ :=
  if G.Cyclic {e | 0 < p e} then
    if h : Nonempty U then G.vertexCore U p hp (Classical.choice h) n else .ret 0
  else .ret 0

theorem vertexAlgorithm_zero (p : E → ℝ) (hp : Prob01 p) (n : ℕ)
    (hz : eventMass p (fun ω => G.Cyclic (retained ω)) = 0) :
    G.vertexAlgorithm U p hp n = .ret 0 := by
  have hn : ¬ G.Cyclic {e | 0 < p e} := by
    intro hc
    have hh := (G.cycleMass_pos_iff p (fun e => (hp e).1) (fun e => (hp e).2)).mpr hc
    change 0 < eventMass p (fun ω => G.Cyclic (retained ω)) at hh
    rw [hz] at hh
    exact (lt_irrefl 0) hh
  simp [vertexAlgorithm, hn]

theorem vertexAlgorithm_failure (O : Oracle (VertexQuery (E := E) U))
    (p : E → ℝ) (hp : Prob01 p) (hU : G.Feedback U {e | 0 < p e})
    {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : ∀ x, (∑ s, if G.VertexGood U (rejectionAccuracy (Fintype.card E)) x (O.answer x s)
      then 0 else (O.law x).value s) ≤ γ)
    {eps : ℝ} (heps : 0 < eps) {n : ℕ} (hn : 64*(U.card : ℝ)/eps^2 ≤ n) (b : ℕ) :
    ((G.vertexAlgorithm U p hp n).discretise b).exp O
      (fun z => if eps*eventMass p (fun ω => G.Cyclic (retained ω)) <
        |z-eventMass p (fun ω => G.Cyclic (retained ω))| then 1 else 0) ≤
      1/16+(U.card+2*Fintype.card E*n : ℕ)*γ+
        (n*(U.card+2*Fintype.card E+2) : ℕ)/(2 : ℝ)^b := by
  by_cases hZ : 0 < eventMass p (fun ω => G.Cyclic (retained ω))
  · have hc := (G.cycleMass_pos_iff p (fun e => (hp e).1) (fun e => (hp e).2)).mp hZ
    obtain ⟨v,hv,_⟩ := (G.feedback_cover U {e | 0 < p e} hU).mp hc
    have hU' : Nonempty U := ⟨⟨v,hv⟩⟩
    simp only [vertexAlgorithm, ite_eq_left hc, dite_eq_left hU']
    exact G.vertexCore_failure U O p hp hU _ hZ hγ0 hγ heps hn b
  · have hz := le_antisymm (not_lt.mp hZ) (eventMass_nonneg hp _)
    rw [G.vertexAlgorithm_zero U p hp n hz]
    simp only [Prog.discretise, Prog.exp, hz, mul_zero, sub_zero, abs_zero, lt_self_iff_false, ite_false]
    positivity

/-- Arbitrary confidence for the finite-bit vertex-witness program. -/
theorem vertexAlgorithm_confidence (O : Oracle (VertexQuery (E := E) U))
    (p : E → ℝ) (hp : Prob01 p) (hU : G.Feedback U {e | 0 < p e})
    {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : ∀ x, (∑ s, if G.VertexGood U (rejectionAccuracy (Fintype.card E)) x (O.answer x s)
      then 0 else (O.law x).value s) ≤ γ)
    {eps δ : ℝ} (heps : 0 < eps) (hδ : 0 < δ) {n b : ℕ}
    (hn : 64*(U.card : ℝ)/eps^2 ≤ n)
    (hqueries : (U.card+2*Fintype.card E*n : ℕ)*γ ≤ 1/16)
    (hbits : (n*(U.card+2*Fintype.card E+2) : ℕ)/(2 : ℝ)^b ≤ 1/16) :
    (((G.vertexAlgorithm U p hp n).discretise b).medianOf (confidenceRuns δ)).exp O
      (fun z => if eps*eventMass p (fun ω => G.Cyclic (retained ω)) <
        |z-eventMass p (fun ω => G.Cyclic (retained ω))| then 1 else 0) ≤ δ := by
  let Z := eventMass p (fun ω => G.Cyclic (retained ω))
  have heq : (fun z : ℝ => if eps*Z < |z-Z| then (1 : ℝ) else 0) =
      (fun z => if |z-Z| ≤ eps*Z then 0 else 1) := by
    funext z; by_cases h : |z-Z| ≤ eps*Z <;> simp [h, not_lt.mpr, lt_of_not_ge]
  change (((G.vertexAlgorithm U p hp n).discretise b).medianOf (confidenceRuns δ)).exp O (fun z => if eps*Z < |z-Z| then 1 else 0) ≤ δ
  rw [heq]
  apply (Prog.medianOf_failure O _ (confidenceRuns δ) ?_ ?_).trans (confidenceRuns_bound hδ)
  · intro a b c ha hc hab hbc
    rcases abs_le.mp ha with ⟨ha₁,ha₂⟩
    rcases abs_le.mp hc with ⟨hc₁,hc₂⟩
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have ht := G.vertexAlgorithm_failure U O p hp hU hγ0 hγ heps hn b
    change ((G.vertexAlgorithm U p hp n).discretise b).exp O (fun z => if eps*Z < |z-Z| then 1 else 0) ≤ _ at ht
    rw [heq] at ht
    linarith

end Digraph
end
end DirectedCycleFPRAS
