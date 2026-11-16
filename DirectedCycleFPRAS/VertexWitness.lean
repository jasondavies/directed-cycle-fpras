module

public import DirectedCycleFPRAS.Reliability

@[expose] public section
namespace DirectedCycleFPRAS
open Classical
noncomputable section
set_option linter.unusedSectionVars false
namespace Digraph
variable {V E : Type} [DecidableEq V] (G : Digraph V E)

/-- A vertex belongs to a nonempty closed directed walk. -/
def VertexWitness (S : Set E) (v : V) : Prop := Relation.TransGen (G.Adj S) v v

/-- Split v into an outgoing terminal `some v` and incoming terminal `none`.
Every edge keeps its identity and its original random bit. -/
def splitVertex (v : V) : Digraph (Option V) E where
  source e := some (G.source e)
  target e := if G.target e = v then none else some (G.target e)

def splitProject (v : V) : Option V → V := fun x => x.getD v

theorem split_adj_project (v : V) (S : Set E) {a b : Option V}
    (h : (G.splitVertex v).Adj S a b) :
    G.Adj S (splitProject v a) (splitProject v b) := by
  obtain ⟨e, he, rfl, rfl⟩ := h
  refine ⟨e, he, rfl, ?_⟩
  simp only [splitVertex, splitProject]
  split_ifs with h <;> simp_all

theorem split_return (v : V) (S : Set E) {x : V}
    (h : Relation.ReflTransGen (G.Adj S) x v) :
    Relation.ReflTransGen ((G.splitVertex v).Adj S)
      (if x = v then none else some x) none := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => simp only [ite_true]; exact .refl
  | @head a c hac _ ih =>
    by_cases ha : a = v
    · simp only [ha, ite_true]; exact .refl
    · obtain ⟨e, he, hs, ht⟩ := hac
      rw [ite_eq_right ha]
      apply ih.head
      exact ⟨e, he, by simp [splitVertex, hs], by simp [splitVertex, ht]⟩

/-- Vertex cycle membership is exactly reliability between the split terminals. -/
theorem vertexWitness_iff_split (v : V) (S : Set E) :
    G.VertexWitness S v ↔ Relation.ReflTransGen ((G.splitVertex v).Adj S) (some v) none := by
  constructor
  · intro h
    obtain ⟨x, ⟨e, he, hs, ht⟩, hr⟩ := Relation.TransGen.head'_iff.mp h
    exact (G.split_return v S hr).head
      ⟨e, he, by simp [splitVertex, hs], by simp [splitVertex, ht]⟩
  · intro h
    have hn : some v ≠ (none : Option V) := by simp
    have ht := (Relation.reflTransGen_iff_eq_or_transGen.mp h).resolve_left (Ne.symm hn)
    have hm : Relation.TransGen (G.Adj S) (splitProject v (some v)) (splitProject v none) := by
      exact ht.lift (splitProject v) (fun _ _ h => G.split_adj_project v S h)
    exact hm

/-- A supplied feedback set is checked by acyclicity after deleting its vertices. -/
def Feedback (U : Finset V) (S : Set E) : Prop :=
  ¬ G.Cyclic {e | e ∈ S ∧ G.source e ∉ U ∧ G.target e ∉ U}

theorem cyclic_iff_vertex (S : Set E) : G.Cyclic S ↔ ∃ v, G.VertexWitness S v := Iff.rfl

theorem feedback_cover (U : Finset V) (S : Set E) (hU : G.Feedback U S) :
    G.Cyclic S ↔ ∃ v ∈ U, G.VertexWitness S v := by
  constructor
  · intro hc
    by_contra hn
    have hnot : ∀ v ∈ U, ¬ G.VertexWitness S v := by simpa using hn
    have restrict : ∀ {a b : V}, Relation.ReflTransGen (G.Adj S) a b →
        Relation.ReflTransGen (G.Adj S) b a →
        Relation.ReflTransGen (G.Adj {e | e ∈ S ∧ G.source e ∉ U ∧ G.target e ∉ U}) a b := by
      intro a b h
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => intro _; exact .refl
      | @head a c hac hcb ih =>
        intro hba
        have ha : a ∉ U := fun ha => hnot a ha (.head' hac (hcb.trans hba))
        have hc : c ∉ U := fun hc => hnot c hc (Relation.TransGen.tail' (hcb.trans hba) hac)
        obtain ⟨e, he, hs, ht⟩ := hac
        exact (ih (hba.tail ⟨e, he, hs, ht⟩)).head
          ⟨e, ⟨he, hs ▸ ha, ht ▸ hc⟩, hs, ht⟩
    obtain ⟨v, h⟩ := hc
    obtain ⟨x, ⟨e, he, hs, ht⟩, hr⟩ := Relation.TransGen.head'_iff.mp h
    have hv : v ∉ U := fun hv => hnot v hv h
    have hx : x ∉ U := fun hx => hnot x hx (Relation.TransGen.tail' hr ⟨e, he, hs, ht⟩)
    apply hU
    refine ⟨v, .head' ⟨e, ⟨he, hs ▸ hv, ht ▸ hx⟩, hs, ht⟩ ?_⟩
    exact restrict hr (.single ⟨e, he, hs, ht⟩)
  · rintro ⟨v, _, hv⟩
    exact ⟨v, hv⟩

variable [Fintype E] [DecidableEq E]

/-- The query identity, for every residual probability vector as well. -/
theorem vertex_weight_reliability (p : E → ℝ) (v : V) :
    eventMass p (fun ω => G.VertexWitness (retained ω) v) =
      (G.splitVertex v).reliability p (some v) none := by
  simp only [reliability, eventMass]
  simp_rw [G.vertexWitness_iff_split]

/-- Positive product mass forces every retained edge into the positive support. -/
theorem retained_subset_support {p : E → ℝ} (hp : Prob01 p) {ω : E → Bool}
    (hω : 0 < edgeWeight p ω) : retained ω ⊆ {e | 0 < p e} := by
  intro e he
  have hn := Finset.prod_ne_zero_iff.mp (ne_of_gt hω) e (Finset.mem_univ e)
  change (if ω e then p e else 1-p e) ≠ 0 at hn
  change ω e = true at he
  simp only [he, ite_true] at hn
  exact lt_of_le_of_ne (hp e).1 (Ne.symm hn)

/-- A feedback set for the input support covers every positive-mass outcome. -/
theorem feedback_cover_supported (U : Finset V) {p : E → ℝ} (hp : Prob01 p)
    (hU : G.Feedback U {e | 0 < p e}) {ω : E → Bool} (hω : 0 < edgeWeight p ω) :
    G.Cyclic (retained ω) ↔ ∃ v : U, G.VertexWitness (retained ω) v.val := by
  have hsub := retained_subset_support hp hω
  have hf : G.Feedback U (retained ω) := by
    rintro ⟨v, hv⟩
    apply hU
    exact ⟨v, Relation.TransGen.mono
      (fun _ _ ⟨e, he, hs, ht⟩ => ⟨e, ⟨hsub he.1, he.2⟩, hs, ht⟩) _ _ hv⟩
  rw [G.feedback_cover U (retained ω) hf]
  exact ⟨fun ⟨v,hv,h⟩ => ⟨⟨v,hv⟩,h⟩, fun ⟨v,h⟩ => ⟨v.val,v.property,h⟩⟩

/-- The vertex cover has exactly the desired cyclicity probability, including
outcomes with zero product mass. -/
theorem vertex_unionMass (U : Finset V) {p : E → ℝ} (hp : Prob01 p)
    (hU : G.Feedback U {e | 0 < p e}) :
    (edgeLaw p (fun e => (hp e).1) (fun e => (hp e).2)).toMass.unionMass
      (fun v : U => fun ω => G.VertexWitness (retained ω) v.val) =
    eventMass p (fun ω => G.Cyclic (retained ω)) := by
  unfold Mass.unionMass eventMass
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : 0 < edgeWeight p ω
  · have he := G.feedback_cover_supported U hp hU hω
    have hi := (Mass.multiplicity_pos_iff (A := fun v : U => fun ω => G.VertexWitness (retained ω) v.val) ω).trans he.symm
    by_cases hc : G.Cyclic (retained ω)
    · rw [ite_eq_left (hi.mpr hc), ite_eq_left hc]; rfl
    · rw [ite_eq_right (fun h => hc (hi.mp h)), ite_eq_right hc]
  · have hz : edgeWeight p ω = 0 := le_antisymm (not_lt.mp hω) (edgeWeight_nonneg hp ω)
    simp [edgeLaw_value, hz]

end Digraph
end
end DirectedCycleFPRAS
