module

public import DirectedCycleFPRAS.AlgorithmSDeferred

@[expose] public section

/-! Deterministic DFS on a retained graph: discovered-set growth, completed
scans, and search completeness within the proved fuel bound. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [ArcEnumeration E] [DecidableEq E]
variable (G : Digraph V E)

/-- Old discovered and pending vertices persist through a scan; any newly
discovered vertex is pending at the end of that scan. -/
theorem scanTree_growth (ω : E → Bool) (R : Finset V) (z : V) (flag : Bool)
    (l : List E) (D : Finset V) (st : List (V × Bool)) :
    let r := (G.scanTree R z flag l D st).eval ω
    D ⊆ r.1 ∧ (∀ a ∈ st, a ∈ r.2) ∧
      (∀ y ∈ r.1, y ∈ D ∨ y ∈ r.2.map Prod.fst) := by
  induction l generalizing D st with
  | nil => exact ⟨fun _ h => h, fun _ h => h, fun _ h => Or.inl h⟩
  | cons e l ih =>
    simp only [scanTree]
    split_ifs
    · simp only [EdgeTree.eval]
      cases ho : ω e with
      | false => exact ih D st
      | true =>
        have h := ih (insert (G.target e) D) ((G.target e,flag && decide (G.target e ∉ R))::st)
        refine ⟨fun y hy => h.1 (Finset.mem_insert_of_mem hy),
          fun a ha => h.2.1 a (by simp [ha]), ?_⟩
        intro y hy
        rcases h.2.2 y hy with hy | hy
        · rcases Finset.mem_insert.mp hy with rfl | hy
          · exact Or.inr (List.mem_map.mpr ⟨(G.target e,flag && decide (G.target e ∉ R)), h.2.1 _ (by simp), rfl⟩)
          · exact Or.inl hy
        · exact Or.inr hy
    · exact ih D st

/-- Every retained edge examined by a scan ends in the discovered set. -/
theorem scanTree_scanned (ω : E → Bool) (R : Finset V) (z : V) (flag : Bool)
    (l : List E) (D : Finset V) (st : List (V × Bool)) :
    ∀ e ∈ l, G.source e = z → ω e = true →
      G.target e ∈ ((G.scanTree R z flag l D st).eval ω).1 := by
  induction l generalizing D st with
  | nil => simp
  | cons j l ih =>
    intro e he hez heo
    simp only [scanTree]
    split_ifs with hj
    · simp only [EdgeTree.eval]
      cases ho : ω j with
      | false =>
        have hel : e ∈ l := by rcases List.mem_cons.mp he with rfl | h; simp [ho] at heo; exact h
        exact ih D st e hel hez heo
      | true =>
        rcases List.mem_cons.mp he with rfl | he
        · exact (G.scanTree_growth ω R z flag l (insert (G.target e) D)
            ((G.target e,flag && decide (G.target e ∉ R))::st)).1 (Finset.mem_insert_self _ _)
        · exact ih _ _ e he hez heo
    · rcases List.mem_cons.mp he with rfl | he
      · have ht : G.target e ∈ D := by by_contra h; exact hj ⟨hez,h⟩
        exact (G.scanTree_growth ω R z flag l D st).1 ht
      · exact ih D st e he hez heo

/-- If all resolved vertices are already discovered, true flags remain true:
new vertices cannot be resolved. -/
theorem scanTree_true (ω : E → Bool) (R : Finset V) (z : V)
    (l : List E) (D : Finset V) (st : List (V × Bool))
    (hR : R ⊆ D) (hst : ∀ a ∈ st, a.2 = true) :
    ∀ a ∈ ((G.scanTree R z true l D st).eval ω).2, a.2 = true := by
  induction l generalizing D st with
  | nil => exact hst
  | cons e l ih =>
    simp only [scanTree]
    split_ifs with he
    · simp only [EdgeTree.eval]
      cases ho : ω e with
      | false => exact ih D st hR hst
      | true =>
        have ht : G.target e ∉ R := fun h => he.2 (hR h)
        apply ih _ _ (fun x hx => Finset.mem_insert_of_mem (hR hx))
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · simp [ht]
        · exact hst a ha
    · exact ih D st hR hst

theorem scanTree_balance (ω : E → Bool) (R : Finset V) (z : V) (flag : Bool)
    (l : List E) (D : Finset V) (st : List (V × Bool)) :
    let r := (G.scanTree R z flag l D st).eval ω
    r.1.card+st.length = D.card+r.2.length := by
  have h := G.sScan_balance (fun _ => 0) R (fun e => some (ω e)) z flag l D st
  rw [← G.scanTree_run, EdgeTree.run_fixed] at h
  cases h with | ret _ h => exact h

theorem scanTree_discovered (ω : E → Bool) (R : Finset V) (z : V) (flag : Bool)
    (l : List E) (D : Finset V) (st : List (V × Bool)) (hst : ∀ a ∈ st, a.1 ∈ D) :
    ∀ a ∈ ((G.scanTree R z flag l D st).eval ω).2,
      a.1 ∈ ((G.scanTree R z flag l D st).eval ω).1 := by
  have h := G.sScan_closed (fun _ => 0) Finset.univ R (by simp)
    (fun e => some (ω e)) z (by simp) flag l D st (by simp) hst
  rw [← G.scanTree_run, EdgeTree.run_fixed] at h
  cases h with | ret _ h => exact h.2

/-- If search has not yet popped the target, discovered targets are still
pending and every processed vertex has all retained successors discovered. -/
structure SearchInvariant (ω : E → Bool) (s t : V) (D : Finset V) (st : List (V × Bool)) : Prop where
  source : s ∈ D
  pending : ∀ a ∈ st, a.1 ∈ D ∧ a.2 = true
  target : t ∈ D → t ∈ st.map Prod.fst
  processed : ∀ e, G.source e ∈ D → G.source e ∉ st.map Prod.fst → ω e = true → G.target e ∈ D

theorem SearchInvariant.scan {ω : E → Bool} {s t z : V} {D : Finset V} {st : List (V × Bool)}
    (h : G.SearchInvariant ω s t D ((z,true)::st)) (hzt : z ≠ t) :
    let r := (G.scanTree {s} z true (arcOrder E) D st).eval ω
    G.SearchInvariant ω s t r.1 r.2 := by
  let r := (G.scanTree {s} z true (arcOrder E) D st).eval ω
  have hg := G.scanTree_growth ω {s} z true (arcOrder E) D st
  have hd := G.scanTree_discovered ω {s} z true (arcOrder E) D st
    (fun a ha => (h.pending a (by simp [ha])).1)
  have ht := G.scanTree_true ω {s} z (arcOrder E) D st (by simpa using h.source)
    (fun a ha => (h.pending a (by simp [ha])).2)
  refine ⟨hg.1 h.source, fun a ha => ⟨hd a ha, ht a ha⟩, ?_, ?_⟩
  · intro htarget
    rcases hg.2.2 t htarget with hD | hstack
    · have hst := h.target hD
      simp only [List.map_cons, List.mem_cons] at hst
      rcases hst with htz | hst
      · exact False.elim (hzt htz.symm)
      · obtain ⟨a, ha, hat⟩ := List.mem_map.mp hst
        exact List.mem_map.mpr ⟨a,hg.2.1 a ha,hat⟩
    · exact hstack
  · intro e heD heStack heOpen
    have heOld : G.source e ∈ D := (hg.2.2 _ heD).resolve_right heStack
    by_cases hez : G.source e = z
    · exact G.scanTree_scanned ω {s} z true (arcOrder E) D st e (by simp) hez heOpen
    · apply hg.1
      apply h.processed e heOld _ heOpen
      simp only [List.map_cons, List.mem_cons, not_or]
      refine ⟨hez, ?_⟩
      intro hmem
      obtain ⟨a,ha,heq⟩ := List.mem_map.mp hmem
      exact heStack (List.mem_map.mpr ⟨a,hg.2.1 a ha,heq⟩)

/-- With sufficient fuel, DFS from the search invariant cannot fail to
record a reachable target. -/
theorem dfsTree_complete (ω : E → Bool) (s t : V) (fuel : ℕ) (D : Finset V)
    (st : List (V × Bool)) (h : G.SearchInvariant ω s t D st)
    (hf : Fintype.card V-D.card+st.length < fuel)
    (hr : Relation.ReflTransGen (G.Adj (retained ω)) s t) :
    (G.dfsTree {s} t fuel D st).eval ω ≠ none := by
  induction fuel generalizing D st with
  | zero => omega
  | succ fuel ih =>
    cases st with
    | nil =>
      have hall (u : V) (hu : Relation.ReflTransGen (G.Adj (retained ω)) s u) : u ∈ D := by
        induction hu with
        | refl => exact h.source
        | @tail y z hu he ihu =>
          obtain ⟨e,he,hs,ht⟩ := he
          exact ht ▸ h.processed e (hs ▸ ihu) (by simp) he
      have ht := hall t hr
      exact False.elim (by simpa using h.target ht)
    | cons zf st =>
      obtain ⟨z,flag⟩ := zf
      have hflag : flag = true := (h.pending (z,flag) (by simp)).2
      subst flag
      by_cases hzt : z = t
      · simp [dfsTree, hzt, EdgeTree.eval]
      · simp only [dfsTree, hzt, ite_false, EdgeTree.eval_bind]
        apply ih _ _ (SearchInvariant.scan G h hzt) _
        have hb := G.scanTree_balance ω {s} z true (arcOrder E) D st
        have hc := Finset.card_le_univ D
        have hc' := Finset.card_le_univ ((G.scanTree {s} z true (arcOrder E) D st).eval ω).1
        simp only [List.length_cons] at hf
        omega

theorem dfsTree_initial_complete (ω : E → Bool) (s t : V)
    (hr : Relation.ReflTransGen (G.Adj (retained ω)) s t) :
    (G.dfsTree {s} t (Fintype.card V+1) {s} [(s,true)]).eval ω ≠ none := by
  apply G.dfsTree_complete ω s t _ _ _ _ _ hr
  · refine ⟨by simp, by simp, ?_, ?_⟩
    · simp
    · intro e hs hn
      exact False.elim (hn (by simpa using hs))
  · have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
    simp
    omega

end Digraph
end
end DirectedCycleFPRAS
