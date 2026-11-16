module

public import DirectedCycleFPRAS.AlgorithmSFlags

@[expose] public section

/-! Static snapshot identities for DFS: changing the resolved set, retaining
already discovered vertices, and replacing sufficient fuel bounds. -/
namespace DirectedCycleFPRAS
open Classical
noncomputable section
set_option linter.unusedSectionVars false
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E)

theorem scanTree_mask (ω : E → Bool) (R : Finset V) (v z : V) (flag : Bool)
    (l : List E) (D : Finset V) (st : List (V × Bool)) :
    (G.scanTree (insert v R) z flag l D (maskStack v st)).eval ω =
      let r := (G.scanTree R z flag l D st).eval ω
      (r.1,maskStack v r.2) := by
  induction l generalizing D st with
  | nil => rfl
  | cons e l ih =>
    simp only [scanTree]
    split_ifs
    · simp only [EdgeTree.eval]
      cases ho : ω e with
      | false => exact ih D st
      | true =>
        have hb : (flag && decide (G.target e ∉ insert v R)) =
            ((flag && decide (G.target e ∉ R)) && decide (G.target e ≠ v)) := by
          by_cases hv : G.target e=v <;> by_cases hR : G.target e∈R <;> simp [hv,hR]
        simpa only [maskStack, List.map_cons, hb, ite_true] using
          ih (insert (G.target e) D) ((G.target e,flag && decide (G.target e ∉ R))::st)
    · exact ih D st

theorem scanTree_resolved_congr (ω : E → Bool) (R T : Finset V) (z : V) (flag : Bool)
    (l : List E) (D : Finset V) (st : List (V × Bool))
    (hRT : ∀ y, y ∉ D → (y∈R ↔ y∈T)) :
    (G.scanTree R z flag l D st).eval ω = (G.scanTree T z flag l D st).eval ω := by
  induction l generalizing D st with
  | nil => rfl
  | cons e l ih =>
    simp only [scanTree]
    split_ifs with he
    · simp only [EdgeTree.eval]
      cases ho : ω e with
      | false => exact ih D st hRT
      | true =>
        have hb : decide (G.target e ∉ R) = decide (G.target e ∉ T) := by
          simp only [hRT _ he.2]
        simp only [ite_true, hb]
        apply ih
        intro y hy
        exact hRT y (fun h => hy (Finset.mem_insert_of_mem h))
    · exact ih D st hRT

theorem dfsTree_resolved_congr (ω : E → Bool) (R T : Finset V) (w : V) (fuel : ℕ)
    (D : Finset V) (st : List (V × Bool)) (hRT : ∀ y, y ∉ D → (y∈R ↔ y∈T)) :
    (G.dfsTree R w fuel D st).eval ω = (G.dfsTree T w fuel D st).eval ω := by
  induction fuel generalizing D st with
  | zero => rfl
  | succ fuel ih =>
    cases st with
    | nil => rfl
    | cons a st =>
      obtain ⟨z,flag⟩ := a
      simp only [dfsTree]
      by_cases hz : z=w
      · simp only [hz, ite_true]
      · simp only [hz, ite_false, EdgeTree.eval_bind]
        rw [G.scanTree_resolved_congr ω R T z flag (arcOrder E) D st hRT]
        apply ih
        intro y hy
        exact hRT y (fun h => hy ((G.scanTree_growth ω T z flag (arcOrder E) D st).1 h))

theorem dfsTree_fuel_eq (ω : E → Bool) (R : Finset V) (w : V) (f g : ℕ)
    (D : Finset V) (st : List (V × Bool))
    (hf : Fintype.card V-D.card+st.length < f)
    (hg : Fintype.card V-D.card+st.length < g) :
    (G.dfsTree R w f D st).eval ω = (G.dfsTree R w g D st).eval ω := by
  have h₁ := G.sDfs_fuel_add (fun _ => 0) R (fun e => some (ω e)) w f g D st hf
  have h₂ := G.sDfs_fuel_add (fun _ => 0) R (fun e => some (ω e)) w g f D st hg
  simp only [← G.dfsTree_run, EdgeTree.run_fixed] at h₁ h₂
  rw [Nat.add_comm g f] at h₂
  exact Prog.ret.inj (h₁.trans h₂.symm)

theorem dfsTree_snapshot_growth (ω : E → Bool) (R : Finset V) (w : V) (fuel : ℕ)
    (D : Finset V) (st : List (V × Bool)) :
    ∀ A ∈ (G.dfsTree R w fuel D st).eval ω, D ⊆ A := by
  induction fuel generalizing D st with
  | zero => simp [dfsTree, EdgeTree.eval]
  | succ fuel ih =>
    cases st with
    | nil => simp [dfsTree, EdgeTree.eval]
    | cons a st =>
      obtain ⟨z,flag⟩ := a
      simp only [dfsTree]
      by_cases hz : z=w
      · simp only [hz, ite_true]
        cases flag <;> simp [EdgeTree.eval]
      · simp only [hz, ite_false, EdgeTree.eval_bind]
        intro A hA
        exact (G.scanTree_growth ω R z flag (arcOrder E) D st).1.trans (ih _ _ A hA)

theorem scanTree_avoids_discovered (ω : E → Bool) (R : Finset V) (w z : V) (flag : Bool)
    (l : List E) (D : Finset V) (st : List (V × Bool))
    (hw : w ∈ D) (hs : w ∉ st.map Prod.fst) :
    w ∉ ((G.scanTree R z flag l D st).eval ω).2.map Prod.fst := by
  induction l generalizing D st with
  | nil => exact hs
  | cons e l ih =>
    simp only [scanTree]
    split_ifs with he
    · simp only [EdgeTree.eval]
      cases ho : ω e with
      | false => exact ih D st hw hs
      | true =>
        apply ih _ _ (Finset.mem_insert_of_mem hw)
        simp only [List.map_cons, List.mem_cons, not_or]
        exact ⟨fun h => he.2 (h ▸ hw), hs⟩
    · exact ih D st hw hs

theorem dfsTree_avoids_discovered (ω : E → Bool) (R : Finset V) (w : V) (fuel : ℕ)
    (D : Finset V) (st : List (V × Bool)) (hw : w ∈ D) (hs : w ∉ st.map Prod.fst) :
    (G.dfsTree R w fuel D st).eval ω = none := by
  induction fuel generalizing D st with
  | zero => rfl
  | succ fuel ih =>
    cases st with
    | nil => rfl
    | cons a st =>
      obtain ⟨z,flag⟩ := a
      have hzw : z ≠ w := by intro h; exact hs (by simp [h])
      have hst : w ∉ st.map Prod.fst := fun h => hs (by simp [h])
      simp only [dfsTree, hzw, ite_false, EdgeTree.eval_bind]
      exact ih _ _ ((G.scanTree_growth ω R z flag (arcOrder E) D st).1 hw)
        (G.scanTree_avoids_discovered ω R w z flag (arcOrder E) D st hw hst)

end Digraph
end
end DirectedCycleFPRAS
