module

public import DirectedCycleFPRAS.AlgorithmSSearch
public import DirectedCycleFPRAS.AlgorithmSPrediction

@[expose] public section

/-! Graph-theoretic meaning of the concrete DFS reach scores. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [ArcEnumeration E] [DecidableEq E]
variable (G : Digraph V E)

theorem scanTree_reachable (ω : E → Bool) (R : Finset V) (x z : V) (flag : Bool)
    (l : List E) (D : Finset V) (st : List (V × Bool))
    (hz : Relation.ReflTransGen (G.Adj (retained ω)) x z)
    (hst : ∀ a ∈ st, Relation.ReflTransGen (G.Adj (retained ω)) x a.1) :
    ∀ a ∈ ((G.scanTree R z flag l D st).eval ω).2,
      Relation.ReflTransGen (G.Adj (retained ω)) x a.1 := by
  induction l generalizing D st with
  | nil => exact hst
  | cons e l ih =>
    simp only [scanTree]
    split_ifs with he
    · simp only [EdgeTree.eval]
      cases ho : ω e with
      | false => exact ih D st hst
      | true =>
        apply ih
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hz.tail ⟨e,ho,he.1,rfl⟩
        · exact hst a ha
    · exact ih D st hst

theorem dfsTree_reachable (ω : E → Bool) (R : Finset V) (x v : V) (fuel : ℕ)
    (D : Finset V) (st : List (V × Bool))
    (hst : ∀ a ∈ st, Relation.ReflTransGen (G.Adj (retained ω)) x a.1)
    (ho : (G.dfsTree R v fuel D st).eval ω ≠ none) :
    Relation.ReflTransGen (G.Adj (retained ω)) x v := by
  induction fuel generalizing D st with
  | zero => exact False.elim (ho rfl)
  | succ fuel ih =>
    cases st with
    | nil => exact False.elim (ho rfl)
    | cons zf st =>
      obtain ⟨z,flag⟩ := zf
      by_cases hz : z = v
      · subst z; exact hst (v,flag) (by simp)
      · simp only [dfsTree, hz, ite_false, EdgeTree.eval_bind] at ho
        exact ih _ _ (G.scanTree_reachable ω R x z flag (arcOrder E) D st
          (hst (z,flag) (by simp)) (fun a ha => hst a (by simp [ha]))) ho

/-- Every recorded vertex is reachable in the retained graph, even when the
starting discovered set contains other vertices and blocks some paths. -/
theorem reachScore_le_reliability (p : E → ℝ) (hp : Prob01 p) (R A : Finset V)
    (x w : V) (hx : x ∈ A) : G.reachScore p R A x w ≤ G.reliability p x w := by
  unfold reachScore
  rw [G.sDfs_deferred p hp (fun _ => none) R A x w hx]
  unfold reliability eventMass
  apply Finset.sum_le_sum
  intro ω _
  let o := (G.dfsTree R w (Fintype.card V+1) A [(x,true)]).eval ω
  by_cases ho : o = none
  · change edgeWeight p ω * o.elim 0 (fun _ => 1) ≤ _
    rw [ho]
    simp only [Option.elim_none, mul_zero]
    split_ifs
    · exact edgeWeight_nonneg hp ω
    · exact le_rfl
  · have hr := G.dfsTree_reachable ω R x w (Fintype.card V+1) A [(x,true)]
      (by simp [Relation.ReflTransGen.refl]) ho
    rw [ite_eq_left hr]
    change edgeWeight p ω * o.elim 0 (fun _ => 1) ≤ edgeWeight p ω
    cases heo : o with
    | none => exact False.elim (ho heo)
    | some D => simp

/-- The bounded record score in FFG Lemma 11, now for the concrete DFS. -/
theorem reachScore_le_ratio (p : E → ℝ) (hp : Prob01 p) (R A : Finset V)
    (s v w : V) (hv : v ∈ A) (hq : 0 < G.reliability p s v) :
    G.reachScore p R A v w ≤ G.reliability p s w / G.reliability p s v :=
  (G.reachScore_le_reliability p hp R A v w hv).trans (G.reliability_le_ratio p hp s v w hq)

/-- Initial DFS reach probability is exactly two-terminal reliability. -/
theorem reachScore_initial (p : E → ℝ) (hp : Prob01 p) (s t : V) :
    G.reachScore p {s} {s} s t = G.reliability p s t := by
  unfold reachScore
  rw [G.sDfs_deferred p hp (fun _ => none) {s} {s} s t (by simp)]
  unfold reliability eventMass
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hr : Relation.ReflTransGen (G.Adj (retained ω)) s t
  · rw [ite_eq_left hr]
    have ho := G.dfsTree_initial_complete ω s t hr
    cases he : (G.dfsTree {s} t (Fintype.card V+1) {s} [(s,true)]).eval ω with
    | none => exact False.elim (ho he)
    | some A =>
      simp only [Option.elim_some, mul_one]
      rw [show forceProb p (fun _ => none) = p from funext (fun _ => rfl)]
  · rw [ite_eq_right hr]
    have ho : (G.dfsTree {s} t (Fintype.card V+1) {s} [(s,true)]).eval ω = none := by
      by_contra h
      exact hr (G.dfsTree_reachable ω {s} s t _ _ _ (by simp [Relation.ReflTransGen.refl]) h)
    simp [ho]

theorem prediction_initial (p : E → ℝ) (hp : Prob01 p) (s w : V) :
    G.prediction p {s} (fun x => if x=s then 1 else 0)
      (fun x => if x=s then [{s}] else []) w = G.reliability p s w := by
  rw [G.prediction_eq_sum]
  simp [G.reachScore_initial p hp]

end Digraph
end
end DirectedCycleFPRAS
