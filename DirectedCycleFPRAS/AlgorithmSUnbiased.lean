module

public import DirectedCycleFPRAS.AlgorithmSSplit

@[expose] public section

/-! FFG equation (8) and Lemma 10 for the concrete DFS and Generate program. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E)

theorem scanTree_no_cut (ω : E → Bool) (R : Finset V) (x : V) (flag : Bool)
    (l : List E) (D : Finset V) (st : List (V × Bool))
    (hc : ∀ e ∈ l, G.source e=x → ω e=true → G.target e∈R)
    (hs : ∀ a ∈ st, a.2=false) :
    ∀ a ∈ ((G.scanTree R x flag l D st).eval ω).2, a.2=false := by
  induction l generalizing D st with
  | nil => exact hs
  | cons e l ih =>
    have hct : ∀ j ∈ l, G.source j=x → ω j=true → G.target j∈R := fun j hj => hc j (by simp [hj])
    simp only [scanTree]
    split_ifs with he
    · simp only [EdgeTree.eval]
      cases ho : ω e with
      | false => exact ih D st hct hs
      | true =>
        apply ih _ _ hct
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · simp [hc e (by simp) he.1 ho]
        · exact hs a ha
    · exact ih D st hct hs

/-- Reaching an unresolved vertex with a true path flag requires an open
outgoing cut edge at the starting vertex. -/
theorem dfsTree_no_cut (ω : E → Bool) (R A : Finset V) (x v : V) (hxv : x ≠ v)
    (fuel : ℕ) (hc : ¬∃ e, G.cutAt R x e ∧ ω e=true) :
    (G.dfsTree R v fuel A [(x,true)]).eval ω = none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    simp only [dfsTree, hxv, ite_false, EdgeTree.eval_bind]
    apply G.dfsTree_false
    apply G.scanTree_no_cut _ _ _ _ _ _ _ _ (by simp)
    intro e _ he ho
    by_contra hn
    exact hc ⟨e,⟨he,hn⟩,ho⟩

/-- First-open conditioning cancels exactly for every DFS record score.
The event of a valid record already entails the conditioning event. -/
theorem recordWeight_eq_dfs (p : E → ℝ) (hp : Prob01 p) (R A : Finset V)
    (x v : V) (hx : x ∈ A) (hxv : x ≠ v) (f : Finset V → ℝ) :
    G.recordWeight p R x v A f =
      (G.sDfs (Q := Empty) p R (fun _ => none) v (Fintype.card V+1) A [(x,true)]).exp noOracle
        (fun o => o.elim 0 f) := by
  unfold recordWeight
  simp_rw [G.sDfs_deferred p hp _ R A x v hx]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, G.firstOpen_mixture]
  rw [show forceProb p (fun _ => none) = p from funext (fun _ => rfl)]
  by_cases hc : ∃ e, G.cutAt R x e ∧ ω e=true
  · simp [hc]
  · rw [ite_eq_right hc, G.dfsTree_no_cut ω R A x v hxv _ hc]
    simp

/-- The last-resolved-vertex splitting identity, FFG equation (8), with the
actual first-open proposal kernel and the concrete restart score. -/
theorem reachScore_split (p : E → ℝ) (hp : Prob01 p) (R A : Finset V)
    (x v w : V) (hx : x ∈ A) (hxv : x ≠ v) :
    G.reachScore p R A x w = G.reachScore p (insert v R) A x w +
      G.recordWeight p R x v A (fun D => G.reachScore p (insert v R) D v w) := by
  rw [G.recordWeight_eq_dfs p hp R A x v hx hxv]
  exact G.reachScore_split_dfs p hp R A x v w hx hxv

/-- FFG Lemma 10 for a concrete continuing round. The splitting identity is
proved, not a hypothesis of this theorem. -/
theorem prediction_generate_unbiased (p : E → ℝ) (hp : Prob01 p) (R : Finset V)
    (qh : V → ℝ) (pools : V → List (Finset V)) (v w : V) (hv : v ∉ R)
    {M : ℕ} (hM : 0 < M) (hpool : PoolInvariant R qh pools M) :
    (G.sGenerate p R qh pools M v M).exp noOracle
      (fun r => G.prediction p (insert v R)
        (Function.update qh v (G.phiS p R qh*r.1/M)) (Function.update pools v r.2) w) =
      G.prediction p R qh pools w := by
  apply G.prediction_generate_unbiased_of_split p hp R qh pools v w hv hM hpool
  intro x hx A hA
  exact G.reachScore_split p hp R A x v w (hpool.contains x hx A hA)
    (fun h => hv (h ▸ hx))

end Digraph
end
end DirectedCycleFPRAS
