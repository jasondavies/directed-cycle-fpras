module

public import DirectedCycleFPRAS.AlgorithmSSnapshot
public import DirectedCycleFPRAS.AlgorithmSReach

@[expose] public section

/-! Last-resolved-vertex decomposition on a fixed retained graph. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [ArcEnumeration E] [DecidableEq E]
variable (G : Digraph V E)

theorem maskStack_eq_self (v : V) (st : List (V × Bool)) (hv : v ∉ st.map Prod.fst) :
    maskStack v st = st := by
  unfold maskStack
  conv_rhs => rw [← List.map_id st]
  apply List.map_congr_left
  intro a ha
  have hne : a.1 ≠ v := fun h => hv (List.mem_map.mpr ⟨a,ha,h⟩)
  simp [hne]

/-- Resolving v removes exactly the target score attributable to descendants
of the recorded v-snapshot. All three traversals use the same retained graph. -/
theorem dfsTree_split (ω : E → Bool) (R : Finset V) (v w : V) (fuel : ℕ)
    (S : Finset E) (D : Finset V) (st : List (V × Bool)) (hr : G.DFSReady S D st)
    (hf : Fintype.card V-D.card+st.length < fuel) :
    recordScore ((G.dfsTree R w fuel D st).eval ω) =
      recordScore ((G.dfsTree (insert v R) w fuel D (maskStack v st)).eval ω) +
      ((G.dfsTree R v fuel D st).eval ω).elim 0 (fun A =>
        recordScore ((G.dfsTree (insert v R) w (Fintype.card V+1) A [(v,true)]).eval ω)) := by
  induction fuel generalizing S D st with
  | zero => omega
  | succ fuel ih =>
    cases st with
    | nil => simp [dfsTree, EdgeTree.eval, maskStack, recordScore]
    | cons zf st =>
      obtain ⟨z,flag⟩ := zf
      have hzD : z ∈ D := hr.discovered (z,flag) (by simp)
      by_cases hzv : z=v
      · subst z
        have hvst : v ∉ st.map Prod.fst := (List.nodup_cons.mp hr.distinct).1
        have hmask : maskStack v ((v,flag)::st) = (v,false)::st := by
          simp only [maskStack, List.map_cons, ne_self_iff_false, decide_false, Bool.and_false]
          rw [show st.map (fun a => (a.1,a.2 && decide (a.1 ≠ v))) = st from maskStack_eq_self v st hvst]
        have hRT : ∀ y, y ∉ D → (y∈R ↔ y∈insert v R) := by
          intro y hy
          have hyv : y ≠ v := fun h => hy (h ▸ hzD)
          simp [hyv]
        conv_lhs => rw [G.dfsTree_resolved_congr ω R (insert v R) w (fuel+1) D ((v,flag)::st) hRT]
        rw [hmask, G.dfsTree_score_head]
        have hDpos : 0 < D.card := Finset.card_pos.mpr ⟨v,hzD⟩
        have hDf := Finset.card_le_univ D
        have hsmall : Fintype.card V-D.card+[(v,true)].length < fuel+1 := by
          simp only [List.length_cons, List.length_nil] at hf ⊢
          omega
        have hlarge : Fintype.card V-D.card+[(v,true)].length < Fintype.card V+1 := by
          simp only [List.length_cons, List.length_nil]
          omega
        rw [G.dfsTree_fuel_eq ω (insert v R) w (fuel+1) (Fintype.card V+1) D [(v,true)] hsmall hlarge]
        have hhit : (G.dfsTree R v (fuel+1) D ((v,flag)::st)).eval ω =
            if flag then some D else none := by simp [dfsTree, EdgeTree.eval]
        rw [hhit]
        cases flag <;> simp [flagValue]
      · have hmask : maskStack v ((z,flag)::st) = (z,flag)::maskStack v st := by simp [maskStack,hzv]
        rw [hmask]
        by_cases hzw : z=w
        · subst z
          have hzero : ((G.dfsTree R v (fuel+1) D ((w,flag)::st)).eval ω).elim 0 (fun A =>
              recordScore ((G.dfsTree (insert v R) w (Fintype.card V+1) A [(v,true)]).eval ω)) = 0 := by
            cases ho : (G.dfsTree R v (fuel+1) D ((w,flag)::st)).eval ω with
            | none => rfl
            | some A =>
              have hDA := G.dfsTree_snapshot_growth ω R v (fuel+1) D ((w,flag)::st) A (by rw [ho]; simp)
              have he := G.dfsTree_avoids_discovered ω (insert v R) w (Fintype.card V+1) A [(v,true)]
                (hDA hzD) (by simpa using hzv)
              simp [he,recordScore]
          rw [hzero,add_zero]
          simp only [dfsTree, ite_true, EdgeTree.eval]
        · simp only [dfsTree, hzv, hzw, ite_false, EdgeTree.eval_bind]
          rw [G.scanTree_mask]
          have hzs : ∀ a ∈ st, z ≠ a.1 := by
            intro a ha hza
            exact (List.nodup_cons.mp hr.distinct).1 (List.mem_map.mpr ⟨a,ha,hza.symm⟩)
          obtain ⟨S',hr'⟩ := (G.scanTree_once R z flag (arcOrder E) (arcOrder_nodup E) S D st
            (DFSReady.pop G hr) hzD hzs
            (fun e _ he hmem => hr.used_off_stack e hmem (z,flag) (by simp) he)).eval_post ω
          apply ih S' _ _ hr'
          have hb := G.scanTree_balance ω R z flag (arcOrder E) D st
          have hc := Finset.card_le_univ D
          have hc' := Finset.card_le_univ ((G.scanTree R z flag (arcOrder E) D st).eval ω).1
          simp only [List.length_cons] at hf
          omega

/-- Averaging the deterministic splitting identity, using deferred decisions
and snapshot regeneration, gives the DFS expectation identity. -/
theorem reachScore_split_dfs (p : E → ℝ) (hp : Prob01 p) (R A : Finset V)
    (x v w : V) (hx : x ∈ A) (hxv : x ≠ v) :
    G.reachScore p R A x w = G.reachScore p (insert v R) A x w +
      (G.sDfs (Q := Empty) p R (fun _ => none) v (Fintype.card V+1) A [(x,true)]).exp noOracle
        (fun o => o.elim 0 (fun D => G.reachScore p (insert v R) D v w)) := by
  have hA : 0 < A.card := Finset.card_pos.mpr ⟨x,hx⟩
  have hAc := Finset.card_le_univ A
  have hf : Fintype.card V-A.card+[(x,true)].length < Fintype.card V+1 := by
    simp only [List.length_cons, List.length_nil]
    omega
  have hm : maskStack v [(x,true)] = [(x,true)] := by simp [maskStack,hxv]
  have hsplit (ω : E → Bool) := G.dfsTree_split ω R v w (Fintype.card V+1) ∅ A [(x,true)]
    (G.dfsReady_initial A x hx) hf
  simp only [hm] at hsplit
  unfold reachScore
  rw [G.sDfs_deferred p hp (fun _ => none) R A x w hx,
    G.sDfs_deferred p hp (fun _ => none) (insert v R) A x w hx]
  have hr := G.sDfs_restart_deferred p hp R (insert v R) A x v w hx
    (Fintype.card V+1) (Fintype.card V+1) (recordScore (V := V))
  change (G.sDfs p R (fun _ => none) v (Fintype.card V+1) A [(x,true)]).exp noOracle
    (fun o => o.elim 0 (fun D => (G.sDfs p (insert v R) (fun _ => none) w
      (Fintype.card V+1) D [(v,true)]).exp noOracle (fun o => o.elim 0 (fun _ => 1)))) = _ at hr
  rw [hr, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  rw [show forceProb p (fun _ => none) = p from funext (fun _ => rfl)]
  have he (o : Option (Finset V)) : recordScore (o.elim none (fun D =>
      (G.dfsTree (insert v R) w (Fintype.card V+1) D [(v,true)]).eval ω)) =
      o.elim 0 (fun D => recordScore ((G.dfsTree (insert v R) w
        (Fintype.card V+1) D [(v,true)]).eval ω)) := by cases o <;> rfl
  rw [he]
  change edgeWeight p ω * recordScore _ = edgeWeight p ω * recordScore _ + _
  rw [hsplit, mul_add]

end Digraph
end
end DirectedCycleFPRAS
