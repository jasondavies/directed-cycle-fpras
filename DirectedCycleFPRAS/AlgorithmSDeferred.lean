module

public import DirectedCycleFPRAS.DeferredEdges
public import DirectedCycleFPRAS.AlgorithmSInvariants

@[expose] public section

/-! Algorithm S's DFS reads each edge at most once. Its exact output law is
therefore the DFS output on one product-distributed retained graph. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [ArcEnumeration E] [DecidableEq E]
variable (G : Digraph V E)

def scanTree (R : Finset V) (z : V) (flag : Bool) :
    List E → Finset V → List (V × Bool) → EdgeTree E (Finset V × List (V × Bool))
  | [], D, st => .ret (D,st)
  | e::l, D, st =>
    if G.source e = z ∧ G.target e ∉ D then
      .read e fun b => if b then
        scanTree R z flag l (insert (G.target e) D) ((G.target e, flag && decide (G.target e ∉ R))::st)
        else scanTree R z flag l D st
    else scanTree R z flag l D st

def dfsTree (R : Finset V) (v : V) : ℕ → Finset V → List (V × Bool) → EdgeTree E (Option (Finset V))
  | 0, _, _ => .ret none
  | _+1, _, [] => .ret none
  | f+1, D, (z,flag)::st =>
    if z=v then .ret (if flag then some D else none)
    else (G.scanTree R z flag (arcOrder E) D st).bind fun r => dfsTree R v f r.1 r.2

theorem scanTree_run (p : E → ℝ) (pre : E → Option Bool) (R : Finset V) (z : V)
    (flag : Bool) (l : List E) (D : Finset V) (st : List (V × Bool)) :
    (G.scanTree R z flag l D st).run p pre = G.sScan (Q := Empty) p R pre z flag l D st := by
  induction l generalizing D st with
  | nil => rfl
  | cons e l ih =>
    simp only [scanTree, sScan]
    split_ifs
    · simp only [EdgeTree.run]
      congr 1
      funext b
      cases b <;> simp [ih]
    · exact ih D st

theorem dfsTree_run (p : E → ℝ) (pre : E → Option Bool) (R : Finset V) (v : V)
    (fuel : ℕ) (D : Finset V) (st : List (V × Bool)) :
    (G.dfsTree R v fuel D st).run p pre = G.sDfs (Q := Empty) p R pre v fuel D st := by
  induction fuel generalizing D st with
  | zero => rfl
  | succ fuel ih =>
    cases st with
    | nil => rfl
    | cons zf st =>
      obtain ⟨z,flag⟩ := zf
      simp only [dfsTree, sDfs]
      by_cases h : z = v
      · simp only [h, ite_true]; rfl
      · simp only [h, ite_false]
        rw [EdgeTree.run_bind, G.scanTree_run]
        congr 1
        funext r
        exact ih r.1 r.2

/-- Previously read edges leave discovered vertices which are no longer
pending. Pending vertices are distinct and already discovered. -/
structure DFSReady (S : Finset E) (D : Finset V) (st : List (V × Bool)) : Prop where
  used_discovered : ∀ e ∈ S, G.source e ∈ D
  used_off_stack : ∀ e ∈ S, ∀ a ∈ st, G.source e ≠ a.1
  distinct : (st.map Prod.fst).Nodup
  discovered : ∀ a ∈ st, a.1 ∈ D

theorem DFSReady.pop {S : Finset E} {D : Finset V} {z : V} {b : Bool} {st : List (V × Bool)}
    (h : G.DFSReady S D ((z,b)::st)) : G.DFSReady S D st := by
  refine ⟨h.used_discovered, ?_, ?_, ?_⟩
  · intro e he a ha; exact h.used_off_stack e he a (by simp [ha])
  · exact (List.nodup_cons.mp h.distinct).2
  · intro a ha; exact h.discovered a (by simp [ha])

theorem DFSReady.record {S : Finset E} {D : Finset V} {st : List (V × Bool)}
    (h : G.DFSReady S D st) (e : E) (he : G.source e ∈ D)
    (hs : ∀ a ∈ st, G.source e ≠ a.1) : G.DFSReady (insert e S) D st := by
  refine ⟨?_, ?_, h.distinct, h.discovered⟩
  · intro j hj; rcases Finset.mem_insert.mp hj with rfl | hj
    · exact he
    · exact h.used_discovered j hj
  · intro j hj a ha; rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hs a ha
    · exact h.used_off_stack j hj a ha

theorem DFSReady.discover {S : Finset E} {D : Finset V} {st : List (V × Bool)}
    (h : G.DFSReady S D st) (y : V) (hy : y ∉ D) (b : Bool) :
    G.DFSReady S (insert y D) ((y,b)::st) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he; exact Finset.mem_insert_of_mem (h.used_discovered e he)
  · intro e he a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · intro heq
      change G.source e = y at heq
      exact hy (heq ▸ h.used_discovered e he)
    · exact h.used_off_stack e he a ha
  · simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, h.distinct⟩
    intro hmem
    obtain ⟨a, ha, hay⟩ := List.mem_map.mp hmem
    exact hy (hay ▸ h.discovered a ha)
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (h.discovered a ha)

/-- A scan preserves read-once freshness for the continuing DFS. -/
theorem scanTree_once (R : Finset V) (z : V) (flag : Bool) (l : List E)
    (hl : l.Nodup) (S : Finset E) (D : Finset V) (st : List (V × Bool))
    (hr : G.DFSReady S D st) (hz : z ∈ D) (hzs : ∀ a ∈ st, z ≠ a.1)
    (hf : ∀ e ∈ l, G.source e = z → e ∉ S) :
    EdgeTree.Once (fun S r => G.DFSReady S r.1 r.2) S (G.scanTree R z flag l D st) := by
  induction l generalizing S D st with
  | nil => exact .ret S _ hr
  | cons e l ih =>
    have hnd := List.nodup_cons.mp hl
    have ht : ∀ j ∈ l, G.source j = z → j ∉ S := fun j hj => hf j (by simp [hj])
    simp only [scanTree]
    split_ifs with he
    · refine .read S e _ (hf e (by simp) he.1) ?_
      intro b
      have hr' := DFSReady.record G hr e (he.1 ▸ hz) (fun a ha => he.1 ▸ hzs a ha)
      have ht' : ∀ j ∈ l, G.source j = z → j ∉ insert e S := by
        intro j hj hjz hmem
        rcases Finset.mem_insert.mp hmem with rfl | hmem
        · exact hnd.1 hj
        · exact ht j hj hjz hmem
      cases b with
      | false => exact ih hnd.2 (insert e S) D st hr' hz hzs ht'
      | true =>
        apply ih hnd.2 (insert e S) _ _ (DFSReady.discover G hr' _ he.2 _) (Finset.mem_insert_of_mem hz) _ ht'
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · intro h
          change z = G.target e at h
          exact he.2 (h ▸ hz)
        · exact hzs a ha
    · exact ih hnd.2 S D st hr hz hzs ht

/-- No edge is revealed twice on any path through the actual DFS tree. -/
theorem dfsTree_once (R : Finset V) (v : V) (fuel : ℕ) (S : Finset E) (D : Finset V)
    (st : List (V × Bool)) (hr : G.DFSReady S D st) :
    EdgeTree.Once (fun _ _ => True) S (G.dfsTree R v fuel D st) := by
  induction fuel generalizing S D st with
  | zero => exact .ret S _ trivial
  | succ fuel ih =>
    cases st with
    | nil => exact .ret S _ trivial
    | cons zf st =>
      obtain ⟨z,flag⟩ := zf
      simp only [dfsTree]
      by_cases h : z = v
      · simp only [h, ite_true]; exact .ret S _ trivial
      · simp only [h, ite_false]
        have hz : z ∈ D := hr.discovered (z,flag) (by simp)
        have hzs : ∀ a ∈ st, z ≠ a.1 := by
          intro a ha hza
          have hnd := (List.nodup_cons.mp hr.distinct).1
          exact hnd (List.mem_map.mpr ⟨a,ha,hza.symm⟩)
        apply (G.scanTree_once R z flag (arcOrder E) (arcOrder_nodup E) S D st
          (DFSReady.pop G hr) hz hzs (fun e _ he hmem => hr.used_off_stack e hmem (z,flag) (by simp) he)).bind _
        intro S' r hready
        exact ih S' r.1 r.2 hready

/-- At a recorded snapshot the target's outgoing edges and all edges the
restarted exploration can read are still fresh. -/
theorem dfsTree_once_snapshot (R : Finset V) (v : V) (fuel : ℕ) (S : Finset E)
    (D : Finset V) (st : List (V × Bool)) (hr : G.DFSReady S D st) :
    EdgeTree.Once (fun S o => ∀ A ∈ o, G.DFSReady S A [(v,true)]) S
      (G.dfsTree R v fuel D st) := by
  induction fuel generalizing S D st with
  | zero => exact .ret S _ (by simp)
  | succ fuel ih =>
    cases st with
    | nil => exact .ret S _ (by simp)
    | cons zf st =>
      obtain ⟨z,flag⟩ := zf
      simp only [dfsTree]
      by_cases h : z=v
      · subst z
        simp only [ite_true]
        cases flag with
        | false => exact .ret S _ (by simp)
        | true =>
          refine .ret S _ ?_
          intro A hA
          have hAD : A=D := by simpa using hA.symm
          subst A
          refine ⟨hr.used_discovered, ?_, by simp, ?_⟩
          · intro e he a ha
            have hav : a=(v,true) := by simpa using ha
            subst a
            exact hr.used_off_stack e he (v,true) (by simp)
          · simpa using hr.discovered (v,true) (by simp)
      · simp only [h, ite_false]
        have hz : z ∈ D := hr.discovered (z,flag) (by simp)
        have hzs : ∀ a ∈ st, z ≠ a.1 := by
          intro a ha hza
          exact (List.nodup_cons.mp hr.distinct).1 (List.mem_map.mpr ⟨a,ha,hza.symm⟩)
        apply (G.scanTree_once R z flag (arcOrder E) (arcOrder_nodup E) S D st
          (DFSReady.pop G hr) hz hzs
          (fun e _ he hmem => hr.used_off_stack e hmem (z,flag) (by simp) he)).bind _
        intro S' r hready
        exact ih S' r.1 r.2 hready

theorem dfsReady_initial (A : Finset V) (x : V) (hx : x ∈ A) :
    G.DFSReady ∅ A [(x,true)] := by
  refine ⟨by simp, by simp, by simp, ?_⟩
  simpa using hx

/-- The complete output law of a restarted DFS, including forced first-open
coordinates, equals deterministic exploration of a product-distributed graph. -/
theorem sDfs_deferred (p : E → ℝ) (hp : Prob01 p) (pre : E → Option Bool)
    (R A : Finset V) (x v : V) (hx : x ∈ A) (fuel : ℕ) (f : Option (Finset V) → ℝ) :
    (G.sDfs (Q := Empty) p R pre v fuel A [(x,true)]).exp noOracle f =
      ∑ ω, edgeWeight (forceProb p pre) ω*f ((G.dfsTree R v fuel A [(x,true)]).eval ω) := by
  rw [← G.dfsTree_run]
  exact (G.dfsTree_once R v fuel ∅ A [(x,true)] (G.dfsReady_initial A x hx)).deferred_forced p hp pre f

/-- Restarting from a recorded snapshot uses precisely the as-yet-unrevealed
part of the same retained graph. This is the regeneration law needed in the
last-resolved-vertex decomposition. -/
theorem sDfs_restart_deferred (p : E → ℝ) (hp : Prob01 p) (R T A : Finset V)
    (x v w : V) (hx : x ∈ A) (fuel restFuel : ℕ) (f : Option (Finset V) → ℝ) :
    (G.sDfs (Q := Empty) p R (fun _ => none) v fuel A [(x,true)]).exp noOracle
      (fun o => o.elim (f none) (fun D =>
        (G.sDfs p T (fun _ => none) w restFuel D [(v,true)]).exp noOracle f)) =
      ∑ ω, edgeWeight p ω * f
        (((G.dfsTree R v fuel A [(x,true)]).eval ω).elim none
          (fun D => (G.dfsTree T w restFuel D [(v,true)]).eval ω)) := by
  let t := G.dfsTree R v fuel A [(x,true)]
  let k : Option (Finset V) → EdgeTree E (Option (Finset V)) :=
    fun o => o.elim (.ret none) (fun D => G.dfsTree T w restFuel D [(v,true)])
  have ht := G.dfsTree_once_snapshot R v fuel ∅ A [(x,true)] (G.dfsReady_initial A x hx)
  have hk : EdgeTree.Once (fun _ _ => True) ∅ (t.bind k) := by
    apply ht.bind k
    intro S o ho
    cases o with
    | none => exact .ret S _ trivial
    | some D => exact G.dfsTree_once T w restFuel S D [(v,true)] (ho D (by simp))
  have h := hk.deferred p hp f
  rw [EdgeTree.run_bind, Prog.exp_bind] at h
  simp only [EdgeTree.eval_bind] at h
  have he (o : Option (Finset V)) : ((k o).run p (fun _ => none)).exp noOracle f =
      o.elim (f none) (fun D =>
        (G.sDfs p T (fun _ => none) w restFuel D [(v,true)]).exp noOracle f) := by
    cases o with
    | none => rfl
    | some D => rw [show k (some D) = G.dfsTree T w restFuel D [(v,true)] from rfl, G.dfsTree_run]
                rfl
  simp_rw [he] at h
  have hstat (ω : E → Bool) : (k (t.eval ω)).eval ω =
      (t.eval ω).elim none (fun D => (G.dfsTree T w restFuel D [(v,true)]).eval ω) := by
    cases t.eval ω <;> rfl
  simp_rw [hstat] at h
  simpa only [t, G.dfsTree_run] using h

end Digraph
end
end DirectedCycleFPRAS
