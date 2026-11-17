module

public import DirectedCycleFPRAS.AlgorithmSStopping

@[expose] public section
namespace DirectedCycleFPRAS
open Classical
noncomputable section
set_option linter.unusedSectionVars false
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [ArcEnumeration E] [DecidableEq E]

/-- A parent-pointer path from the root whose nonroot vertices avoid R. -/
def ParentAvoid (R : Finset V) (parent : V → Option V) (root v : V) : Prop :=
  Relation.ReflTransGen (fun x y => parent y = some x ∧ y ∉ R) root v

/-- Every installed pointer joins two discovered vertices. -/
def ParentClosed (D : Finset V) (parent : V → Option V) : Prop :=
  ∀ x y, parent y = some x → x ∈ D ∧ y ∈ D

/-- Installing the parent of a newly discovered vertex cannot change any old
vertex's parent-path test. -/
theorem parentAvoid_update_old (R D : Finset V) (parent : V → Option V)
    (root z y v : V) (hc : ParentClosed D parent) (_hz : z ∈ D)
    (hy : y ∉ D) (hv : v ∈ D) :
    ParentAvoid R (Function.update parent y (some z)) root v ↔ ParentAvoid R parent root v := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail b c h hbc ih =>
      have hcy : c ≠ y := fun he => hy (he ▸ hv)
      have hp : parent c = some b := by simpa [Function.update_of_ne hcy] using hbc.1
      exact (ih (hc b c hp).1).tail ⟨hp, hbc.2⟩
  · intro h
    apply Relation.ReflTransGen.mono _ _ _ h
    intro a b hab
    have hby : b ≠ y := fun he => hy (he ▸ (hc a b hab.1).2)
    exact ⟨by simpa [Function.update_of_ne hby] using hab.1, hab.2⟩

/-- The new vertex passes precisely when its parent passes and it avoids R. -/
theorem parentAvoid_update_new (R D : Finset V) (parent : V → Option V)
    (root z y : V) (hc : ParentClosed D parent) (hr : root ∈ D)
    (hz : z ∈ D) (hy : y ∉ D) :
    ParentAvoid R (Function.update parent y (some z)) root y ↔
      ParentAvoid R parent root z ∧ y ∉ R := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with heq | ⟨x, hx, hxy⟩
    · exact False.elim (hy (heq ▸ hr))
    · have hxz : x = z := by simpa using hxy.1.symm
      subst x
      exact ⟨(parentAvoid_update_old R D parent root z y z hc hz hy hz).mp hx, hxy.2⟩
  · rintro ⟨h, hyR⟩
    exact ((parentAvoid_update_old R D parent root z y z hc hz hy hz).mpr h).tail
      ⟨Function.update_self _ _ _, hyR⟩

theorem parentClosed_update (D : Finset V) (parent : V → Option V)
    (z y : V) (hc : ParentClosed D parent) (hz : z ∈ D) :
    ParentClosed (insert y D) (Function.update parent y (some z)) := by
  intro a b hab
  by_cases hb : b = y
  · subst b
    have ha : a = z := by simpa using hab.symm
    subst a
    exact ⟨Finset.mem_insert_of_mem hz, Finset.mem_insert_self _ _⟩
  · have hp : parent b = some a := by simpa [Function.update_of_ne hb] using hab
    exact ⟨Finset.mem_insert_of_mem (hc a b hp).1, Finset.mem_insert_of_mem (hc a b hp).2⟩

/-- DFS state with an explicit parent table and a vertex-only stack. -/
structure ParentState (V : Type) where
  discovered : Finset V
  stack : List V
  parent : V → Option V

def ParentState.Valid (root : V) (s : ParentState V) : Prop :=
  root ∈ s.discovered ∧ ParentClosed s.discovered s.parent ∧ ∀ v ∈ s.stack, v ∈ s.discovered

def ParentState.flags (R : Finset V) (root : V) (s : ParentState V) : List (V × Bool) :=
  s.stack.map fun v => (v, decide (ParentAvoid R s.parent root v))

def ParentState.discover (s : ParentState V) (z y : V) : ParentState V :=
  ⟨insert y s.discovered, y :: s.stack, Function.update s.parent y (some z)⟩

theorem ParentState.valid_discover {root : V} {s : ParentState V} (hs : s.Valid root)
    {z y : V} (hz : z ∈ s.discovered) : (s.discover z y).Valid root := by
  refine ⟨Finset.mem_insert_of_mem hs.1, parentClosed_update _ _ _ _ hs.2.1 hz, ?_⟩
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (hs.2.2 v hv)

theorem ParentState.flags_discover (R : Finset V) (root : V) (s : ParentState V)
    (hs : s.Valid root) (z y : V) (hz : z ∈ s.discovered) (hy : y ∉ s.discovered) :
    (s.discover z y).flags R root =
      (y, decide (ParentAvoid R s.parent root z) && decide (y ∉ R)) :: s.flags R root := by
  simp only [flags, discover, List.map_cons]
  congr 1
  · simp [parentAvoid_update_new R s.discovered s.parent root z y hs.2.1 hs.1 hz hy]
  · apply List.map_congr_left
    intro v hv
    simp only [parentAvoid_update_old R s.discovered s.parent root z y v hs.2.1 hz hy (hs.2.2 v hv)]

variable (G : Digraph V E) (p : E → ℝ)

/-- The scan updates a parent only when discovering a new vertex. It stores
no Boolean eligibility flags. -/
def parentScan (pre : E → Option Bool) (z : V) : List E → ParentState V → Prog Empty (ParentState V)
  | [], s => .ret s
  | e :: l, s =>
    if G.source e = z ∧ G.target e ∉ s.discovered then
      ((pre e).elim (Prog.choose (coin (p e)) Prog.ret) Prog.ret).bind fun o =>
        if o then parentScan pre z l (s.discover z (G.target e)) else parentScan pre z l s
    else parentScan pre z l s

theorem parentScan_valid (pre : E → Option Bool) (root z : V) (l : List E)
    (s : ParentState V) (hs : s.Valid root) (hz : z ∈ s.discovered) :
    Prog.Sat (fun _ => True) (fun _ => True)
      (fun r : ParentState V => r.Valid root ∧ z ∈ r.discovered) (G.parentScan p pre z l s) := by
  induction l generalizing s with
  | nil => exact .ret _ ⟨hs, hz⟩
  | cons e l ih =>
    unfold parentScan
    split_ifs with he
    · refine (Prog.Sat.trivial _).bind fun o _ => ?_
      cases o with
      | false => exact ih s hs hz
      | true => exact ih _ (ParentState.valid_discover hs hz) (Finset.mem_insert_of_mem hz)
    · exact ih s hs hz

/-- The scan with explicit pointers simulates the existing flag-based scan. -/
theorem parentScan_law (R : Finset V) (pre : E → Option Bool) (root z : V) (l : List E)
    (s : ParentState V) (hs : s.Valid root) (hz : z ∈ s.discovered)
    (f : Finset V × List (V × Bool) → ℝ) :
    (G.parentScan p pre z l s).exp noOracle (fun r => f (r.discovered, r.flags R root)) =
      (G.sScan p R pre z (decide (ParentAvoid R s.parent root z)) l
        s.discovered (s.flags R root)).exp noOracle f := by
  induction l generalizing s with
  | nil => rfl
  | cons e l ih =>
    simp only [parentScan, sScan]
    by_cases he : G.source e = z ∧ G.target e ∉ s.discovered
    · simp only [he, not_false_eq_true, and_self, ite_true, Prog.exp_bind]
      apply congrArg (((pre e).elim (Prog.choose (coin (p e)) Prog.ret) Prog.ret).exp noOracle)
      funext o
      cases o with
      | false => exact ih s hs hz
      | true =>
        simp only [ite_true]
        rw [ih _ (ParentState.valid_discover hs hz) (Finset.mem_insert_of_mem hz),
          ParentState.flags_discover R root s hs z (G.target e) hz he.2]
        simp only [show ParentAvoid R (s.discover z (G.target e)).parent root z =
            ParentAvoid R s.parent root z from propext
              (parentAvoid_update_old R s.discovered s.parent root z (G.target e) z hs.2.1 hz he.2 hz)]
        rfl
    · simp only [he, ite_false]
      exact ih s hs hz

/-- Each push adds exactly one discovered vertex, also on zero-mass branches. -/
theorem parentScan_balance (pre : E → Option Bool) (z : V) (l : List E) (s : ParentState V) :
    Prog.Sat (fun _ => True) (fun _ => True)
      (fun r : ParentState V => r.discovered.card + s.stack.length =
        s.discovered.card + r.stack.length) (G.parentScan p pre z l s) := by
  induction l generalizing s with
  | nil => exact .ret _ rfl
  | cons e l ih =>
    unfold parentScan
    split_ifs with he
    · refine (Prog.Sat.trivial _).bind fun o _ => ?_
      cases o with
      | false => exact ih s
      | true =>
        apply (ih (s.discover z (G.target e))).imp
        intro r hr
        simp only [ParentState.discover, List.length_cons, Finset.card_insert_of_notMem he.2] at hr
        omega
    · exact ih s

/-- Complete a DFS using parent pointers, without a second record. -/
def parentExplore (pre : E → Option Bool) : ℕ → ParentState V → Prog Empty (ParentState V)
  | 0, s => .ret s
  | f + 1, s => match s.stack with
    | [] => .ret s
    | z :: st => (G.parentScan p pre z (arcOrder E) {s with stack := st}).bind fun r =>
        parentExplore pre f r

/-- With the usual potential bound, finishing the parent traversal really
empties its stack on every branch. -/
theorem parentExplore_done (pre : E → Option Bool) (fuel : ℕ) (s : ParentState V)
    (hf : Fintype.card V - s.discovered.card + s.stack.length < fuel) :
    Prog.Sat (fun _ => True) (fun _ => True)
      (fun r : ParentState V => r.stack = []) (G.parentExplore p pre fuel s) := by
  induction fuel generalizing s with
  | zero => omega
  | succ fuel ih =>
    cases hst : s.stack with
    | nil =>
      simp only [parentExplore, hst]
      exact .ret _ hst
    | cons z st =>
      simp only [parentExplore, hst]
      apply (G.parentScan_balance p pre z (arcOrder E) {s with stack := st}).bind
      intro r hr
      apply ih
      have hD := Finset.card_le_univ s.discovered
      have hD' := Finset.card_le_univ r.discovered
      simp only [hst, List.length_cons] at hf
      change r.discovered.card + st.length = s.discovered.card + r.stack.length at hr
      omega

/-- Additional fuel is redundant once the parent traversal's potential is covered. -/
theorem parentExplore_fuel_add (pre : E → Option Bool) (fuel extra : ℕ) (s : ParentState V)
    (hf : Fintype.card V - s.discovered.card + s.stack.length < fuel) :
    G.parentExplore p pre fuel s = G.parentExplore p pre (fuel + extra) s := by
  induction fuel generalizing s with
  | zero => omega
  | succ fuel ih =>
    cases hst : s.stack with
    | nil => simp [Nat.succ_add, parentExplore, hst]
    | cons z st =>
      simp only [Nat.succ_add, parentExplore, hst]
      apply (G.parentScan_balance p pre z (arcOrder E) {s with stack := st}).bind_congr
        (fun _ => trivial)
      intro r hr
      apply ih
      have hD := Finset.card_le_univ s.discovered
      have hD' := Finset.card_le_univ r.discovered
      simp only [hst, List.length_cons] at hf
      change r.discovered.card + st.length = s.discovered.card + r.stack.length at hr
      omega

/-- Literal parent-pointer traversal: test the path when the target is popped,
freeze that snapshot, and finish exploring. There are no stored flags. -/
def parentDfs (R : Finset V) (pre : E → Option Bool) (root v : V) :
    ℕ → ParentState V → Prog Empty (Option (Finset V))
  | 0, _ => .ret none
  | f + 1, s => match s.stack with
    | [] => .ret none
    | z :: st =>
      if z = v then
        (G.parentExplore p pre (f + 1) s).bind fun _ =>
          .ret (if ParentAvoid R s.parent root z then some s.discovered else none)
      else (G.parentScan p pre z (arcOrder E) {s with stack := st}).bind fun r =>
        parentDfs R pre root v f r

/-- The same potential suffices before and after the target is popped. -/
theorem parentDfs_fuel_add (R : Finset V) (pre : E → Option Bool) (root v : V)
    (fuel extra : ℕ) (s : ParentState V)
    (hf : Fintype.card V - s.discovered.card + s.stack.length < fuel) :
    G.parentDfs p R pre root v fuel s = G.parentDfs p R pre root v (fuel + extra) s := by
  induction fuel generalizing s with
  | zero => omega
  | succ fuel ih =>
    cases hst : s.stack with
    | nil => simp [Nat.succ_add, parentDfs, hst]
    | cons z st =>
      simp only [Nat.succ_add, parentDfs, hst]
      by_cases hz : z = v
      · simp only [hz, ite_true]
        rw [G.parentExplore_fuel_add p pre (fuel + 1) extra s hf,
          Nat.add_right_comm fuel 1 extra]
      · simp only [hz, ite_false]
        apply (G.parentScan_balance p pre z (arcOrder E) {s with stack := st}).bind_congr
          (fun _ => trivial)
        intro r hr
        apply ih
        have hD := Finset.card_le_univ s.discovered
        have hD' := Finset.card_le_univ r.discovered
        simp only [hst, List.length_cons] at hf
        change r.discovered.card + st.length = s.discovered.card + r.stack.length at hr
        omega

/-- The canonical n+1 fuel completes the explicit-parent traversal from a
valid snapshot, including all exploration after the record is frozen. -/
theorem parentDfs_initial_fuel (R : Finset V) (pre : E → Option Bool) (root v : V)
    (D : Finset V) (hroot : root ∈ D) (extra : ℕ) :
    G.parentDfs p R pre root v (Fintype.card V + 1) ⟨D, [root], fun _ => none⟩ =
      G.parentDfs p R pre root v (Fintype.card V + 1 + extra) ⟨D, [root], fun _ => none⟩ := by
  apply G.parentDfs_fuel_add
  have hD : 0 < D.card := Finset.card_pos.mpr ⟨root, hroot⟩
  have hcard := Finset.card_le_univ D
  simp only [List.length_cons, List.length_nil]
  omega

/-- Equality of the whole recorded-snapshot law for explicit parents and flags. -/
theorem parentDfs_law (R : Finset V) (pre : E → Option Bool) (root v : V) (fuel : ℕ)
    (s : ParentState V) (hs : s.Valid root) (f : Option (Finset V) → ℝ) :
    (G.parentDfs p R pre root v fuel s).exp noOracle f =
      (G.sDfs p R pre v fuel s.discovered (s.flags R root)).exp noOracle f := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    cases hst : s.stack with
    | nil => simp [parentDfs, ParentState.flags, hst, sDfs, Prog.exp]
    | cons z st =>
      have hz : z ∈ s.discovered := hs.2.2 z (by simp [hst])
      have ht : ({s with stack := st} : ParentState V).Valid root :=
        ⟨hs.1, hs.2.1, fun x hx => hs.2.2 x (by simp [hst, hx])⟩
      simp only [parentDfs, hst, ParentState.flags, List.map_cons, sDfs]
      by_cases hzv : z = v
      · simp only [hzv, ite_true, Prog.exp_bind, Prog.exp]
        rw [Prog.exp_const]
        split_ifs <;> simp_all
      · simp only [hzv, ite_false, Prog.exp_bind]
        trans (G.parentScan p pre z (arcOrder E) {s with stack := st}).exp noOracle
          (fun r => (G.sDfs p R pre v fuel r.discovered (r.flags R root)).exp noOracle f)
        · apply (G.parentScan_valid p pre root z (arcOrder E) _ ht hz).supported.exp_congr
          intro r hr
          exact ih r hr.1
        · exact G.parentScan_law p R pre root z (arcOrder E) _ ht hz
            (fun r => (G.sDfs p R pre v fuel r.1 r.2).exp noOracle f)

/-- The paper's parent-pointer path test and finish-after-recording traversal
have exactly the snapshot law used by the existing Algorithm S iteration. -/
theorem parentDfs_initial_law (R : Finset V) (pre : E → Option Bool) (root v : V)
    (D : Finset V) (hroot : root ∈ D) (fuel : ℕ) (f : Option (Finset V) → ℝ) :
    (G.parentDfs p R pre root v fuel ⟨D, [root], fun _ => none⟩).exp noOracle f =
      (G.sDfs p R pre v fuel D [(root, true)]).exp noOracle f := by
  have hs : (ParentState.mk D [root] (fun _ => none)).Valid root := by
    refine ⟨hroot, ?_, ?_⟩
    · intro x y h; cases h
    · simpa using hroot
  simpa [ParentState.flags, ParentAvoid, Relation.ReflTransGen.refl] using
    G.parentDfs_law p R pre root v fuel _ hs f

end Digraph
end
end DirectedCycleFPRAS
