module

public import DirectedCycleFPRAS.AlgorithmSSearch

@[expose] public section

/-! Linearity of the target's path flag under a fixed retained graph.
Exploration order and discovered sets do not depend on path flags. -/
namespace DirectedCycleFPRAS
open Classical
noncomputable section
set_option linter.unusedSectionVars false
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E)

def recordScore (o : Option (Finset V)) : ℝ := o.elim 0 (fun _ => 1)
def flagValue (b : Bool) : ℝ := if b then 1 else 0

def falseStack (st : List (V × Bool)) : List (V × Bool) := st.map (fun a => (a.1,false))

def maskStack (v : V) (st : List (V × Bool)) : List (V × Bool) :=
  st.map (fun a => (a.1, a.2 && decide (a.1 ≠ v)))

inductive FlagSum : List (V × Bool) → List (V × Bool) → List (V × Bool) → Prop
  | nil : FlagSum [] [] []
  | cons (z : V) (a b c : Bool) {st st₀ st₁ : List (V × Bool)} :
      flagValue a = flagValue b + flagValue c → FlagSum st st₀ st₁ →
      FlagSum ((z,a)::st) ((z,b)::st₀) ((z,c)::st₁)

theorem flagValue_and {a b c : Bool} (h : flagValue a = flagValue b+flagValue c) (d : Bool) :
    flagValue (a&&d) = flagValue (b&&d)+flagValue (c&&d) := by
  cases d with
  | false => simp [flagValue]
  | true => simpa using h

theorem scanTree_flagSum (ω : E → Bool) (R : Finset V) (z : V) (a b c : Bool)
    (habc : flagValue a = flagValue b+flagValue c) (l : List E) (D : Finset V)
    (st st₀ st₁ : List (V × Bool)) (hs : FlagSum st st₀ st₁) :
    let r := (G.scanTree R z a l D st).eval ω
    let r₀ := (G.scanTree R z b l D st₀).eval ω
    let r₁ := (G.scanTree R z c l D st₁).eval ω
    r.1=r₀.1 ∧ r.1=r₁.1 ∧ FlagSum r.2 r₀.2 r₁.2 := by
  induction l generalizing D st st₀ st₁ with
  | nil => exact ⟨rfl,rfl,hs⟩
  | cons e l ih =>
    simp only [scanTree]
    split_ifs
    · simp only [EdgeTree.eval]
      cases ho : ω e with
      | false => exact ih D st st₀ st₁ hs
      | true => exact ih _ _ _ _ (.cons _ _ _ _ (flagValue_and habc _) hs)
    · exact ih D st st₀ st₁ hs

/-- With a fixed traversal, the final target flag is linear in disjoint
initial flag assignments. -/
theorem dfsTree_score_add (ω : E → Bool) (R : Finset V) (w : V) (fuel : ℕ)
    (D : Finset V) (st st₀ st₁ : List (V × Bool)) (hs : FlagSum st st₀ st₁) :
    recordScore ((G.dfsTree R w fuel D st).eval ω) =
      recordScore ((G.dfsTree R w fuel D st₀).eval ω) +
      recordScore ((G.dfsTree R w fuel D st₁).eval ω) := by
  induction fuel generalizing D st st₀ st₁ with
  | zero => simp [dfsTree, EdgeTree.eval, recordScore]
  | succ fuel ih =>
    cases hs with
    | nil => simp [dfsTree, EdgeTree.eval, recordScore]
    | @cons z a b c st st₀ st₁ hflag hs =>
      by_cases hz : z=w
      · simp only [dfsTree, hz, ite_true]
        have he (d : Bool) : recordScore ((EdgeTree.ret (if d then some D else none) : EdgeTree E _).eval ω) = flagValue d := by
          cases d <;> rfl
        simp only [he]
        exact hflag
      · simp only [dfsTree, hz, ite_false, EdgeTree.eval_bind]
        have hscan := G.scanTree_flagSum ω R z a b c hflag (arcOrder E) D _ _ _ hs
        rw [← hscan.1, ← hscan.2.1]
        exact ih _ _ _ _ hscan.2.2

theorem scanTree_append (ω : E → Bool) (R : Finset V) (z : V) (flag : Bool)
    (l : List E) (D : Finset V) (st suffix : List (V × Bool)) :
    (G.scanTree R z flag l D (st++suffix)).eval ω =
      let r := (G.scanTree R z flag l D st).eval ω
      (r.1,r.2++suffix) := by
  induction l generalizing D st with
  | nil => rfl
  | cons e l ih =>
    simp only [scanTree]
    split_ifs
    · simp only [EdgeTree.eval]
      cases ho : ω e with
      | false => exact ih D st
      | true => exact ih (insert (G.target e) D) ((G.target e,flag && decide (G.target e ∉ R))::st)
    · exact ih D st

theorem scanTree_false (ω : E → Bool) (R : Finset V) (z : V)
    (l : List E) (D : Finset V) (st : List (V × Bool)) (hs : ∀ a ∈ st, a.2=false) :
    ∀ a ∈ ((G.scanTree R z false l D st).eval ω).2, a.2=false := by
  induction l generalizing D st with
  | nil => exact hs
  | cons e l ih =>
    simp only [scanTree]
    split_ifs
    · simp only [EdgeTree.eval]
      cases ho : ω e with
      | false => exact ih D st hs
      | true =>
        apply ih
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · rfl
        · exact hs a ha
    · exact ih D st hs

theorem dfsTree_false (ω : E → Bool) (R : Finset V) (w : V) (fuel : ℕ)
    (D : Finset V) (st : List (V × Bool)) (hs : ∀ a ∈ st, a.2=false) :
    (G.dfsTree R w fuel D st).eval ω = none := by
  induction fuel generalizing D st with
  | zero => rfl
  | succ fuel ih =>
    cases st with
    | nil => rfl
    | cons a st =>
      obtain ⟨z,flag⟩ := a
      have hf : flag=false := hs (z,flag) (by simp)
      subst flag
      by_cases hz : z=w
      · simp [dfsTree, hz, EdgeTree.eval]
      · simp only [dfsTree, hz, ite_false, EdgeTree.eval_bind]
        exact ih _ _ (G.scanTree_false ω R z (arcOrder E) D st (fun a ha => hs a (by simp [ha])))

/-- A suffix with false flags contributes no target score. It can be dropped
because DFS processes all descendants of the prefix before visiting the suffix. -/
theorem dfsTree_score_false_suffix (ω : E → Bool) (R : Finset V) (w : V) (fuel : ℕ)
    (D : Finset V) (st suffix : List (V × Bool)) (hs : ∀ a ∈ suffix, a.2=false) :
    recordScore ((G.dfsTree R w fuel D (st++suffix)).eval ω) =
      recordScore ((G.dfsTree R w fuel D st).eval ω) := by
  induction fuel generalizing D st with
  | zero => rfl
  | succ fuel ih =>
    cases st with
    | nil =>
      simp only [List.nil_append, dfsTree, EdgeTree.eval]
      rw [G.dfsTree_false ω R w (fuel+1) D suffix hs]
    | cons a st =>
      obtain ⟨z,flag⟩ := a
      simp only [List.cons_append, dfsTree]
      by_cases hz : z=w
      · simp only [hz, ite_true]
      · simp only [hz, ite_false, EdgeTree.eval_bind, G.scanTree_append]
        exact ih _ _

theorem FlagSum.zero_right (st : List (V × Bool)) : FlagSum st st (falseStack st) := by
  induction st with
  | nil => exact .nil
  | cons a st ih => exact .cons a.1 a.2 a.2 false (by simp [flagValue]) ih

/-- Changing the head flag from false to true adds exactly the score of
restarting from that head and dropping the pending suffix. -/
theorem dfsTree_score_head (ω : E → Bool) (R : Finset V) (w z : V) (fuel : ℕ)
    (D : Finset V) (st : List (V × Bool)) (flag : Bool) :
    recordScore ((G.dfsTree R w fuel D ((z,flag)::st)).eval ω) =
      recordScore ((G.dfsTree R w fuel D ((z,false)::st)).eval ω) +
      flagValue flag * recordScore ((G.dfsTree R w fuel D [(z,true)]).eval ω) := by
  cases flag with
  | false => simp [flagValue]
  | true =>
    have h := G.dfsTree_score_add ω R w fuel D _ _ _
      (FlagSum.cons z true false true (by norm_num [flagValue]) (FlagSum.zero_right st))
    have hs : ∀ a ∈ falseStack st, a.2=false := by
      intro a ha; obtain ⟨b,_,rfl⟩ := List.mem_map.mp ha; rfl
    have he := G.dfsTree_score_false_suffix ω R w fuel D [(z,true)] (falseStack st) hs
    simp only [List.singleton_append] at he
    rw [he] at h
    simpa [flagValue] using h

end Digraph
end
end DirectedCycleFPRAS
