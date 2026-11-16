module

public import DirectedCycleFPRAS.AlgorithmSOrdered
public import DirectedCycleFPRAS.ReindexLaw

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E)

/-- The induced graph on a closed set, with both vertices and edges genuinely
reindexed to subtypes. Closure supplies the target's membership proof. -/
def inducedClosed (U : Finset V) (hU : ∀ e, G.source e ∈ U → G.target e ∈ U) :
    Digraph U {e : E // G.source e ∈ U} where
  source e := ⟨G.source e, e.property⟩
  target e := ⟨G.target e, hU e e.property⟩

/-- Filter an arc list while retaining the original order. -/
def subtypeOrder (U : Finset V) : List E → List {e : E // G.source e ∈ U}
  | [] => []
  | e :: l => if he : G.source e ∈ U then ⟨e, he⟩ :: subtypeOrder U l else subtypeOrder U l

variable {U : Finset V}
def upSet (D : Finset U) : Finset V := D.image Subtype.val
def upStack (st : List (U × Bool)) : List (V × Bool) := st.map fun x => (x.1.val, x.2)
def upPool (pool : List (Finset U)) : List (Finset V) := pool.map upSet

@[simp] theorem mem_upSet (D : Finset U) (v : U) : v.val ∈ upSet D ↔ v ∈ D := by
  simp [upSet]

theorem upSet_subset (D : Finset U) : upSet D ⊆ U := by
  rintro v hv
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
  exact x.property

@[simp] theorem upSet_insert (D : Finset U) (v : U) : upSet (insert v D) = insert v.val (upSet D) := by
  simp [upSet]
@[simp] theorem upSet_empty : upSet (∅ : Finset U) = ∅ := by simp [upSet]
@[simp] theorem upStack_cons (st : List (U × Bool)) (v : U) (b : Bool) :
    upStack ((v, b) :: st) = (v.val, b) :: upStack st := rfl
@[simp] theorem upStack_nil : upStack ([] : List (U × Bool)) = [] := rfl
@[simp] theorem upPool_cons (pool : List (Finset U)) (D : Finset U) :
    upPool (D :: pool) = upSet D :: upPool pool := rfl
@[simp] theorem upPool_nil : upPool ([] : List (Finset U)) = [] := rfl
@[simp] theorem upPool_length (pool : List (Finset U)) : (upPool pool).length = pool.length := by
  simp [upPool]
@[simp] theorem upPool_getD (pool : List (Finset U)) (i : ℕ) :
    (upPool pool).getD i ∅ = upSet (pool.getD i ∅) := by
  simpa [upPool] using List.getD_map pool ∅ (n := i) upSet

variable (p : E → ℝ) (U : Finset V) (hU : ∀ e, G.source e ∈ U → G.target e ∈ U)

theorem subtypeOrder_map (l : List E) :
    (G.subtypeOrder U l).map Subtype.val = l.filter (fun e => decide (G.source e ∈ U)) := by
  induction l with
  | nil => rfl
  | cons e l ih => by_cases he : G.source e ∈ U <;> simp [subtypeOrder, he, ih]

/-- The inherited list contains every retained arc, with no new duplicates. -/
theorem subtypeOrder_nodup (l : List E) (hl : l.Nodup) : (G.subtypeOrder U l).Nodup := by
  apply List.Nodup.of_map (f := Subtype.val)
  rw [G.subtypeOrder_map U l]
  exact hl.filter _

theorem mem_subtypeOrder (l : List E) (e : {e : E // G.source e ∈ U}) :
    e ∈ G.subtypeOrder U l ↔ e.val ∈ l := by
  have h : e.val ∈ (G.subtypeOrder U l).map Subtype.val ↔ e.val ∈ l := by
    rw [G.subtypeOrder_map U l]
    simp [e.property]
  simpa [e.property] using h

theorem subtypeOrder_complete (e : {e : E // G.source e ∈ U}) :
    e ∈ G.subtypeOrder U (arcOrder E) := by
  rw [G.mem_subtypeOrder U]
  simp [arcOrder]

@[simp] theorem induced_cut (R : Finset U) (u : U) (e : {e : E // G.source e ∈ U}) :
    (G.inducedClosed U hU).cutAt R u e ↔ G.cutAt (upSet R) u.val e.val := by
  simp only [cutAt, inducedClosed, ← Subtype.val_inj,
    mem_upSet R (⟨G.target e.val, hU e.val e.property⟩ : U)]

/-- Scan simulation retains the exact sequence of random choices; removed
arcs are precisely those whose sources cannot be the current vertex. -/
theorem sScan_subtype (R : Finset U) (pre : E → Option Bool) (z : U) (flag : Bool)
    (l : List E) (D : Finset U) (st : List (U × Bool))
    (f : Finset V × List (V × Bool) → ℝ) :
    ((G.inducedClosed U hU).sScan (fun e => p e.val) R (fun e => pre e.val) z flag
      (G.subtypeOrder U l) D st).exp noOracle (fun r => f (upSet r.1, upStack r.2)) =
      (G.sScan p (upSet R) pre z.val flag l (upSet D) (upStack st)).exp noOracle f := by
  induction l generalizing D st with
  | nil => rfl
  | cons e l ih =>
    by_cases heU : G.source e ∈ U
    · simp only [subtypeOrder, dite_eq_left heU, sScan]
      have hc : ((G.inducedClosed U hU).source ⟨e, heU⟩ = z ∧
          (G.inducedClosed U hU).target ⟨e, heU⟩ ∉ D) ↔
          (G.source e = z.val ∧ G.target e ∉ upSet D) := by
        simp only [inducedClosed, ← Subtype.val_inj,
          mem_upSet D (⟨G.target e, hU e heU⟩ : U)]
      simp only [hc]
      by_cases he : G.source e = z.val ∧ G.target e ∉ upSet D
      · simp only [he, not_false_eq_true, and_self, ite_true, Prog.exp_bind]
        apply congrArg (((pre e).elim (Prog.choose (coin (p e)) Prog.ret) Prog.ret).exp noOracle)
        funext o
        cases o with
        | false => exact ih D st
        | true =>
          simpa only [ite_true, upSet_insert, upStack_cons, inducedClosed,
            mem_upSet R (⟨G.target e, hU e heU⟩ : U)] using
            ih (insert ⟨G.target e, hU e heU⟩ D)
              ((⟨G.target e, hU e heU⟩, flag && decide (⟨G.target e, hU e heU⟩ ∉ R)) :: st)
      · simp only [he, ite_false]
        exact ih D st
    · have hne : G.source e ≠ z.val := fun h => heU (h ▸ z.property)
      simp only [subtypeOrder, dite_eq_right heU, sScan, hne, false_and, ite_false]
      exact ih D st

/-- DFS on actual subtype states simulates the ambient DFS with the inherited order. -/
theorem oDfs_subtype (order : List E) (R : Finset U) (pre : E → Option Bool) (v : U)
    (fuel : ℕ) (D : Finset U) (st : List (U × Bool)) (f : Option (Finset V) → ℝ) :
    ((G.inducedClosed U hU).oDfs (fun e => p e.val) (G.subtypeOrder U order) R
      (fun e => pre e.val) v fuel D st).exp noOracle (fun o => f (o.map upSet)) =
      (G.oDfs p order (upSet R) pre v.val fuel (upSet D) (upStack st)).exp noOracle f := by
  induction fuel generalizing D st with
  | zero => rfl
  | succ fuel ih =>
    cases st with
    | nil => rfl
    | cons zf st =>
      obtain ⟨z, flag⟩ := zf
      simp only [oDfs, upStack_cons, Subtype.val_inj]
      by_cases hz : z = v
      · simp only [hz, ite_true]
        cases flag <;> rfl
      · simp only [hz, ite_false, Prog.exp_bind]
        simp_rw [ih]
        exact G.sScan_subtype p U hU R pre z flag order D st
          (fun r => (G.oDfs p order (upSet R) pre v.val fuel r.1 r.2).exp noOracle f)

/-- Edge weights are unchanged after reindexing both endpoints and arcs. -/
theorem oFirst_subtype (rank : E → ℕ) (R : Finset U) (u : U) (e : {e : E // G.source e ∈ U}) :
    (G.inducedClosed U hU).oFirst (fun e => p e.val) (fun e => rank e.val) R u e =
      G.oFirst p rank (upSet R) u.val e.val := by
  unfold oFirst
  simp only [G.induced_cut U hU R u e]
  split_ifs
  · congr 1
    rw [Finset.prod_filter, Finset.prod_filter]
    apply Fintype.prod_of_injective Subtype.val Subtype.val_injective
    · intro j hj
      have hn : G.source j ∉ U := fun h => hj ⟨⟨j, h⟩, rfl⟩
      have hc : ¬ G.cutAt (upSet R) u.val j := fun h => hn (h.1 ▸ u.property)
      simp [hc]
    · intro j
      simp only [induced_cut]
  · rfl

theorem oFirst_outside (rank : E → ℕ) (R : Finset U) (u : U) (e : E) (he : G.source e ∉ U) :
    G.oFirst p rank (upSet R) u.val e = 0 := by
  have hc : ¬ G.cutAt (upSet R) u.val e := fun h => he (h.1 ▸ u.property)
  simp [oFirst, hc]

theorem oGamma_subtype (rank : E → ℕ) (R : Finset U) (u : U) :
    (G.inducedClosed U hU).oGamma (fun e => p e.val) (fun e => rank e.val) R u =
      G.oGamma p rank (upSet R) u.val := by
  unfold oGamma
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro e he
    exact G.oFirst_outside p U rank R u e (fun h => he ⟨⟨e, h⟩, rfl⟩)
  · intro e
    exact G.oFirst_subtype p U hU rank R u e

theorem oPre_subtype (rank : E → ℕ) (R : Finset U) (u : U)
    (j e : {e : E // G.source e ∈ U}) :
    (G.inducedClosed U hU).oPre (fun e => rank e.val) R u j e =
      G.oPre rank (upSet R) u.val j.val e.val := by
  simp only [oPre, induced_cut, Subtype.val_inj]


/-- Reindexing the entire iteration, including all three finite choices. -/
theorem oIter_subtype (order : List E) (rank : E → ℕ) (dfsFuel : ℕ)
    (R : Finset U) (qh : V → ℝ) (qh' : U → ℝ)
    (pools : V → List (Finset V)) (pools' : U → List (Finset U))
    (hqh : ∀ u, qh' u = qh u.val) (hpools : ∀ u, pools u.val = upPool (pools' u))
    (M : ℕ) (v : U) (f : Option (Finset V) → ℝ) :
    ((G.inducedClosed U hU).oIter (fun e => p e.val) (G.subtypeOrder U order)
      (fun e => rank e.val) dfsFuel R qh' pools' M v).exp noOracle (fun o => f (o.map upSet)) =
      (G.oIter p order rank dfsFuel (upSet R) qh pools M v.val).exp noOracle f := by
  unfold oIter
  simp only [Prog.exp]
  symm
  apply normLaw_reindex (fun o : Option U => o.map Subtype.val)
    (Option.map_injective Subtype.val_injective) _ _ none
  · intro o
    cases o with
    | none => rfl
    | some u => simp only [Option.map_some, Option.elim_some, hqh, oGamma_subtype, mem_upSet]
  · intro o ho
    cases o with
    | none => exact False.elim (ho ⟨none, rfl⟩)
    | some u =>
      have hu : u ∉ U := fun h => ho ⟨some ⟨u, h⟩, rfl⟩
      have hr : u ∉ upSet R := fun h => hu (upSet_subset R h)
      simp [hr]
  · intro o
    cases o with
    | none => rfl
    | some u =>
      simp only [Option.map_some, Option.elim_some, Prog.exp, hpools, upPool_length]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      apply normLaw_reindex
        (fun o : Option {e : E // G.source e ∈ U} => o.map Subtype.val)
        (Option.map_injective Subtype.val_injective) _ _ none
      · intro j
        cases j with
        | none => rfl
        | some j => exact G.oFirst_subtype p U hU rank R u j
      · intro j hj
        cases j with
        | none => exact False.elim (hj ⟨none, rfl⟩)
        | some j => exact G.oFirst_outside p U rank R u j (fun h => hj ⟨some ⟨j, h⟩, rfl⟩)
      · intro j
        cases j with
        | none => rfl
        | some j =>
          simp only [Option.map_some, Option.elim_some, upPool_getD]
          have hpre : (G.inducedClosed U hU).oPre (fun e => rank e.val) R u j =
              fun e => G.oPre rank (upSet R) u.val j.val e.val := by
            funext e
            exact G.oPre_subtype U hU rank R u j e
          rw [hpre]
          exact (G.oDfs_subtype p U hU order R (G.oPre rank (upSet R) u.val j.val)
            v dfsFuel (pools' u |>.getD i ∅) [(u, true)] f).symm

theorem oGenerate_subtype (order : List E) (rank : E → ℕ) (dfsFuel : ℕ)
    (R : Finset U) (qh : V → ℝ) (qh' : U → ℝ)
    (pools : V → List (Finset V)) (pools' : U → List (Finset U))
    (hqh : ∀ u, qh' u = qh u.val) (hpools : ∀ u, pools u.val = upPool (pools' u))
    (M : ℕ) (v : U) (i : ℕ) (f : ℕ × List (Finset V) → ℝ) :
    ((G.inducedClosed U hU).oGenerate (fun e => p e.val) (G.subtypeOrder U order)
      (fun e => rank e.val) dfsFuel R qh' pools' M v i).exp noOracle
        (fun r => f (r.1, upPool r.2)) =
      (G.oGenerate p order rank dfsFuel (upSet R) qh pools M v.val i).exp noOracle f := by
  induction i generalizing f with
  | zero => rfl
  | succ i ih =>
    simp only [oGenerate, Prog.exp_bind]
    have hstep : ∀ acc : ℕ × List (Finset U),
        ((G.inducedClosed U hU).oIter (fun e => p e.val) (G.subtypeOrder U order)
          (fun e => rank e.val) dfsFuel R qh' pools' M v).exp noOracle
            (fun o => f ((o.elim acc fun D => (acc.1 + 1, D :: acc.2)).1,
              upPool (o.elim acc fun D => (acc.1 + 1, D :: acc.2)).2)) =
        (G.oIter p order rank dfsFuel (upSet R) qh pools M v.val).exp noOracle
          (fun o => f (o.elim (acc.1, upPool acc.2) fun D => (acc.1 + 1, D :: upPool acc.2))) := by
      intro acc
      convert G.oIter_subtype p U hU order rank dfsFuel R qh qh' pools pools' hqh hpools M v
        (fun o => f (o.elim (acc.1, upPool acc.2) fun D => (acc.1 + 1, D :: upPool acc.2))) using 1
      congr 1
      funext o
      cases o <;> rfl
    simp only [Prog.exp]
    simp_rw [hstep]
    exact ih (fun acc => (G.oIter p order rank dfsFuel (upSet R) qh pools M v.val).exp noOracle
      (fun o => f (o.elim acc fun D => (acc.1 + 1, D :: acc.2))))

theorem oPhi_subtype (rank : E → ℕ) (R : Finset U) (qh : V → ℝ) (qh' : U → ℝ)
    (hqh : ∀ u, qh' u = qh u.val) :
    (G.inducedClosed U hU).oPhi (fun e => p e.val) (fun e => rank e.val) R qh' =
      G.oPhi p rank (upSet R) qh := by
  unfold oPhi
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro u hu
    have hU' : u ∉ U := fun h => hu ⟨⟨u, h⟩, rfl⟩
    have hR : u ∉ upSet R := fun h => hU' (upSet_subset R h)
    simp [hR]
  · intro u
    simp only [mem_upSet, hqh, oGamma_subtype]

private theorem map_argmax {A B : Type} (l : List A) (e : A → B) (f : B → ℝ) :
    (l.argmax (fun a => f (e a))).map e = (l.map e).argmax f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.argmax_cons, ← ih]
    cases l.argmax (fun a => f (e a)) with
    | none => rfl
    | some b => simp only [Option.map_some]; split_ifs <;> rfl

/-- The cut and its tie-breaking order survive subtype restriction exactly. -/
theorem subtype_cut_order (order : List E) (R : Finset U) :
    (((G.subtypeOrder U order).filter fun e =>
      (G.inducedClosed U hU).source e ∈ R ∧ (G.inducedClosed U hU).target e ∉ R).map Subtype.val) =
      order.filter (fun e => G.source e ∈ upSet R ∧ G.target e ∉ upSet R) := by
  induction order with
  | nil => rfl
  | cons e l ih =>
    by_cases he : G.source e ∈ U
    · have hc : decide ((G.inducedClosed U hU).source ⟨e, he⟩ ∈ R ∧
          (G.inducedClosed U hU).target ⟨e, he⟩ ∉ R) =
          decide (G.source e ∈ upSet R ∧ G.target e ∉ upSet R) := by
        simp only [inducedClosed, mem_upSet R (⟨G.source e, he⟩ : U),
          mem_upSet R (⟨G.target e, hU e he⟩ : U)]
      simp only [subtypeOrder, dite_eq_left he, List.filter_cons, hc]
      split_ifs <;> simp only [List.map_cons, ih]
    · have hr : G.source e ∉ upSet R := fun h => he (upSet_subset R h)
      simp only [subtypeOrder, dite_eq_right he, List.filter_cons, hr, false_and,
        Bool.false_eq_true, decide_false, ite_false]
      exact ih


/-- Whole-program simulation on the induced vertex and edge types. The only
choices omitted by reindexing have zero weight; fallback alternatives remain. -/
theorem oRounds_subtype (order : List E) (rank : E → ℕ) (dfsFuel : ℕ) (t : U)
    (M fuel : ℕ) (R : Finset U) (qh : V → ℝ) (qh' : U → ℝ)
    (pools : V → List (Finset V)) (pools' : U → List (Finset U))
    (hqh : ∀ u, qh' u = qh u.val) (hpools : ∀ u, pools u.val = upPool (pools' u)) (f : ℝ → ℝ) :
    ((G.inducedClosed U hU).oRounds (fun e => p e.val) (G.subtypeOrder U order)
      (fun e => rank e.val) dfsFuel t M fuel R qh' pools').exp noOracle f =
      (G.oRounds p order rank dfsFuel t.val M fuel (upSet R) qh pools).exp noOracle f := by
  induction fuel generalizing R qh qh' pools pools' with
  | zero => simp only [oRounds, Prog.exp, hqh]
  | succ fuel ih =>
    simp only [oRounds, mem_upSet]
    by_cases ht : t ∈ R
    · simp only [ht, ite_true, Prog.exp, hqh]
    · simp only [ht, ite_false]
      have hmax : (((G.subtypeOrder U order).filter fun e =>
          (G.inducedClosed U hU).source e ∈ R ∧ (G.inducedClosed U hU).target e ∉ R).argmax
          (fun e => qh' ((G.inducedClosed U hU).source e) * p e.val)).map Subtype.val =
          (order.filter fun e => G.source e ∈ upSet R ∧ G.target e ∉ upSet R).argmax
            (fun e => qh (G.source e) * p e) := by
        have hscore : (fun e : {e : E // G.source e ∈ U} =>
            qh' ((G.inducedClosed U hU).source e) * p e.val) =
            fun e => qh (G.source e.val) * p e.val := by
          funext e
          rw [hqh]
          rfl
        rw [hscore, map_argmax _ Subtype.val (fun e => qh (G.source e) * p e)]
        rw [G.subtype_cut_order U hU order R]
      rw [← hmax]
      generalize he : (((G.subtypeOrder U order).filter fun e =>
          (G.inducedClosed U hU).source e ∈ R ∧ (G.inducedClosed U hU).target e ∉ R).argmax
          (fun e => qh' ((G.inducedClosed U hU).source e) * p e.val)) = o
      cases o with
      | none => rfl
      | some e =>
        simp only [Option.map_some, Option.elim_some, hqh]
        change (if qh (G.source e.val) * p e.val ≤ 0 then Prog.ret 0 else _).exp noOracle f =
          (if qh (G.source e.val) * p e.val ≤ 0 then Prog.ret 0 else _).exp noOracle f
        split_ifs
        · rfl
        · simp only [Prog.exp_bind]
          have hcont : ∀ res : ℕ × List (Finset U),
              ((G.inducedClosed U hU).oRounds (fun e => p e.val) (G.subtypeOrder U order)
                (fun e => rank e.val) dfsFuel t M fuel
                (insert ((G.inducedClosed U hU).target e) R)
                (Function.update qh' ((G.inducedClosed U hU).target e)
                  ((G.inducedClosed U hU).oPhi (fun e => p e.val) (fun e => rank e.val) R qh' * res.1 / M))
                (Function.update pools' ((G.inducedClosed U hU).target e) res.2)).exp noOracle f =
              (G.oRounds p order rank dfsFuel t.val M fuel (insert (G.target e.val) (upSet R))
                (Function.update qh (G.target e.val) (G.oPhi p rank (upSet R) qh * res.1 / M))
                (Function.update pools (G.target e.val) (upPool res.2))).exp noOracle f := by
            intro res
            rw [G.oPhi_subtype p U hU rank R qh qh' hqh]
            simpa only [upSet_insert, inducedClosed] using
              ih (insert ((G.inducedClosed U hU).target e) R)
                (Function.update qh (G.target e.val) (G.oPhi p rank (upSet R) qh * res.1 / M))
                (Function.update qh' ((G.inducedClosed U hU).target e)
                  (G.oPhi p rank (upSet R) qh * res.1 / M))
                (Function.update pools (G.target e.val) (upPool res.2))
                (Function.update pools' ((G.inducedClosed U hU).target e) res.2)
                (by intro u; by_cases hu : u = (G.inducedClosed U hU).target e
                    · subst u; simp [inducedClosed]
                    · have hu' : u.val ≠ G.target e.val := fun h => hu (Subtype.ext h)
                      simp [Function.update_of_ne hu, Function.update_of_ne hu', hqh])
                (by intro u; by_cases hu : u = (G.inducedClosed U hU).target e
                    · subst u; simp [inducedClosed]
                    · have hu' : u.val ≠ G.target e.val := fun h => hu (Subtype.ext h)
                      simp [Function.update_of_ne hu, Function.update_of_ne hu', hpools])
          simp_rw [hcont]
          exact G.oGenerate_subtype p U hU order rank dfsFuel R qh qh' pools pools' hqh hpools
            M ((G.inducedClosed U hU).target e) M
            (fun res => (G.oRounds p order rank dfsFuel t.val M fuel
              (insert (G.target e.val) (upSet R))
              (Function.update qh (G.target e.val) (G.oPhi p rank (upSet R) qh * res.1 / M))
              (Function.update pools (G.target e.val) res.2)).exp noOracle f)

/-- Restriction to a closed set preserves the complete output law, with
actual subtype vertices and edges and the inherited arc order and ranks. -/
theorem orderedAlgS_subtype (order : List E) (rank : E → ℕ) (dfsFuel rounds : ℕ)
    (s t : U) (M : ℕ) (f : ℝ → ℝ) :
    ((G.inducedClosed U hU).orderedAlgS (fun e => p e.val) (G.subtypeOrder U order)
      (fun e => rank e.val) dfsFuel rounds s t M).exp noOracle f =
      (G.orderedAlgS p order rank dfsFuel rounds s.val t.val M).exp noOracle f := by
  have h := G.oRounds_subtype p U hU order rank dfsFuel t M rounds {s}
    (fun u => if u = s.val then 1 else 0) (fun u => if u = s then 1 else 0)
    (fun u => if u = s.val then [{s.val}] else []) (fun u => if u = s then [{s}] else [])
    (by intro u; simp)
    (by intro u; by_cases hu : u = s <;> simp [hu, upPool, upSet]) f
  simpa [orderedAlgS, upSet] using h

/-- The original exact Algorithm S is equal in law to its reindexed induced
graph version. Fuel and sample counts are explicit and unchanged. -/
theorem algS_inducedClosed (s t : U) (M : ℕ) (f : ℝ → ℝ) :
    ((G.inducedClosed U hU).orderedAlgS (fun e => p e.val) (G.subtypeOrder U (arcOrder E))
      (fun e => (arcOrder E).idxOf e.val) (Fintype.card V + 1) (Fintype.card V) s t M).exp noOracle f =
      (G.algS p s.val t.val M).exp noOracle f := by
  exact (G.orderedAlgS_subtype p U hU (arcOrder E) (fun e => (arcOrder E).idxOf e)
    (Fintype.card V + 1) (Fintype.card V) s t M f).trans
      (congrArg (fun m : Prog Empty ℝ => m.exp noOracle f) (G.orderedAlgS_canonical p s.val t.val M))

/-- In particular this applies to the actual subtype of reachable vertices. -/
theorem algS_reachable_subtype (s t : V) (ht : t ∈ G.reachableVertices s) (M : ℕ) (f : ℝ → ℝ) :
    ((G.inducedClosed (G.reachableVertices s) (G.reachableVertices_closed s)).orderedAlgS
      (fun e => p e.val) (G.subtypeOrder (G.reachableVertices s) (arcOrder E))
      (fun e => (arcOrder E).idxOf e.val) (Fintype.card V + 1) (Fintype.card V)
      ⟨s, G.source_mem_reachableVertices s⟩ ⟨t, ht⟩ M).exp noOracle f =
      (G.algS p s t M).exp noOracle f :=
  G.algS_inducedClosed p (G.reachableVertices s) (G.reachableVertices_closed s) _ _ M f

end Digraph
end
end DirectedCycleFPRAS
