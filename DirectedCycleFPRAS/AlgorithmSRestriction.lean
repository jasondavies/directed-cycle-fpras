module

public import DirectedCycleFPRAS.AlgorithmSInvariants

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false

/-- A zero weight has zero mass unless it is the fallback alternative. -/
theorem normLaw_zero {ι : Type} [Fintype ι] (w : ι → ℝ) (d i : ι)
    (hi : i ≠ d) (hw : w i = 0) : (normLaw w d).value i = 0 := by
  unfold normLaw
  split_ifs <;> simp [hw, hi]

namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E) (p : E → ℝ)

/-- Closure with a weaker stack invariant, also covering default empty pools. -/
theorem sScan_subset (U R : Finset V) (hU : ∀ e, G.source e ∈ U → G.target e ∈ U)
    (pre : E → Option Bool) (z : V) (hz : z ∈ U) (flag : Bool)
    (l : List E) (D : Finset V) (st : List (V × Bool)) (hD : D ⊆ U)
    (hst : ∀ x ∈ st, x.1 ∈ U) :
    Prog.Sat (fun _ => True) (fun _ => True)
      (fun r : Finset V × List (V × Bool) => r.1 ⊆ U ∧ ∀ x ∈ r.2, x.1 ∈ U)
      (G.sScan (Q := Empty) p R pre z flag l D st) := by
  induction l generalizing D st with
  | nil => exact .ret _ ⟨hD, hst⟩
  | cons e l ih =>
    unfold sScan
    split_ifs with he
    · refine (Prog.Sat.trivial _).bind fun o _ => ?_
      cases o with
      | false => exact ih D st hD hst
      | true =>
        apply ih
        · exact Finset.insert_subset (hU e (he.1 ▸ hz)) hD
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hU e (he.1 ▸ hz)
          · exact hst x hx
    · exact ih D st hD hst

theorem sDfs_subset (U R : Finset V) (hU : ∀ e, G.source e ∈ U → G.target e ∈ U)
    (pre : E → Option Bool) (v : V) (f : ℕ) (D : Finset V)
    (st : List (V × Bool)) (hD : D ⊆ U) (hst : ∀ x ∈ st, x.1 ∈ U) :
    Prog.Sat (fun _ => True) (fun _ => True)
      (fun o : Option (Finset V) => ∀ A ∈ o, A ⊆ U)
      (G.sDfs (Q := Empty) p R pre v f D st) := by
  induction f generalizing D st with
  | zero => exact .ret _ (by simp)
  | succ f ih =>
    cases st with
    | nil => exact .ret _ (by simp)
    | cons zf st =>
      obtain ⟨z, flag⟩ := zf
      unfold sDfs
      by_cases hz : z = v
      · simp only [hz, ite_true]
        cases flag <;> refine .ret _ ?_ <;> simp_all
      · simp only [hz, ite_false]
        apply (G.sScan_subset p U R hU pre z (hst (z, flag) (by simp)) flag
          (arcOrder E) D st hD (fun x hx => hst x (by simp [hx]))).bind
        intro r hr
        exact ih r.1 r.2 hr.1 hr.2

theorem sDfs_restrict_subset (q : E → ℝ) (U R : Finset V)
    (hU : ∀ e, G.source e ∈ U → G.target e ∈ U)
    (pre : E → Option Bool) (hpq : ∀ e, G.source e ∈ U → p e = q e)
    (v : V) (f : ℕ) (D : Finset V) (st : List (V × Bool))
    (hD : D ⊆ U) (hst : ∀ x ∈ st, x.1 ∈ U) :
    G.sDfs (Q := Empty) p R pre v f D st = G.sDfs q R pre v f D st := by
  induction f generalizing D st with
  | zero => rfl
  | succ f ih =>
    cases st with
    | nil => rfl
    | cons zf st =>
      obtain ⟨z, flag⟩ := zf
      have hz := hst (z, flag) (by simp)
      simp only [sDfs]
      by_cases hzt : z = v
      · simp only [hzt, ite_true]
      · simp only [hzt, ite_false]
        rw [← G.sScan_restrict p q U R pre pre hpq (fun _ _ => rfl) z hz flag]
        apply (G.sScan_subset p U R hU pre z hz flag (arcOrder E) D st hD
          (fun x hx => hst x (by simp [hx]))).bind_congr (fun _ => trivial)
        intro r hr
        exact ih r.1 r.2 hr.1 hr.2

theorem firstOpenWeight_restrict (q : E → ℝ) (U R : Finset V)
    (hpq : ∀ e, G.source e ∈ U → p e = q e) (u : V) (hu : u ∈ U) (e : E) :
    G.firstOpenWeight p R u e = G.firstOpenWeight q R u e := by
  unfold firstOpenWeight
  split_ifs with he
  · rw [hpq e (he.1 ▸ hu)]
    congr 1
    apply Finset.prod_congr rfl
    intro e' he'
    exact congrArg (fun x : ℝ => 1 - x) (hpq e' ((Finset.mem_filter.mp he').2.1.1 ▸ hu))
  · rfl

theorem gammaS_restrict (q : E → ℝ) (U R : Finset V)
    (hpq : ∀ e, G.source e ∈ U → p e = q e) (u : V) (hu : u ∈ U) :
    G.gammaS p R u = G.gammaS q R u := by
  unfold gammaS
  exact Finset.sum_congr rfl fun e _ => G.firstOpenWeight_restrict p q U R hpq u hu e

private theorem getD_subset (U : Finset V) (l : List (Finset V))
    (hl : ∀ D ∈ l, D ⊆ U) (i : ℕ) : l.getD i ∅ ⊆ U := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hl _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
    exact Finset.empty_subset _

/-- Every supported sample stays in a closed vertex set. Zero-weight choices
outside the resolved set are ignored, including in degenerate fallback cases. -/
theorem sIter_subset (U R : Finset V) (hU : ∀ e, G.source e ∈ U → G.target e ∈ U)
    (hR : R ⊆ U) (qh : V → ℝ) (pools : V → List (Finset V))
    (hpools : ∀ u ∈ R, ∀ D ∈ pools u, D ⊆ U) (M : ℕ) (v : V) :
    Prog.Supported (fun o : Option (Finset V) => ∀ D ∈ o, D ⊆ U)
      (G.sIter p R qh pools M v) := by
  refine .choose _ _ ?_
  intro o ho
  cases o with
  | none => exact .ret _ (by simp)
  | some u =>
    have hu : u ∈ R := by
      by_contra hu
      apply ho
      exact normLaw_zero _ none (some u) (by simp) (by simp [hu])
    refine .choose _ _ fun i _ => .choose _ _ ?_
    intro j _
    cases j with
    | none => exact .ret _ (by simp)
    | some j =>
      exact (G.sDfs_subset p U R hU _ v _ _ _
        (getD_subset U (pools u) (hpools u hu) i) (by simpa using hR hu)).supported

/-- Equality of the complete one-iteration law under changes outside U. -/
theorem sIter_restrict (q : E → ℝ) (U R : Finset V)
    (hU : ∀ e, G.source e ∈ U → G.target e ∈ U)
    (hpq : ∀ e, G.source e ∈ U → p e = q e) (hR : R ⊆ U)
    (qh : V → ℝ) (pools : V → List (Finset V))
    (hpools : ∀ u ∈ R, ∀ D ∈ pools u, D ⊆ U) (M : ℕ) (v : V)
    (f : Option (Finset V) → ℝ) :
    (G.sIter p R qh pools M v).exp noOracle f =
      (G.sIter q R qh pools M v).exp noOracle f := by
  have hw : (fun o : Option V => o.elim 0 fun u => if u ∈ R then qh u * G.gammaS p R u else 0) =
      (fun o : Option V => o.elim 0 fun u => if u ∈ R then qh u * G.gammaS q R u else 0) := by
    funext o
    cases o with
    | none => rfl
    | some u =>
      simp only [Option.elim_some]
      split_ifs with hu
      · rw [G.gammaS_restrict p q U R hpq u (hR hu)]
      · rfl
  unfold sIter
  simp only [Prog.exp]
  rw [hw]
  apply Finset.sum_congr rfl
  intro o _
  cases o with
  | none => rfl
  | some u =>
    by_cases hu : u ∈ R
    · have hew : (fun j : Option E => j.elim 0 (G.firstOpenWeight p R u)) =
          (fun j : Option E => j.elim 0 (G.firstOpenWeight q R u)) := by
        funext j
        cases j with
        | none => rfl
        | some j => exact G.firstOpenWeight_restrict p q U R hpq u (hR hu) j
      simp only [Option.elim_some, Prog.exp]
      rw [hew]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      cases j with
      | none => rfl
      | some j =>
        simp only [Option.elim_some]
        rw [G.sDfs_restrict_subset p q U R hU _ hpq v _ _ _
          (getD_subset U (pools u) (hpools u hu) i) (by simpa using hR hu)]
    · have hz := normLaw_zero (fun o : Option V => o.elim 0 fun u =>
          if u ∈ R then qh u * G.gammaS q R u else 0) none (some u) (by simp) (by simp [hu])
      simp only [hz, zero_mul]


theorem sGenerate_subset (U R : Finset V) (hU : ∀ e, G.source e ∈ U → G.target e ∈ U)
    (hR : R ⊆ U) (qh : V → ℝ) (pools : V → List (Finset V))
    (hpools : ∀ u ∈ R, ∀ D ∈ pools u, D ⊆ U) (M : ℕ) (v : V) (i : ℕ) :
    Prog.Supported (fun r : ℕ × List (Finset V) => ∀ D ∈ r.2, D ⊆ U)
      (G.sGenerate p R qh pools M v i) := by
  induction i with
  | zero => exact .ret _ (by simp)
  | succ i ih =>
    apply ih.bind
    intro acc hacc
    apply (G.sIter_subset p U R hU hR qh pools hpools M v).bind
    intro o ho
    cases o with
    | none => exact .ret _ hacc
    | some D =>
      refine .ret _ ?_
      simpa only [Option.elim_some, List.mem_cons, forall_eq_or_imp] using
        And.intro (ho D (by simp)) hacc

theorem sGenerate_restrict (q : E → ℝ) (U R : Finset V)
    (hU : ∀ e, G.source e ∈ U → G.target e ∈ U)
    (hpq : ∀ e, G.source e ∈ U → p e = q e) (hR : R ⊆ U)
    (qh : V → ℝ) (pools : V → List (Finset V))
    (hpools : ∀ u ∈ R, ∀ D ∈ pools u, D ⊆ U) (M : ℕ) (v : V) (i : ℕ)
    (f : ℕ × List (Finset V) → ℝ) :
    (G.sGenerate p R qh pools M v i).exp noOracle f =
      (G.sGenerate q R qh pools M v i).exp noOracle f := by
  induction i generalizing f with
  | zero => rfl
  | succ i ih =>
    simp only [sGenerate, Prog.exp_bind]
    simp_rw [G.sIter_restrict p q U R hU hpq hR qh pools hpools M v]
    exact ih _

private theorem argmax_congr_on {ι : Type} (l : List ι) (f g : ι → ℝ)
    (h : ∀ x ∈ l, f x = g x) : l.argmax f = l.argmax g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.argmax_cons, List.argmax_cons, ih (fun x hx => h x (by simp [hx]))]
    cases he : l.argmax g with
    | none => rfl
    | some b =>
      have hb : b ∈ l := List.argmax_mem (by rw [he]; simp)
      simp only [h a (by simp), h b (by simp [hb])]

/-- The full round law is insensitive to probabilities outside a closed set,
provided its resolved vertices and saved snapshots lie in that set. -/
theorem sRounds_restrict (q : E → ℝ) (U : Finset V)
    (hU : ∀ e, G.source e ∈ U → G.target e ∈ U)
    (hpq : ∀ e, G.source e ∈ U → p e = q e) (t : V) (M fuel : ℕ)
    (R : Finset V) (hR : R ⊆ U) (qh : V → ℝ) (pools : V → List (Finset V))
    (hpools : ∀ u ∈ R, ∀ D ∈ pools u, D ⊆ U) (f : ℝ → ℝ) :
    (G.sRounds p t M fuel R qh pools).exp noOracle f =
      (G.sRounds q t M fuel R qh pools).exp noOracle f := by
  induction fuel generalizing R qh pools f with
  | zero => rfl
  | succ fuel ih =>
    simp only [sRounds]
    by_cases ht : t ∈ R
    · simp only [ht, ite_true]
    · simp only [ht, ite_false]
      have heq := argmax_congr_on
        ((arcOrder E).filter fun e => G.source e ∈ R ∧ G.target e ∉ R)
        (fun e => qh (G.source e) * p e) (fun e => qh (G.source e) * q e) (by
          intro e he
          have hs : G.source e ∈ R := ((of_decide_eq_true (List.mem_filter.mp he).2)).1
          rw [hpq e (hR hs)])
      rw [heq]
      generalize he : (((arcOrder E).filter fun e => G.source e ∈ R ∧ G.target e ∉ R).argmax
        fun e => qh (G.source e) * q e) = o
      cases o with
      | none => rfl
      | some e =>
        have hmem := List.argmax_mem (show e ∈ (((arcOrder E).filter
          fun e => G.source e ∈ R ∧ G.target e ∉ R).argmax
          fun e => qh (G.source e) * q e) by rw [he]; simp)
        have hcut : G.source e ∈ R ∧ G.target e ∉ R := by
          simpa using (List.mem_filter.mp hmem).2
        have htarget := hU e (hR hcut.1)
        simp only [Option.elim_some, hpq e (hR hcut.1)]
        split_ifs
        · rfl
        · have hphi : G.phiS p R qh = G.phiS q R qh := by
            unfold phiS
            apply Finset.sum_congr rfl
            intro u _
            split_ifs with hu
            · rw [G.gammaS_restrict p q U R hpq u (hR hu)]
            · rfl
          rw [hphi]
          apply (G.sGenerate_subset p U R hU hR qh pools hpools M (G.target e) M).exp_bind_congr
            (G.sGenerate_restrict p q U R hU hpq hR qh pools hpools M (G.target e) M)
          intro res hres g
          apply ih (insert (G.target e) R) (Finset.insert_subset htarget hR)
          intro u hu D hD
          by_cases hue : u = G.target e
          · subst u
            rw [Function.update_self] at hD
            exact hres D hD
          · rw [Function.update_of_ne hue] at hD
            exact hpools u (Finset.mem_of_mem_insert_of_ne hu hue) D hD

/-- Algorithm S has the same output law after arbitrary changes to edges
outside a closed set containing its source. The sample budget is unchanged. -/
theorem algS_restrict (q : E → ℝ) (U : Finset V)
    (hU : ∀ e, G.source e ∈ U → G.target e ∈ U)
    (hpq : ∀ e, G.source e ∈ U → p e = q e) (s t : V) (hs : s ∈ U)
    (M : ℕ) (f : ℝ → ℝ) :
    (G.algS p s t M).exp noOracle f = (G.algS q s t M).exp noOracle f := by
  apply G.sRounds_restrict p q U hU hpq t M _ {s} (by simpa)
  intro u hu D hD
  have : u = s := by simpa using hu
  subst u
  simp only [ite_true, List.mem_singleton] at hD
  subst D
  simpa

/-- Vertices reachable from the source in the underlying directed graph. -/
def reachableVertices (s : V) : Finset V :=
  Finset.univ.filter fun v => Relation.ReflTransGen (G.Adj Set.univ) s v

theorem source_mem_reachableVertices (s : V) : s ∈ G.reachableVertices s := by
  simp only [reachableVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact .refl

theorem reachableVertices_closed (s : V) (e : E)
    (he : G.source e ∈ G.reachableVertices s) : G.target e ∈ G.reachableVertices s := by
  simp only [reachableVertices, Finset.mem_filter, Finset.mem_univ, true_and] at *
  exact he.tail ⟨e, Set.mem_univ e, rfl, rfl⟩

/-- Zeroing every edge whose source is unreachable preserves the entire
Algorithm S output law, at the same budget and in the ambient vertex type. -/
theorem algS_zero_unreachable (s t : V) (M : ℕ) (f : ℝ → ℝ) :
    (G.algS p s t M).exp noOracle f =
      (G.algS (fun e => if G.source e ∈ G.reachableVertices s then p e else 0) s t M).exp
        noOracle f := by
  exact G.algS_restrict p _ (G.reachableVertices s) (G.reachableVertices_closed s)
    (fun e he => by simp [he]) s t (G.source_mem_reachableVertices s) M f

end Digraph
end
end DirectedCycleFPRAS
