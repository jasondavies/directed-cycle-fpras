module

public import DirectedCycleFPRAS.RationalAlgorithmS
public import DirectedCycleFPRAS.AlgorithmSAccuracy

@[expose] public section

/-! Accuracy of executable rational Algorithm S with an explicitly supplied
arc order. Order validity is checked by ordinary list predicates; no equality
with a noncomputable canonical enumeration is needed. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E)

/-- Theorem 9 holds for every duplicate-free complete arc order. -/
theorem orderedAlgS_accuracy (p : E → ℝ) (hp : Prob01 p)
    (order : List E) (hnodup : order.Nodup) (hcomplete : ∀ e, e∈order)
    (s t : V) {M : ℕ} (hM : 0<M) (hq : 0<G.reliability p s t)
    {α δ : ℝ} (hα : 0<α)
    (hgrowth : 2*(Fintype.card V : ℝ)^2*Fintype.card E≤M)
    (hbudget : 2*(Fintype.card V : ℝ)^3*Fintype.card E≤δ*α^2*M) :
    (G.orderedAlgS p order (fun e => order.idxOf e) (Fintype.card V+1)
      (Fintype.card V) s t M).exp noOracle
      (fun z => if |z-G.reliability p s t|≤α*G.reliability p s t then 0 else 1) ≤ δ := by
  let : ArcEnumeration E := ⟨order,hnodup,hcomplete⟩
  change (G.orderedAlgS p (arcOrder E) (fun e => (arcOrder E).idxOf e)
    (Fintype.card V+1) (Fintype.card V) s t M).exp noOracle _ ≤ δ
  rw [G.orderedAlgS_canonical]
  exact G.algS_accuracy p hp s t hM hq hα hgrowth hbudget

/-- Constant-confidence exact accuracy on an arbitrary complete arc order. -/
theorem orderedAlgS_constant_accuracy (p : E → ℝ) (hp : Prob01 p)
    (order : List E) (hnodup : order.Nodup) (hcomplete : ∀ e, e∈order)
    (s t : V) (hq : 0<G.reliability p s t) {α : ℝ} (hα : 0<α) (hα1 : α≤1) :
    (G.orderedAlgS p order (fun e => order.idxOf e) (Fintype.card V+1)
      (Fintype.card V) s t (algSSamples (Fintype.card V) (Fintype.card E) α)).exp noOracle
      (fun z => if |z-G.reliability p s t|≤α*G.reliability p s t then 0 else 1) ≤ 1/8 := by
  let : ArcEnumeration E := ⟨order,hnodup,hcomplete⟩
  change (G.orderedAlgS p (arcOrder E) (fun e => (arcOrder E).idxOf e)
    (Fintype.card V+1) (Fintype.card V) s t _).exp noOracle _ ≤ 1/8
  rw [G.orderedAlgS_canonical]
  by_cases hst : s=t
  · subst t
    have hret : G.algS (Q := Empty) p s s (algSSamples (Fintype.card V) (Fintype.card E) α) = .ret 1 := by
      unfold algS
      cases Fintype.card V <;> simp [sRounds]
    rw [hret,G.reliability_self]
    simp [Prog.exp,hα.le]
  · have hn : 0<Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
    have hm : 0<Fintype.card E := by
      have hpath := (G.reliability_pos_iff hp s t).mp hq
      apply Fintype.card_pos_iff.mpr
      rcases Relation.ReflTransGen.cases_tail hpath with heq | ⟨u,_,hedge⟩
      · exact False.elim (hst heq.symm)
      · obtain ⟨e,_,_,_⟩ := hedge
        exact ⟨e⟩
    have hM : 0<algSSamples (Fintype.card V) (Fintype.card E) α := by
      have hb : 16*(Fintype.card V : ℝ)^3*Fintype.card E/α^2 ≤
          algSSamples (Fintype.card V) (Fintype.card E) α := Nat.le_ceil _
      have hr : (0 : ℝ)<algSSamples (Fintype.card V) (Fintype.card E) α :=
        lt_of_lt_of_le (by positivity) hb
      exact_mod_cast hr
    have hb := Prog.algSSamples_bounds hn (le_refl (Fintype.card V)) (le_refl (Fintype.card E)) hα hα1
    exact G.algS_accuracy p hp s t hM hq hα hb.1 hb.2

/-- Rounding error composes with Theorem 9 for the compiled rational program. -/
theorem rationalAlgS_accuracy (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ)))
    {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (hnodup : order.Nodup) (hcomplete : ∀ e, e∈order)
    (s t : V) {M : ℕ} (hM : 0<M) (b : ℕ)
    (hq : 0<G.reliability (fun e => (p e : ℝ)) s t)
    {α δ : ℝ} (hα : 0<α)
    (hgrowth : 2*(Fintype.card V : ℝ)^2*Fintype.card E≤M)
    (hbudget : 2*(Fintype.card V : ℝ)^3*Fintype.card E≤δ*α^2*M) :
    ((G.rationalAlgS p vertices edges order (fun e => order.idxOf e) s t M).compile b).toProg.exp noOracle
      (fun z => if |(z : ℝ)-G.reliability (fun e => (p e : ℝ)) s t|≤
        α*G.reliability (fun e => (p e : ℝ)) s t then 0 else 1) ≤
      δ+(algSChoices n m M : ℝ)/(2 : ℝ)^b := by
  have he : order.toFinset = Finset.univ := by ext e; simp [hcomplete e]
  have hlen : order.length=m := by
    have hm : Fintype.card E=m := by simpa using (Fintype.card_congr edges).symm
    rw [← List.toFinset_card_of_nodup hnodup,he,Finset.card_univ,hm]
  let f := fun z : ℝ => if |z-G.reliability (fun e => (p e : ℝ)) s t|≤
    α*G.reliability (fun e => (p e : ℝ)) s t then (0 : ℝ) else 1
  have hc := G.rationalAlgS_compile_error p vertices edges order (fun e => order.idxOf e) s t M b hlen f
    (fun x => by dsimp [f]; split_ifs <;> norm_num)
    (fun x => by dsimp [f]; split_ifs <;> norm_num)
  have ha := G.orderedAlgS_accuracy (fun e => (p e : ℝ)) hp order hnodup hcomplete
    s t hM hq hα hgrowth hbudget
  have hupper := (abs_le.mp hc).2
  change _ ≤ δ+_
  dsimp [f] at hupper
  linarith

/-- Equal terminals return one before making any rational random choice. -/
theorem rationalAlgS_self (p : E → ℚ) {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (rank : E → ℕ) (s : V) (M : ℕ) :
    G.rationalAlgS p vertices edges order rank s s M = .ret 1 := by
  unfold rationalAlgS
  cases Fintype.card V <;> simp [rRounds]

/-- The compiled rational Algorithm S meets the constant-confidence reliability
contract for every supplied complete arc order, at the paper's budgets. -/
theorem rationalAlgS_constant_accuracy (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ)))
    {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (hnodup : order.Nodup) (hcomplete : ∀ e, e∈order)
    (s t : V) (hq : 0<G.reliability (fun e => (p e : ℝ)) s t)
    {α : ℝ} (hα : 0<α) (hα1 : α≤1) :
    let M := algSSamples n m α
    ((G.rationalAlgS p vertices edges order (fun e => order.idxOf e) s t M).compile
      (algSBits n m M)).toProg.exp noOracle
      (fun z => if |(z : ℝ)-G.reliability (fun e => (p e : ℝ)) s t|≤
        α*G.reliability (fun e => (p e : ℝ)) s t then 0 else 1) ≤ 1/4 := by
  dsimp only
  by_cases hst : s=t
  · subst t
    rw [G.rationalAlgS_self,G.reliability_self]
    simp [RatProg.compile,BitProg.toProg,Prog.exp,hα.le]
  · have hncard : Fintype.card V=n := by simpa using (Fintype.card_congr vertices).symm
    have hmcard : Fintype.card E=m := by simpa using (Fintype.card_congr edges).symm
    have hn : 0<Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
    have hm : 0<Fintype.card E := by
      have hpath := (G.reliability_pos_iff hp s t).mp hq
      apply Fintype.card_pos_iff.mpr
      rcases Relation.ReflTransGen.cases_tail hpath with heq | ⟨u,_,hedge⟩
      · exact False.elim (hst heq.symm)
      · obtain ⟨e,_,_,_⟩ := hedge
        exact ⟨e⟩
    have hM : 0<algSSamples n m α := by
      have hb : 16*(n : ℝ)^3*m/α^2 ≤ algSSamples n m α := Nat.le_ceil _
      have hn' : 0<n := hncard ▸ hn
      have hm' : 0 < m := hmcard ▸ hm
      have hr : (0 : ℝ)<algSSamples n m α := lt_of_lt_of_le (by positivity) hb
      exact_mod_cast hr
    have hb := Prog.algSSamples_bounds hn (le_refl (Fintype.card V)) (le_refl (Fintype.card E)) hα hα1
    rw [hncard,hmcard] at hb
    have h := G.rationalAlgS_accuracy p hp vertices edges order hnodup hcomplete s t hM
      (algSBits n m (algSSamples n m α)) hq hα
      (by simpa only [hncard,hmcard] using hb.1)
      (by simpa only [hncard,hmcard] using hb.2)
    have hbits := algSBits_spec n m (algSSamples n m α)
    linarith

/-- The exact nominal rational program has failure at most one eighth. -/
theorem rationalAlgS_nominal_accuracy (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ)))
    {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (hnodup : order.Nodup) (hcomplete : ∀ e, e∈order)
    (s t : V) (hq : 0<G.reliability (fun e => (p e : ℝ)) s t)
    {α : ℝ} (hα : 0<α) (hα1 : α≤1) :
    let M := algSSamples n m α
    (G.rationalAlgS p vertices edges order (fun e => order.idxOf e) s t M).nominal.exp noOracle
      (fun z => if |(z : ℝ)-G.reliability (fun e => (p e : ℝ)) s t|≤
        α*G.reliability (fun e => (p e : ℝ)) s t then 0 else 1) ≤ 1/8 := by
  dsimp only
  have hn : Fintype.card V=n := by simpa using (Fintype.card_congr vertices).symm
  have hm : Fintype.card E=m := by simpa using (Fintype.card_congr edges).symm
  rw [G.rationalAlgS_law p vertices edges order (fun e => order.idxOf e) s t _
    (fun z => if |z-G.reliability (fun e => (p e : ℝ)) s t|≤
      α*G.reliability (fun e => (p e : ℝ)) s t then 0 else 1)]
  have h := G.orderedAlgS_constant_accuracy (fun e => (p e : ℝ)) hp order hnodup hcomplete s t hq hα hα1
  simpa only [hn,hm] using h

end Digraph
end
end DirectedCycleFPRAS
