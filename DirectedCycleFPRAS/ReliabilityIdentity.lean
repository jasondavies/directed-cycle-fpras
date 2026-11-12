module

public import DirectedCycleFPRAS.CycleEstimator

@[expose] public section

/-! # Witness weights are edge probabilities times deleted-edge reliability -/

namespace DirectedCycleFPRAS

open scoped BigOperators
noncomputable section

variable {V E : Type} [Fintype E] [DecidableEq E]

/-- Split one edge bit from all the other independently sampled bits. -/
def assemble (e : E) (b : Bool) (ω : {f : E // f ≠ e} → Bool) : E → Bool :=
  (Equiv.funSplitAt e Bool).symm (b, ω)

omit [Fintype E] in
@[simp] theorem assemble_self (e : E) (b : Bool) (ω : {f : E // f ≠ e} → Bool) :
    assemble e b ω e = b := by simp [assemble, Equiv.funSplitAt_symm_apply]

omit [Fintype E] in
@[simp] theorem assemble_other (e : E) (b : Bool) (ω : {f : E // f ≠ e} → Bool)
    (f : {f : E // f ≠ e}) : assemble e b ω f = ω f := by
  simp [assemble, Equiv.funSplitAt_symm_apply, f.property]

/-- Factorisation of the product measure at a designated edge. -/
theorem edgeLaw_split (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (e : E) (b : Bool) (ω : {f : E // f ≠ e} → Bool) :
    (edgeLaw p hp0 hp1).value (assemble e b ω) =
      (if b then p e else 1 - p e) *
        (edgeLaw (fun f : {f : E // f ≠ e} => p f)
          (fun f => hp0 f) (fun f => hp1 f)).value ω := by
  change (∏ f, if assemble e b ω f then p f else 1 - p f) = _
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e)]
  rw [assemble_self]
  congr 1
  rw [Finset.prod_subtype (p := fun f : E => f ≠ e)
    (Finset.univ.erase e) (by simp)]
  simp only [assemble_other]
  rfl

namespace Digraph
variable (G : Digraph V E)

/-- The retained subgraph with designated edge e forced absent. -/
def restSet (e : E) (ω : {f : E // f ≠ e} → Bool) : Set E :=
  retained (assemble e false ω)

omit [Fintype E] in
theorem retained_erase (e : E) (b : Bool) (ω : {f : E // f ≠ e} → Bool) :
    retained (assemble e b ω) \ {e} = restSet e ω := by
  ext f
  by_cases hf : f = e
  · subst f
    simp [retained, restSet]
  · simp [retained, restSet, assemble, Equiv.funSplitAt_symm_apply, hf]

omit [Fintype E] in
theorem witness_assemble (e : E) (b : Bool) (ω : {f : E // f ≠ e} → Bool) :
    G.event e (assemble e b ω) ↔ b = true ∧
      Relation.ReflTransGen (G.Adj (restSet e ω)) (G.target e) (G.source e) := by
  unfold event Witness
  rw [retained_erase]
  simp only [retained, Set.mem_ofPred_eq, assemble_self]

/-- The ordinary source-to-target reliability in the graph with e deleted.
A zero-length return path handles self-loops. -/
def deletedReliability (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (e : E) : ℝ :=
  ∑ ω, @ite ℝ
    (Relation.ReflTransGen (G.Adj (restSet e ω)) (G.target e) (G.source e))
    (Classical.propDecidable _)
    ((edgeLaw (fun f : {f : E // f ≠ e} => p f)
      (fun f => hp0 f) (fun f => hp1 f)).value ω) 0

/-- The exact reliability-oracle identity used to compute each witness weight. -/
theorem weight_eq_edge_mul_reliability (p : E → ℝ)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) (e : E) :
    letI : ∀ e, DecidablePred (G.event e) := fun _ => Classical.decPred _
    (edgeLaw p hp0 hp1).toMass.weight G.event e = p e * G.deletedReliability p hp0 hp1 e := by
  classical
  unfold Mass.weight
  rw [← (Equiv.funSplitAt e Bool).symm.sum_comp
    (fun ω => if G.event e ω then (edgeLaw p hp0 hp1).value ω else 0)]
  rw [Fintype.sum_prod_type]
  change (∑ b : Bool, ∑ ω, if G.event e (assemble e b ω)
    then (edgeLaw p hp0 hp1).value (assemble e b ω) else 0) = _
  simp_rw [G.witness_assemble, edgeLaw_split]
  rw [Fintype.sum_bool]
  simp only [Bool.false_eq_true, false_and,
    true_and, ite_false, ite_true, Finset.sum_const_zero, add_zero]
  unfold deletedReliability
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

end Digraph
end
end DirectedCycleFPRAS
