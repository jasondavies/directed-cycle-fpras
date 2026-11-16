module

public import DirectedCycleFPRAS.Reliability
public import Mathlib.Combinatorics.SetFamily.FourFunctions

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type} [Fintype E] [DecidableEq E]

/-- Product Bernoulli weights are log-supermodular, including deterministic
coordinates. This is the hypothesis of the finite FKG theorem. -/
theorem edgeWeight_lattice (p : E → ℝ) (x y : E → Bool) :
    edgeWeight p x * edgeWeight p y = edgeWeight p (x ⊓ y) * edgeWeight p (x ⊔ y) := by
  classical
  unfold edgeWeight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  simp only [Pi.inf_apply, Pi.sup_apply]
  have hcoord (a b : Bool) :
      (if a then p e else 1-p e) * (if b then p e else 1-p e) =
      (if a ⊓ b then p e else 1-p e) * (if a ⊔ b then p e else 1-p e) := by
    cases a <;> cases b <;> simp [mul_comm]
  exact hcoord (x e) (y e)

/-- Harris's inequality (FFG Lemma 4) for arbitrary independent edge
probabilities in `[0,1]`. -/
theorem harris (p : E → ℝ) (hp : Prob01 p) (A B : (E → Bool) → Prop)
    (hA : Monotone A) (hB : Monotone B) :
    eventMass p A * eventMass p B ≤ eventMass p (fun x => A x ∧ B x) := by
  classical
  have indicator_mono (C : (E → Bool) → Prop) (hC : Monotone C) :
      Monotone (fun x => if C x then (1 : ℝ) else 0) := by
    classical
    intro x y hxy
    by_cases hx : C x
    · simp [hx, hC hxy hx]
    · simp only [ite_eq_right hx]; split_ifs <;> norm_num
  have h := fkg (μ := edgeWeight p) (f := fun x => if A x then (1 : ℝ) else 0)
    (g := fun x => if B x then (1 : ℝ) else 0)
    (fun x => edgeWeight_nonneg hp x)
    (fun x => by dsimp; split_ifs <;> norm_num) (fun x => by dsimp; split_ifs <;> norm_num)
    (indicator_mono A hA) (indicator_mono B hB) (fun x y => (edgeWeight_lattice p x y).le)
  rw [edgeWeight_sum, one_mul] at h
  simp only [mul_ite, mul_one, mul_zero] at h
  have he : (∑ x, if B x then if A x then edgeWeight p x else 0 else 0) =
      eventMass p (fun x => A x ∧ B x) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases ha : A x <;> by_cases hb : B x <;> simp [ha, hb]
  exact h.trans_eq he

theorem eventMass_mono (p : E → ℝ) (hp : Prob01 p) {A B : (E → Bool) → Prop}
    (h : ∀ x, A x → B x) : eventMass p A ≤ eventMass p B := by
  classical
  apply Finset.sum_le_sum
  intro x _
  by_cases ha : A x
  · simp [ha,h x ha]
  · simp only [ite_eq_right ha]
    split_ifs
    · exact edgeWeight_nonneg hp x
    · rfl

/-- The marginal of a product edge law is its retention parameter. -/
theorem eventMass_edge (p : E → ℝ) (e : E) :
    eventMass p (fun ω => ω e = true) = p e := by
  unfold eventMass
  calc
    _ = ∑ ω, p e * edgeWeight (pin p e true) ω := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [edgeWeight_eq_mul_rest p e, edgeWeight_pin]
      cases h : ω e <;> simp [h]
    _ = p e := by rw [← Finset.mul_sum, edgeWeight_sum, mul_one]

namespace Digraph
variable {V : Type} (G : Digraph V E)

theorem reachEvent_monotone (s t : V) :
    Monotone (fun ω => Relation.ReflTransGen (G.Adj (retained ω)) s t) := by
  classical
  intro x y hxy hr
  apply Relation.ReflTransGen.mono (fun _ _ h => ?_) _ _ hr
  obtain ⟨e,he,hs,ht⟩ := h
  refine ⟨e,?_,hs,ht⟩
  have hh := hxy e
  change x e = true at he
  change y e = true
  exact Bool.eq_true_of_true_le (he ▸ hh)

/-- The reliability comparison used in the record bound of FFG Lemma 11. -/
theorem reliability_mul_le (p : E → ℝ) (hp : Prob01 p) (s v w : V) :
    G.reliability p s v * G.reliability p v w ≤ G.reliability p s w := by
  classical
  exact (harris p hp _ _ (G.reachEvent_monotone s v) (G.reachEvent_monotone v w)).trans
    (eventMass_mono p hp (fun _ h => h.1.trans h.2))

/-- Appending a retained arc gives the second inequality of FFG Lemma 8.
Harris handles any overlap between the reachability event and that arc. -/
theorem reliability_arc (p : E → ℝ) (hp : Prob01 p) (s : V) (e : E) :
    G.reliability p s (G.source e) * p e ≤ G.reliability p s (G.target e) := by
  have hm : Monotone (fun ω : E → Bool => ω e = true) := by
    intro x y hxy hx
    exact Bool.eq_true_of_true_le (hx ▸ hxy e)
  have h := harris p hp _ _ (G.reachEvent_monotone s (G.source e)) hm
  rw [eventMass_edge] at h
  exact h.trans (eventMass_mono p hp fun ω h =>
    h.1.tail ⟨e, h.2, rfl, rfl⟩)

theorem reliability_le_ratio (p : E → ℝ) (hp : Prob01 p) (s v w : V)
    (hv : 0 < G.reliability p s v) :
    G.reliability p v w ≤ G.reliability p s w/G.reliability p s v := by
  classical
  apply (le_div_iff₀ hv).mpr
  simpa [mul_comm] using G.reliability_mul_le p hp s v w

end Digraph
end
end DirectedCycleFPRAS
