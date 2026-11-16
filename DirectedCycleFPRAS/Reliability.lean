module

public import DirectedCycleFPRAS.ProductLaw
public import DirectedCycleFPRAS.Amplification

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
variable {V E : Type} [Fintype E] [DecidableEq E]
namespace Digraph
variable (G : Digraph V E)

/-- Directed two-terminal reliability: the probability that `t` is reachable
from `s` when edges are retained independently with probabilities `q`. -/
def reliability (q : E → ℝ) (s t : V) : ℝ :=
  eventMass q (fun ω => Relation.ReflTransGen (G.Adj (retained ω)) s t)

/-- Exact positivity test for reliability: reachability in the support. -/
theorem reliability_pos_iff {q : E → ℝ} (hq : Prob01 q) (s t : V) :
    0 < G.reliability q s t ↔ Relation.ReflTransGen (G.Adj {e | 0 < q e}) s t := by
  unfold reliability
  rw [eventMass_pos_iff hq]
  · have hs : retained (support q) = {e | 0 < q e} := by
      ext e
      simp [retained, support]
    rw [hs]
  · intro ω ω' h hr
    exact Relation.ReflTransGen.mono
      (fun _ _ ⟨f, hf, hs, ht⟩ => ⟨f, h f hf, hs, ht⟩) _ _ hr

/-- The cycle probability is the mass of a monotone event. -/
theorem cycleMass_eq_eventMass (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) :
    G.cycleMass (edgeLaw p hp0 hp1).toMass = eventMass p (fun ω => G.Cyclic (retained ω)) :=
  rfl

/-- The zero case: the cycle probability is positive exactly when the
positive-probability support contains a directed cycle. -/
theorem cycleMass_pos_iff (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) :
    0 < G.cycleMass (edgeLaw p hp0 hp1).toMass ↔ G.Cyclic {e | 0 < p e} := by
  rw [cycleMass_eq_eventMass, eventMass_pos_iff (fun e => ⟨hp0 e, hp1 e⟩)]
  · have hs : retained (support p) = {e | 0 < p e} := by
      ext e
      simp [retained, support]
    rw [hs]
  · rintro ω ω' h ⟨v, hv⟩
    exact ⟨v, Relation.TransGen.mono (fun _ _ ⟨f, hf, hs, ht⟩ => ⟨f, h f hf, hs, ht⟩) _ _ hv⟩
/-- A reliability instance on the fixed graph: edge probabilities and terminals. -/
abbrev Query (V E : Type) := (E → ℝ) × V × V

end Digraph

def Derived (p q : E → ℝ) : Prop := ∀ e, q e = p e ∨ q e = 0 ∨ q e = 1

omit [Fintype E] [DecidableEq E] in
theorem derived_self (p : E → ℝ) : Derived p p := fun _ => Or.inl rfl

omit [Fintype E] in
theorem derived_pin {p q : E → ℝ} (h : Derived p q) (f : E) (b : Bool) :
    Derived p (pin q f b) := by
  intro e
  by_cases he : e = f
  · subst he
    rw [pin_self]
    cases b <;> simp
  · rw [pin_of_ne q b he]
    exact h e

omit [Fintype E] [DecidableEq E] in
theorem derived_prob01 {p q : E → ℝ} (hp : Prob01 p) (h : Derived p q) : Prob01 q := by
  intro e
  rcases h e with h | h | h <;> rw [h]
  · exact hp e
  · norm_num
  · norm_num


end
end DirectedCycleFPRAS
