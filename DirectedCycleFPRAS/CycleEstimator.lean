module

public import DirectedCycleFPRAS.Estimator
public import DirectedCycleFPRAS.GraphWitness

@[expose] public section

/-! # Specialisation to independently retained directed edges -/

namespace DirectedCycleFPRAS

open scoped BigOperators
noncomputable section

variable {V E : Type} [Fintype E] [DecidableEq E]

/-- Independent edge retention, including probabilities zero and one. -/
def edgeLaw (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) : Law (E → Bool) where
  value ω := ∏ e, if ω e then p e else 1 - p e
  nonneg ω := by
    apply Finset.prod_nonneg
    intro e _
    split_ifs
    · exact hp0 e
    · exact sub_nonneg.mpr (hp1 e)
  sum_one := by
    classical
    rw [← Fintype.prod_sum (fun (e : E) (b : Bool) => if b then p e else 1 - p e)]
    apply Finset.prod_eq_one
    intro e _
    simp

namespace Digraph

variable (G : Digraph V E)

/-- The retained-edge subset encoded by an assignment of Boolean edge bits. -/
def retained (ω : E → Bool) : Set E := {e | ω e = true}

/-- The edge-indexed witness family on the finite outcome space. -/
def event (e : E) (ω : E → Bool) : Prop := G.Witness (retained ω) e

/-- Probability/mass of a cyclic subgraph, with a graph-theoretic definition. -/
def cycleMass (μ : Mass (E → Bool)) : ℝ :=
  ∑ ω, @ite ℝ (G.Cyclic (retained ω)) (Classical.propDecidable _) (μ.value ω) 0

/-- The generic union mass is exactly the directed-cycle probability. -/
theorem cycleMass_eq_unionMass (μ : Mass (E → Bool)) :
    G.cycleMass μ = @Mass.unionMass _ _ _ _ μ G.event (fun _ => Classical.decPred _) := by
  classical
  apply Finset.sum_congr rfl
  intro ω _
  have heq : G.Cyclic (retained ω) ↔ 0 < Mass.multiplicity G.event ω := by
    rw [Mass.multiplicity_pos_iff]
    exact G.cyclic_iff_exists_witness _
  simp only [heq]

/-- The proved robust estimator bound specialised to the actual independent-edge
model. The approximate sampling law and weight estimate remain explicit inputs. -/
theorem cycle_estimator_bound
    (pEdge : E → ℝ) (hp0 : ∀ e, 0 ≤ pEdge e) (hp1 : ∀ e, pEdge e ≤ 1)
    (pSample : Law (E → Bool)) {w ε : ℝ} {n : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hn : 0 < n) :
    let μ := (edgeLaw pEdge hp0 hp1).toMass
    letI : ∀ e, DecidablePred (G.event e) := fun _ => Classical.decPred _
    0 < μ.totalWeight G.event →
    |w - μ.totalWeight G.event| ≤ (ε / 4) * μ.totalWeight G.event →
    l1 pSample.value (μ.mixture G.event) ≤ ε / (16 * Fintype.card E) →
    (∑ xs, if ε * G.cycleMass μ <
        |w * Law.sampleAverage (Mass.score G.event) n xs - G.cycleMass μ|
      then (pSample.samples n).value xs else 0) ≤
      1 / ((n : ℝ) * (ε / (16 * Fintype.card E))^2) := by
  classical
  intro μ hW hw hs
  rw [G.cycleMass_eq_unionMass]
  exact approximate_mixture_estimator μ G.event pSample hW hε hε1 hn hw hs

/-- The explicit independent-edge estimator has success probability at least
3/4 when its weight estimate and sampling law meet the displayed contracts. -/
theorem cycle_estimator_success
    (pEdge : E → ℝ) (hp0 : ∀ e, 0 ≤ pEdge e) (hp1 : ∀ e, pEdge e ≤ 1)
    (pSample : Law (E → Bool)) {w ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let μ := (edgeLaw pEdge hp0 hp1).toMass
    letI : ∀ e, DecidablePred (G.event e) := fun _ => Classical.decPred _
    0 < μ.totalWeight G.event →
    |w - μ.totalWeight G.event| ≤ (ε / 4) * μ.totalWeight G.event →
    l1 pSample.value (μ.mixture G.event) ≤ ε / (16 * Fintype.card E) →
    (∑ xs, if ε * G.cycleMass μ <
        |w * Law.sampleAverage (Mass.score G.event)
          (sampleBudget (Fintype.card E) ε) xs - G.cycleMass μ|
      then (pSample.samples (sampleBudget (Fintype.card E) ε)).value xs else 0) ≤ 1 / 4 := by
  classical
  intro μ hW hw hs
  rw [G.cycleMass_eq_unionMass]
  exact approximate_mixture_success μ G.event pSample hW hε hε1 hw hs

end Digraph
end
end DirectedCycleFPRAS
