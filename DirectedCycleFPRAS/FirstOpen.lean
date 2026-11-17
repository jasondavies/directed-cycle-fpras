module

public import DirectedCycleFPRAS.AlgorithmS

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type} [Fintype E] [ArcEnumeration E] [DecidableEq E]

/-- A partial assignment of edge states. -/
def Compatible (pre : E → Option Bool) (ω : E → Bool) : Prop :=
  ∀ e b, pre e = some b → ω e = b

def forceProb (p : E → ℝ) (pre : E → Option Bool) (e : E) : ℝ :=
  (pre e).elim (p e) (fun b => if b then 1 else 0)

def cylinderWeight (p : E → ℝ) (pre : E → Option Bool) : ℝ :=
  ∏ e, (pre e).elim 1 (fun b => if b then p e else 1 - p e)

/-- The exact factorization for revealing any partial assignment. No division
or positivity assumption is needed, so zero-probability cylinders are covered. -/
theorem cylinder_factor (p : E → ℝ) (pre : E → Option Bool) (ω : E → Bool) :
    cylinderWeight p pre * edgeWeight (forceProb p pre) ω =
      if Compatible pre ω then edgeWeight p ω else 0 := by
  unfold cylinderWeight edgeWeight
  rw [← Finset.prod_mul_distrib]
  by_cases h : Compatible pre ω
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro e _
    unfold forceProb
    cases hp : pre e with
    | none => simp
    | some b =>
      have hω := h e b hp
      cases b <;> simp [hω]
  · rw [ite_eq_right h]
    have hex : ∃ e b, pre e = some b ∧ ω e ≠ b := by
      unfold Compatible at h
      push Not at h
      exact h
    obtain ⟨e, b, he, hω⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    unfold forceProb
    cases b <;> cases hw : ω e <;> simp_all

/-- The probability of a partial assignment is the product of its fixed factors. -/
theorem cylinder_mass (p : E → ℝ) (pre : E → Option Bool) :
    eventMass p (Compatible pre) = cylinderWeight p pre := by
  unfold eventMass
  simp_rw [← cylinder_factor]
  rw [← Finset.mul_sum, edgeWeight_sum, mul_one]

namespace Digraph
variable {V : Type} (G : Digraph V E) (p : E → ℝ)

/-- j is the first open outgoing cut edge at u. -/
def FirstOpen (R : Finset V) (u : V) (j : E) (ω : E → Bool) : Prop :=
  G.cutAt R u j ∧ ω j = true ∧
    ∀ e, G.cutAt R u e → arcBefore e j → ω e = false

theorem firstOpen_compatible (R : Finset V) (u : V) (j : E) (hj : G.cutAt R u j)
    (ω : E → Bool) : G.FirstOpen R u j ω ↔ Compatible (G.preState R u j) ω := by
  constructor
  · rintro ⟨_, hopen, hprior⟩ e b he
    unfold preState at he
    split_ifs at he with hc heq hbefore
    · subst e
      have hb : b = true := Option.some.inj he.symm
      simpa [hb] using hopen
    · have hb : b = false := by simpa using he.symm
      subst b
      exact hprior e hc hbefore
  · intro h
    refine ⟨hj, h j true (by simp [preState, hj]), ?_⟩
    intro e he hbefore
    have hne : e ≠ j := by intro heq; subst e; exact (Nat.lt_irrefl _) hbefore
    exact h e false (by simp [preState, he, hne, hbefore])

theorem firstOpen_cylinderWeight (R : Finset V) (u : V) (j : E) (hj : G.cutAt R u j) :
    cylinderWeight p (G.preState R u j) = G.firstOpenWeight p R u j := by
  unfold cylinderWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [preState, hj, ite_true, Option.elim_some]
  unfold firstOpenWeight
  rw [ite_eq_left hj, Finset.prod_filter]
  congr 1
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [arcBefore, Nat.lt_irrefl, and_false, ite_false, one_mul]
  apply Finset.prod_congr rfl
  intro e he
  have hne := Finset.ne_of_mem_erase he
  simp only [hne, ite_false]
  by_cases hc : G.cutAt R u e <;> by_cases ho : (arcOrder E).idxOf e < (arcOrder E).idxOf j <;>
    simp [hc, ho]

theorem firstOpen_mass (R : Finset V) (u : V) (j : E) :
    eventMass p (G.FirstOpen R u j) = G.firstOpenWeight p R u j := by
  by_cases hj : G.cutAt R u j
  · have hpred : G.FirstOpen R u j = Compatible (G.preState R u j) :=
      funext fun ω => propext (G.firstOpen_compatible R u j hj ω)
    rw [hpred, cylinder_mass, G.firstOpen_cylinderWeight p R u j hj]
  · simp [eventMass, FirstOpen, firstOpenWeight, hj]

theorem firstOpen_unique (R : Finset V) (u : V) (ω : E → Bool)
    (hout : ∃ e, G.cutAt R u e ∧ ω e = true) : ∃! j, G.FirstOpen R u j ω := by
  let S := Finset.univ.filter fun e => G.cutAt R u e ∧ ω e = true
  have hS : S.Nonempty := by obtain ⟨e, he⟩ := hout; exact ⟨e, by simpa [S] using he⟩
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image S (fun e => (arcOrder E).idxOf e) hS
  have hj' := (Finset.mem_filter.mp hj).2
  have hfirst : G.FirstOpen R u j ω := by
    refine ⟨hj'.1, hj'.2, ?_⟩
    intro e he hbefore
    cases hw : ω e with
    | false => rfl
    | true => exact False.elim ((not_lt_of_ge (hmin e (by simp [S, he, hw]))) hbefore)
  refine ⟨j, hfirst, ?_⟩
  intro e he
  have hle := hmin e (by simp [S, he.1, he.2.1])
  have heq : (arcOrder E).idxOf j = (arcOrder E).idxOf e := by
    by_contra hne
    have hlt : arcBefore j e := lt_of_le_of_ne hle hne
    have := he.2.2 j hj'.1 hlt
    simp [hj'.2] at this
  exact ((List.idxOf_inj (by simp : j ∈ arcOrder E)).mp heq).symm

/-- Mixing forced-edge product laws with the first-open weights gives exactly
the original product law restricted to the event that the cut has an open edge. -/
theorem firstOpen_mixture (R : Finset V) (u : V) (ω : E → Bool) :
    (∑ j, G.firstOpenWeight p R u j * edgeWeight (forceProb p (G.preState R u j)) ω) =
      if ∃ e, G.cutAt R u e ∧ ω e = true then edgeWeight p ω else 0 := by
  have hterm : ∀ j, G.firstOpenWeight p R u j * edgeWeight (forceProb p (G.preState R u j)) ω =
      if G.FirstOpen R u j ω then edgeWeight p ω else 0 := by
    intro j
    by_cases hj : G.cutAt R u j
    · rw [← G.firstOpen_cylinderWeight p R u j hj, cylinder_factor,
        ← G.firstOpen_compatible R u j hj ω]
    · simp [firstOpenWeight, FirstOpen, hj]
  simp_rw [hterm]
  by_cases hout : ∃ e, G.cutAt R u e ∧ ω e = true
  · rw [ite_eq_left hout]
    obtain ⟨j, hj, huniq⟩ := G.firstOpen_unique R u ω hout
    rw [Finset.sum_eq_single j]
    · exact ite_eq_left hj
    · intro e _ hne
      exact ite_eq_right (fun he => hne (huniq e he))
    · simp
  · rw [ite_eq_right hout]
    apply Finset.sum_eq_zero
    intro j _
    exact ite_eq_right (fun hj => hout ⟨j, hj.1, hj.2.1⟩)

/-- gammaS is the probability that the outgoing cut has at least one open edge. -/
theorem gammaS_eventMass (R : Finset V) (u : V) :
    G.gammaS p R u = eventMass p (fun ω => ∃ e, G.cutAt R u e ∧ ω e = true) := by
  have h := congrArg (fun f : (E → Bool) → ℝ => ∑ ω, f ω)
    (funext (G.firstOpen_mixture p R u))
  rw [Finset.sum_comm] at h
  simp only [← Finset.mul_sum, edgeWeight_sum, mul_one] at h
  refine h.trans ?_
  unfold eventMass
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> rfl

/-- Exact conditional joint law of the cut sampler, with free states drawn
independently after fixing its first open edge. -/
theorem firstOpen_conditional (R : Finset V) (u : V) (ω : E → Bool) :
    (∑ j, (G.firstOpenWeight p R u j / G.gammaS p R u) *
      edgeWeight (forceProb p (G.preState R u j)) ω) =
    condWeight p (fun ω => ∃ e, G.cutAt R u e ∧ ω e = true) ω := by
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, G.firstOpen_mixture, G.gammaS_eventMass]
  unfold condWeight
  split_ifs <;> simp

end Digraph
end
end DirectedCycleFPRAS
