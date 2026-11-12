module

public import DirectedCycleFPRAS.ReliabilityIdentity
public import DirectedCycleFPRAS.ConditionalSampler
public import DirectedCycleFPRAS.Amplification

@[expose] public section

/-!
# The oracle reduction from directed-cycle probability to reliability

This file defines the complete algorithm as a randomized oracle program whose
only queries are directed two-terminal reliability instances on the input
graph with some edge probabilities replaced by zero or one, and proves its
probabilistic correctness against a randomized reliability oracle.

* `Digraph.cycleAlgorithm` is the algorithm.
* `Digraph.cycleAlgorithm_queryBound` bounds its oracle calls by `m + 2*m*n`.
* `Digraph.cycleAlgorithm_ideal` analyses it for an oracle whose answers to
  valid queries are always accurate, but may be random.
* `Digraph.cycleAlgorithm_failure` transfers the bound to an oracle that is
  accurate only with high probability on each call, via the adaptive coupling.
* `Digraph.cycle_fpras_reduction` instantiates the sample budget and obtains
  failure probability at most 1/4.
* `Digraph.cycle_fpras_of_constant_confidence` starts from an oracle that is
  accurate only with probability 3/4 per call and amplifies it by medians.

Running time and bit complexity are not modelled; internal random choices use
exact real weights. See FORMALIZATION.md for the exact boundary.
-/

namespace DirectedCycleFPRAS

open scoped BigOperators
open Classical

noncomputable section

variable {V E : Type} [Fintype E] [DecidableEq E]

namespace Digraph

variable (G : Digraph V E)

/-- The decidability instance used by `CycleEstimator`, made available globally
so that statements here agree syntactically with the statistical theorems. -/
instance eventDecidable (e : E) : DecidablePred (G.event e) := Classical.decPred _

/-! ## Reliability and the return-path event -/

/-- Directed two-terminal reliability: the probability that `t` is reachable
from `s` when edges are retained independently with probabilities `q`. -/
def reliability (q : E → ℝ) (s t : V) : ℝ :=
  eventMass q (fun ω => Relation.ReflTransGen (G.Adj (retained ω)) s t)

/-- The target of `e` returns to its source without using `e`. -/
def returnEvent (e : E) (ω : E → Bool) : Prop :=
  Relation.ReflTransGen (G.Adj (retained ω \ {e})) (G.target e) (G.source e)

omit [Fintype E] [DecidableEq E] in
theorem event_iff (e : E) (ω : E → Bool) :
    G.event e ω ↔ ω e = true ∧ G.returnEvent e ω := Iff.rfl

omit [Fintype E] in
theorem retained_update_diff (e : E) (ω : E → Bool) (b : Bool) :
    retained (Function.update ω e b) \ {e} = retained ω \ {e} := by
  ext f
  by_cases h : f = e
  · subst h
    simp
  · simp [retained, h]

omit [Fintype E] in
theorem returnEvent_update (e : E) (ω : E → Bool) (b : Bool) :
    G.returnEvent e (Function.update ω e b) ↔ G.returnEvent e ω := by
  unfold returnEvent
  rw [retained_update_diff]

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

/-- The return-path probability is a reliability instance on the same graph
with the probability of `e` set to zero, for arbitrary parameters. -/
theorem eventMass_returnEvent (q : E → ℝ) (e : E) :
    eventMass q (G.returnEvent e) =
      G.reliability (pin q e false) (G.target e) (G.source e) := by
  rw [← eventMass_pin_indep q e false (G.returnEvent e) (G.returnEvent_update e)]
  unfold reliability eventMass
  apply Finset.sum_congr rfl
  intro ω _
  rw [edgeWeight_pin]
  cases h : ω e
  · have hs : retained ω \ {e} = retained ω := by
      ext f
      by_cases hf : f = e
      · subst hf
        simp [retained, h]
      · simp [hf]
    unfold returnEvent
    rw [hs]
  · simp

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

/-! ## Witness weights and conditional laws in pinned form -/

theorem event_term (p : E → ℝ) (e : E) (ω : E → Bool) :
    (if G.event e ω then edgeWeight p ω else 0) =
      p e * (if G.returnEvent e ω then edgeWeight (pin p e true) ω else 0) := by
  rw [edgeWeight_pin, edgeWeight_eq_mul_rest p e]
  simp only [G.event_iff]
  cases h : ω e <;> by_cases hr : G.returnEvent e ω <;> simp [hr]

theorem weight_eq_pinned (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) (e : E) :
    (edgeLaw p hp0 hp1).toMass.weight G.event e =
      p e * eventMass (pin p e true) (G.returnEvent e) := by
  unfold Mass.weight eventMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  exact G.event_term p e ω

/-- Conditioning on witness `e` is the same as fixing `e` present and
conditioning the remaining product law on the return path. -/
theorem conditional_eq_condWeight (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (e : E) (hw : 0 < (edgeLaw p hp0 hp1).toMass.weight G.event e) (ω : E → Bool) :
    (edgeLaw p hp0 hp1).toMass.conditional G.event e ω =
      condWeight (pin p e true) (G.returnEvent e) ω := by
  have hpe : p e ≠ 0 := by
    intro hz
    rw [G.weight_eq_pinned, hz, zero_mul] at hw
    exact lt_irrefl _ hw
  unfold Mass.conditional condWeight
  rw [G.weight_eq_pinned]
  change (if G.event e ω then edgeWeight p ω else 0) / _ = _
  rw [G.event_term, mul_div_mul_left _ _ hpe]

/-! ## Reliability queries -/

/-- A reliability instance on the fixed graph: edge probabilities and terminals. -/
abbrev Query (V E : Type) := (E → ℝ) × V × V

/-- The exact answer to a query. -/
def exact (x : Query V E) : ℝ := G.reliability x.1 x.2.1 x.2.2

/-- The exact positivity test performed before a call. -/
def Feasible (x : Query V E) : Prop :=
  Relation.ReflTransGen (G.Adj {f | 0 < x.1 f}) x.2.1 x.2.2

/-- Relative accuracy of an answer. -/
def Accurate (α : ℝ) (x : Query V E) (r : ℝ) : Prop := |r - G.exact x| ≤ α * G.exact x

/-- The query for the return-path probability of `e`: delete `e` by giving it
probability zero and ask for reliability from its target to its source. -/
def returnQuery (q : E → ℝ) (e : E) : Query V E := (pin q e false, G.target e, G.source e)

theorem exact_returnQuery (q : E → ℝ) (e : E) :
    G.exact (G.returnQuery q e) = eventMass q (G.returnEvent e) :=
  (G.eventMass_returnEvent q e).symm

theorem feasible_iff {x : Query V E} (hx : Prob01 x.1) : G.Feasible x ↔ 0 < G.exact x :=
  (G.reliability_pos_iff hx _ _).symm

/-- The exact answer to the return query is the deleted-edge reliability of
`ReliabilityIdentity`: deleting an edge and giving it probability zero are the
same reliability instance. -/
theorem deletedReliability_eq_exact (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (e : E) : G.deletedReliability p hp0 hp1 e = G.exact (G.returnQuery p e) := by
  change _ = eventMass (pin p e false)
    (fun ω => Relation.ReflTransGen (G.Adj (retained ω)) (G.target e) (G.source e))
  unfold eventMass deletedReliability
  rw [← (Equiv.funSplitAt e Bool).symm.sum_comp
    (fun ω => if Relation.ReflTransGen (G.Adj (retained ω)) (G.target e) (G.source e)
      then edgeWeight (pin p e false) ω else 0)]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  change _ = (∑ ω, if Relation.ReflTransGen (G.Adj (retained (assemble e true ω)))
        (G.target e) (G.source e) then edgeWeight (pin p e false) (assemble e true ω) else 0) +
      ∑ ω, if Relation.ReflTransGen (G.Adj (retained (assemble e false ω)))
        (G.target e) (G.source e) then edgeWeight (pin p e false) (assemble e false ω) else 0
  have hrest : ∀ ω : {f : E // f ≠ e} → Bool,
      restWeight p e (assemble e false ω) =
        (edgeLaw (fun f : {f : E // f ≠ e} => p f) (fun f => hp0 f) (fun f => hp1 f)).value ω := by
    intro ω
    unfold restWeight
    rw [Finset.prod_subtype (p := fun f : E => f ≠ e) (Finset.univ.erase e) (by simp)]
    simp only [assemble_other]
    rfl
  simp only [edgeWeight_pin, assemble_self, Bool.true_eq_false, ite_false, zero_mul, ite_self,
    Finset.sum_const_zero, zero_add, ite_true, one_mul, hrest]
  rfl

/-- Each witness weight is the edge probability times the exact answer to the
corresponding oracle query. -/
theorem weight_eq_edge_mul_exact (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (e : E) :
    (edgeLaw p hp0 hp1).toMass.weight G.event e = p e * G.exact (G.returnQuery p e) := by
  rw [← G.deletedReliability_eq_exact p hp0 hp1 e]
  exact G.weight_eq_edge_mul_reliability p hp0 hp1 e

end Digraph

/-- Residual parameters: every edge keeps its input probability or is pinned
to zero or one. Residual instances therefore have no new numerical data. -/
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

namespace Digraph

variable (G : Digraph V E) (p : E → ℝ)

/-- Queries on which the oracle is required to be accurate: residual
instances of the input with positive reliability. -/
def Valid (x : Query V E) : Prop := Derived p x.1 ∧ 0 < G.exact x

/-- An answer is acceptable if it is accurate whenever the query is valid. -/
def Good (α : ℝ) (x : Query V E) (r : ℝ) : Prop := G.Valid p x → G.Accurate α x r

/-- A guarded answer is accurate, including the exact zero of an infeasible query. -/
theorem guarded_accurate (hp : Prob01 p) (O : Oracle (Query V E)) {α : ℝ}
    (hO : ∀ x s, G.Good p α x (O.answer x s)) (x : Query V E) (hx : Derived p x.1)
    (s : O.Seed) :
    |(if G.Feasible x then O.answer x s else 0) - G.exact x| ≤ α * G.exact x := by
  have hx01 : Prob01 x.1 := derived_prob01 hp hx
  by_cases hf : G.Feasible x
  · rw [ite_eq_left hf]
    exact hO x s ⟨hx, (G.feasible_iff hx01).mp hf⟩
  · have hnn : 0 ≤ G.exact x := eventMass_nonneg hx01 _
    have hz : G.exact x = 0 :=
      le_antisymm (not_lt.mp fun h => hf ((G.feasible_iff hx01).mpr h)) hnn
    rw [ite_eq_right hf, hz]
    simp

/-! ## The algorithm -/

/-- Estimate all witness weights `p e * Rel(G - e, target e, source e)`. -/
def initWeights : List E → (E → ℝ) → Prog (Query V E) (E → ℝ)
  | [], acc => .ret acc
  | e :: l, acc =>
    Prog.guarded (G.Feasible (G.returnQuery p e)) (G.returnQuery p e) fun r =>
      initWeights l (Function.update acc e (p e * r))

/-- Sample conditionally on witness `e`: fix `e` present and expose every edge. -/
def sampleWitness (bits : ℕ) (e : E) : Prog (Query V E) (E → Bool) :=
  expose bits (fun q => G.returnQuery q e) (fun q => G.Feasible (G.returnQuery q e))
    Finset.univ.toList (pin p e true)

/-- One draw from the approximate witness mixture, using `bits` random bits
for the witness and for each exposed edge. With unusable weights the fallback
is the empty outcome, whose score is zero. -/
def sampler (bits : ℕ) (w : E → ℝ) : Prog (Query V E) (E → Bool) :=
  Prog.draw bits (normLaw (fun o : Option E => o.elim 0 w) none) fun o =>
    o.elim (.ret fun _ => false) (G.sampleWitness p bits)

/-- Local operations charged for the final aggregation: one witness test per
sample and edge, and the two sums. -/
def aggregationWork (m n : ℕ) : ℕ := n * m + n + m

/-- The complete algorithm with `n` samples and `bits` random bits per
discrete choice. It returns zero without any oracle call when the
positive-probability support is acyclic. -/
def cycleAlgorithm (bits n : ℕ) : Prog (Query V E) ℝ :=
  if G.Cyclic {e | 0 < p e} then
    (G.initWeights p Finset.univ.toList fun _ => 0).bind fun w =>
      ((G.sampler p bits w).replicate n).bind fun xs =>
        .work (aggregationWork (Fintype.card E) n)
          (.ret ((∑ e, w e) * Law.sampleAverage (Mass.score G.event) n xs))
  else .ret 0

/-! ## Oracle-call and random-bit budgets -/

omit [Fintype E] in
theorem initWeights_queryBound (l : List E) (acc : E → ℝ) :
    Prog.QueryBound (G.initWeights p l acc) l.length := by
  induction l generalizing acc with
  | nil => exact .ret _ _
  | cons e l ih => exact Prog.QueryBound.guarded fun r => ih _

omit [Fintype E] in
theorem initWeights_bitBound (bits : ℕ) (l : List E) (acc : E → ℝ) :
    Prog.BitBound bits (G.initWeights p l acc) 0 := by
  induction l generalizing acc with
  | nil => exact .ret _ _
  | cons e l ih => exact Prog.BitBound.guarded fun r => ih _

theorem sampler_queryBound (bits : ℕ) (w : E → ℝ) :
    Prog.QueryBound (G.sampler p bits w) (2 * Fintype.card E) := by
  have hbr : ∀ o : Option E, Prog.QueryBound
      (o.elim (Prog.ret fun _ => false) (G.sampleWitness p bits)) (2 * Fintype.card E) := by
    intro o
    cases o with
    | none => exact .ret _ _
    | some e =>
      have h := expose_queryBound bits (fun q => G.returnQuery q e)
        (fun q => G.Feasible (G.returnQuery q e)) Finset.univ.toList (pin p e true)
      rw [Finset.length_toList, Finset.card_univ] at h
      exact h
  exact Prog.QueryBound.draw hbr

theorem sampler_bitBound (bits : ℕ) (w : E → ℝ) :
    Prog.BitBound bits (G.sampler p bits w) (Fintype.card E + 1) := by
  refine Prog.BitBound.ofDraw fun o => ?_
  cases o with
  | none => exact .ret _ _
  | some e =>
    have h := expose_bitBound bits (fun q => G.returnQuery q e)
      (fun q => G.Feasible (G.returnQuery q e)) Finset.univ.toList (pin p e true)
    rw [Finset.length_toList, Finset.card_univ] at h
    exact h

/-- At most `m + 2*m*n` oracle calls on every execution path. -/
theorem cycleAlgorithm_queryBound (bits n : ℕ) :
    Prog.QueryBound (G.cycleAlgorithm p bits n)
      (Fintype.card E + n * (2 * Fintype.card E)) := by
  unfold cycleAlgorithm
  split_ifs
  · have hinit := G.initWeights_queryBound p Finset.univ.toList fun _ => 0
    rw [Finset.length_toList, Finset.card_univ] at hinit
    have hrep : ∀ w, Prog.QueryBound
        (((G.sampler p bits w).replicate n).bind fun xs =>
          Prog.work (aggregationWork (Fintype.card E) n)
            (Prog.ret ((∑ e, w e) * Law.sampleAverage (Mass.score G.event) n xs)))
        (n * (2 * Fintype.card E)) := by
      intro w
      have h := ((G.sampler_queryBound p bits w).replicate n).bind
        (g := fun xs => Prog.work (aggregationWork (Fintype.card E) n)
          (Prog.ret ((∑ e, w e) * Law.sampleAverage (Mass.score G.event) n xs)))
        (b := 0) fun xs => .work _ _ _ (.ret _ _)
      simpa using h
    exact hinit.bind hrep
  · exact .ret _ _

/-- All internal randomness consists of at most `n * (m + 1)` uniform draws of
`bits` random bits each, on every execution path. -/
theorem cycleAlgorithm_bitBound (bits n : ℕ) :
    Prog.BitBound bits (G.cycleAlgorithm p bits n) (n * (Fintype.card E + 1)) := by
  unfold cycleAlgorithm
  split_ifs
  · have hinit := G.initWeights_bitBound p bits Finset.univ.toList fun _ => 0
    have hrep : ∀ w, Prog.BitBound bits
        (((G.sampler p bits w).replicate n).bind fun xs =>
          Prog.work (aggregationWork (Fintype.card E) n)
            (Prog.ret ((∑ e, w e) * Law.sampleAverage (Mass.score G.event) n xs)))
        (n * (Fintype.card E + 1)) := by
      intro w
      have h := ((G.sampler_bitBound p bits w).replicate n).bind
        (g := fun xs => Prog.work (aggregationWork (Fintype.card E) n)
          (Prog.ret ((∑ e, w e) * Law.sampleAverage (Mass.score G.event) n xs)))
        (d := 0) fun xs => .work _ _ _ (.ret _ _)
      simpa using h
    simpa using hinit.bind hrep
  · exact .ret _ _

/-! ## Analysis with an always-accurate randomized oracle -/

section Ideal

variable (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) (O : Oracle (Query V E)) {α : ℝ}

include hp0 hp1 in
/-- Every weight vector produced by the initial phase is accurate. -/
theorem exp_initWeights_le (hO : ∀ x s, G.Good p α x (O.answer x s))
    (g : (E → ℝ) → ℝ) (c : ℝ)
    (hg : ∀ w : E → ℝ,
      (∀ e, |w e - (edgeLaw p hp0 hp1).toMass.weight G.event e| ≤
        α * (edgeLaw p hp0 hp1).toMass.weight G.event e) → g w ≤ c)
    (l : List E) (acc : E → ℝ)
    (hacc : ∀ e, e ∉ l → |acc e - (edgeLaw p hp0 hp1).toMass.weight G.event e| ≤
      α * (edgeLaw p hp0 hp1).toMass.weight G.event e) :
    (G.initWeights p l acc).exp O g ≤ c := by
  have hp : Prob01 p := fun e => ⟨hp0 e, hp1 e⟩
  induction l generalizing acc with
  | nil => exact hg acc fun e => hacc e (by simp)
  | cons e l ih =>
    change (Prog.guarded _ _ _).exp O g ≤ c
    rw [Prog.exp_guarded]
    have hbound : ∀ s : O.Seed,
        (G.initWeights p l (Function.update acc e (p e *
          (if G.Feasible (G.returnQuery p e) then O.answer (G.returnQuery p e) s else 0)))).exp
          O g ≤ c := by
      intro s
      apply ih
      intro e' he'
      by_cases hee : e' = e
      · subst hee
        have h := G.guarded_accurate p hp O hO (G.returnQuery p e')
          (derived_pin (derived_self p) e' false) s
        rw [G.exact_returnQuery,
          ← eventMass_pin_indep p e' true (G.returnEvent e') (G.returnEvent_update e')] at h
        rw [Function.update_self, G.weight_eq_pinned, ← mul_sub, abs_mul,
          abs_of_nonneg (hp0 e')]
        calc p e' * |_ - _| ≤ p e' * (α * eventMass (pin p e' true) (G.returnEvent e')) :=
              mul_le_mul_of_nonneg_left h (hp0 e')
          _ = α * (p e' * eventMass (pin p e' true) (G.returnEvent e')) := by ring
      · rw [Function.update_of_ne hee]
        exact hacc e' (by simp [hee, he'])
    calc _ ≤ ∑ s, (O.law (G.returnQuery p e)).value s * c :=
          Finset.sum_le_sum fun s _ =>
            mul_le_mul_of_nonneg_left (hbound s) ((O.law _).nonneg s)
      _ = c := by rw [← Finset.sum_mul, Law.sum_one, one_mul]

/-- The conditional sampler for a positive-weight witness is within
`4 * α + 2 / 2^bits` per edge of the exact conditional law. -/
theorem sampleWitness_l1 (bits : ℕ) (hp : Prob01 p)
    (hO : ∀ x s, G.Good p α x (O.answer x s))
    (hα0 : 0 ≤ α) (hα : α ≤ 1 / 2) (e : E)
    (hpos : 0 < eventMass (pin p e true) (G.returnEvent e)) :
    l1 ((G.sampleWitness p bits e).law O).value
        (condWeight (pin p e true) (G.returnEvent e)) ≤
      Fintype.card E * (4 * α + 2 / (2 : ℝ) ^ bits) := by
  have h := expose_l1 bits O (G.returnEvent e) (fun q => G.returnQuery q e)
    (fun q => G.Feasible (G.returnQuery q e)) (Derived p) hα0 hα
    (fun q hq => derived_prob01 hp hq) (fun q f b hq => derived_pin hq f b)
    (fun q hq => by
      rw [G.feasible_iff (x := G.returnQuery q e)
        (prob01_pin (derived_prob01 hp hq) e false), G.exact_returnQuery])
    (fun q hq hq' s => by
      have h := hO (G.returnQuery q e) s
        ⟨derived_pin hq e false, by rw [G.exact_returnQuery]; exact hq'⟩
      unfold Accurate at h
      rwa [G.exact_returnQuery] at h)
    Finset.univ.toList (pin p e true) (derived_pin (derived_self p) e true) hpos
    (fun e' he' => absurd (Finset.mem_toList.mpr (Finset.mem_univ e')) he')
  rw [Finset.length_toList, Finset.card_univ] at h
  exact h

include hp0 hp1 in
/-- The sampling program is close to the ideal witness mixture, for every
accurate weight vector and averaged over oracle seeds and random bits. The
error is `4 * (m + 1) * α` from the oracle and `(3 * m + 1) / 2^bits` from
rounding the `m + 1` discrete choices. -/
theorem sampler_l1 (bits : ℕ) (hO : ∀ x s, G.Good p α x (O.answer x s))
    (hα0 : 0 ≤ α) (hα : α ≤ 1 / 2) (w : E → ℝ)
    (hW : 0 < (edgeLaw p hp0 hp1).toMass.totalWeight G.event)
    (hw : ∀ e, |w e - (edgeLaw p hp0 hp1).toMass.weight G.event e| ≤
      α * (edgeLaw p hp0 hp1).toMass.weight G.event e) :
    l1 ((G.sampler p bits w).law O).value ((edgeLaw p hp0 hp1).toMass.mixture G.event) ≤
      (4 * α + (Fintype.card E + 1) / (2 : ℝ) ^ bits) +
        Fintype.card E * (4 * α + 2 / (2 : ℝ) ^ bits) := by
  have hp : Prob01 p := fun e => ⟨hp0 e, hp1 e⟩
  set μ := (edgeLaw p hp0 hp1).toMass with hμ
  have hwt0 : ∀ e, 0 ≤ μ.weight G.event e := μ.weight_nonneg G.event
  -- Exact and estimated selection weights, extended by a null fallback alternative.
  let aopt : Option E → ℝ := fun o => o.elim 0 fun e => μ.weight G.event e
  let bopt : Option E → ℝ := fun o => o.elim 0 w
  have ha0 : ∀ o, 0 ≤ aopt o := by
    intro o
    cases o with
    | none => exact le_refl _
    | some e => exact hwt0 e
  have hasum : ∑ o, aopt o = μ.totalWeight G.event := by
    rw [Fintype.sum_option]
    simp only [aopt, Option.elim_none, Option.elim_some, zero_add]
    rfl
  have hapos : 0 < ∑ o, aopt o := hasum ▸ hW
  have hest : ∀ o, |bopt o - aopt o| ≤ α * aopt o := by
    intro o
    cases o with
    | none => simp [aopt, bopt]
    | some e => exact hw e
  have hlow : ∀ o, (1 - α) * aopt o ≤ bopt o := by
    intro o
    have := (abs_le.mp (hest o)).1
    linarith
  have hb0 : ∀ o, 0 ≤ bopt o := fun o => (mul_nonneg (by linarith) (ha0 o)).trans (hlow o)
  have hbpos : 0 < ∑ o, bopt o := by
    have hle : (1 - α) * ∑ o, aopt o ≤ ∑ o, bopt o := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun o _ => hlow o
    have : 0 < (1 - α) * ∑ o, aopt o := mul_pos (by linarith) hapos
    linarith
  have hnorm := normalised_weights_l1 aopt bopt ha0 hα0 hα hapos hest
  have hval : (normLaw bopt none).value = fun o => bopt o / ∑ j, bopt j :=
    funext (normLaw_value bopt none hb0 hbpos)
  have hsel : l1 (bitLaw bits (normLaw bopt none)).value (fun o => aopt o / ∑ j, aopt j) ≤
      4 * α + (Fintype.card E + 1) / (2 : ℝ) ^ bits := by
    have hbit := bitLaw_l1 bits (normLaw bopt none)
    rw [Fintype.card_option] at hbit
    have h2 : l1 (normLaw bopt none).value (fun o => aopt o / ∑ j, aopt j) ≤ 4 * α := by
      rw [hval]
      exact hnorm
    have htri := l1_triangle (bitLaw bits (normLaw bopt none)).value
      (normLaw bopt none).value (fun o => aopt o / ∑ j, aopt j)
    push_cast at hbit
    linarith
  have hlaw : ((G.sampler p bits w).law O).value = fun ω =>
      ∑ o, (bitLaw bits (normLaw bopt none)).value o *
        ((o.elim (Prog.ret fun _ => false) (G.sampleWitness p bits)).law O).value ω := by
    ext ω
    simp only [Prog.law, sampler, Prog.exp_draw]
    rfl
  have hmix : μ.mixture G.event = fun ω =>
      ∑ o : Option E, (aopt o / ∑ j, aopt j) *
        (o.elim (fun _ => 0) fun e => μ.conditional G.event e) ω := by
    ext ω
    rw [μ.mixture_eq_conditioned_sum G.event hW ω, Fintype.sum_option, hasum]
    simp [aopt]
  rw [hlaw, hmix]
  apply l1_mixture_le (fun o => (bitLaw bits (normLaw bopt none)).value o)
    (fun o => aopt o / ∑ j, aopt j)
    (fun o => ((o.elim (Prog.ret fun _ => false) (G.sampleWitness p bits)).law O).value)
    (fun o => o.elim (fun _ => 0) fun e => μ.conditional G.event e)
  · exact fun o x => Mass.nonneg _ x
  · exact fun o => Law.sum_one _
  · exact fun o => div_nonneg (ha0 o) hapos.le
  · rw [← Finset.sum_div, div_self (ne_of_gt hapos)]
  · exact hsel
  · intro o ho
    cases o with
    | none =>
      simp [aopt] at ho
    | some e =>
      have hwe : 0 < μ.weight G.event e := by
        by_contra h
        have hz : μ.weight G.event e = 0 := le_antisymm (not_lt.mp h) (hwt0 e)
        simp only [aopt, Option.elim_some, hz, zero_div] at ho
        exact lt_irrefl _ ho
      have hpos : 0 < eventMass (pin p e true) (G.returnEvent e) := by
        by_contra h
        have hz : eventMass (pin p e true) (G.returnEvent e) = 0 :=
          le_antisymm (not_lt.mp h) (eventMass_nonneg (prob01_pin hp e true) _)
        rw [hμ, G.weight_eq_pinned, hz, mul_zero] at hwe
        exact lt_irrefl _ hwe
      have hcond : μ.conditional G.event e = condWeight (pin p e true) (G.returnEvent e) :=
        funext (G.conditional_eq_condWeight p hp0 hp1 e hwe)
      change l1 ((G.sampleWitness p bits e).law O).value (μ.conditional G.event e) ≤ _
      rw [hcond]
      exact G.sampleWitness_l1 p O bits hp hO hα0 hα e hpos

/-- Failure probability of the algorithm with an oracle whose answers to valid
queries are always within relative error `ε / (128 * m * (m + 1))`. The oracle
may be randomized and is called adaptively; only Chebyshev's inequality over
the independent samples remains. -/
theorem cycleAlgorithm_ideal {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {bits n : ℕ} (hn : 0 < n)
    (hbits : (3 * Fintype.card E + 1) / (2 : ℝ) ^ bits ≤ ε / (32 * Fintype.card E))
    (hO : ∀ x s,
      G.Good p (ε / (128 * Fintype.card E * (Fintype.card E + 1))) x (O.answer x s)) :
    (G.cycleAlgorithm p bits n).exp O (fun z =>
        if ε * G.cycleMass (edgeLaw p hp0 hp1).toMass <
          |z - G.cycleMass (edgeLaw p hp0 hp1).toMass| then 1 else 0) ≤
      1 / ((n : ℝ) * (ε / (16 * Fintype.card E)) ^ 2) := by
  set μ := (edgeLaw p hp0 hp1).toMass with hμ
  have hbound0 : (0 : ℝ) ≤ 1 / ((n : ℝ) * (ε / (16 * Fintype.card E)) ^ 2) := by positivity
  unfold cycleAlgorithm
  by_cases hc : G.Cyclic {e | 0 < p e}
  · rw [ite_eq_left hc]
    have hZ : 0 < G.cycleMass μ := (G.cycleMass_pos_iff p hp0 hp1).mpr hc
    have hW : 0 < μ.totalWeight G.event := by
      have h := μ.unionMass_le_totalWeight G.event
      rw [← G.cycleMass_eq_unionMass μ] at h
      exact lt_of_lt_of_le hZ h
    have hm : 0 < Fintype.card E := by
      by_contra h
      have hz : Fintype.card E = 0 := Nat.eq_zero_of_not_pos h
      have hb := μ.totalWeight_le_card_mul_unionMass G.event
      rw [hz, Nat.cast_zero, zero_mul] at hb
      exact absurd hW (not_lt.mpr hb)
    have hm' : (1 : ℝ) ≤ Fintype.card E := by exact_mod_cast hm
    set α := ε / (128 * (Fintype.card E : ℝ) * (Fintype.card E + 1)) with hαdef
    have hden : 0 < 128 * (Fintype.card E : ℝ) * (Fintype.card E + 1) := by positivity
    have hα0 : 0 ≤ α := by positivity
    have hαε : α ≤ ε / 256 := by
      have h256 : (256 : ℝ) ≤ 128 * (Fintype.card E : ℝ) * (Fintype.card E + 1) := by nlinarith
      rw [hαdef]
      exact div_le_div_of_nonneg_left hε.le (by norm_num) h256
    have hα : α ≤ 1 / 2 := by linarith
    have hsum : (4 * α + (Fintype.card E + 1) / (2 : ℝ) ^ bits) +
        Fintype.card E * (4 * α + 2 / (2 : ℝ) ^ bits) ≤ ε / (16 * Fintype.card E) := by
      have h1 : 4 * α + Fintype.card E * (4 * α) = ε / (32 * Fintype.card E) := by
        rw [hαdef]
        field_simp
        ring
      have h2 : ((Fintype.card E : ℝ) + 1) / (2 : ℝ) ^ bits +
          Fintype.card E * (2 / (2 : ℝ) ^ bits) =
            (3 * Fintype.card E + 1) / (2 : ℝ) ^ bits := by ring
      have h3 : ε / (32 * (Fintype.card E : ℝ)) + ε / (32 * Fintype.card E) =
          ε / (16 * Fintype.card E) := by
        field_simp
        ring
      linarith
    rw [Prog.exp_bind]
    apply G.exp_initWeights_le p hp0 hp1 O hO _ _ _ _ _
      (fun e he => absurd (Finset.mem_toList.mpr (Finset.mem_univ e)) he)
    intro w hw
    rw [Prog.exp_bind, Prog.exp_replicate]
    have hwW : |(∑ e, w e) - μ.totalWeight G.event| ≤ (ε / 4) * μ.totalWeight G.event := by
      have h1 : |(∑ e, w e) - μ.totalWeight G.event| ≤ α * μ.totalWeight G.event := by
        unfold Mass.totalWeight
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => hw e)
      have h2 : α * μ.totalWeight G.event ≤ (ε / 4) * μ.totalWeight G.event :=
        mul_le_mul_of_nonneg_right (by linarith) hW.le
      exact h1.trans h2
    have hl1 : l1 ((G.sampler p bits w).law O).value (μ.mixture G.event) ≤
        ε / (16 * Fintype.card E) :=
      (G.sampler_l1 p hp0 hp1 O bits hO hα0 hα w hW hw).trans hsum
    have key := G.cycle_estimator_bound p hp0 hp1 ((G.sampler p bits w).law O)
      (w := ∑ e, w e) hε hε1 hn hW hwW hl1
    refine le_trans (le_of_eq ?_) key
    apply Finset.sum_congr rfl
    intro xs _
    simp only [Prog.exp]
    split_ifs <;> simp
  · rw [ite_eq_right hc]
    have hZ : G.cycleMass μ = 0 := by
      have hnn : 0 ≤ G.cycleMass μ := by
        rw [G.cycleMass_eq_unionMass μ]
        exact μ.unionMass_nonneg G.event
      exact le_antisymm (not_lt.mp fun h => hc ((G.cycleMass_pos_iff p hp0 hp1).mp h)) hnn
    simp only [Prog.exp, hZ]
    simpa using hbound0

end Ideal

/-! ## The reduction theorem -/

/-- **Probabilistic correctness of the reduction.** Let the oracle answer each
valid reliability query (a residual instance with positive reliability) within
relative error `ε / (128 * m * (m + 1))` except with probability at most `γ`,
using fresh randomness on each call, and let `bits` be large enough that
`(3 * m + 1) / 2^bits ≤ ε / (32 * m)`. Then the algorithm with `n` samples has
relative error more than `ε` with probability at most the Chebyshev term plus
`(m + 2*m*n) * γ`. The hypothesis on `bits` forces `m ≥ 1`; the edgeless case
is `cycleAlgorithm_no_edges`. Exactness of the zero case is the separate
theorem `cycleAlgorithm_of_cycleMass_eq_zero`. No independence is assumed
after conditioning on oracle successes. -/
theorem cycleAlgorithm_failure (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (O : Oracle (Query V E)) {ε γ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hγ0 : 0 ≤ γ)
    {bits n : ℕ} (hn : 0 < n)
    (hbits : (3 * Fintype.card E + 1) / (2 : ℝ) ^ bits ≤ ε / (32 * Fintype.card E))
    (hO : ∀ x, G.Valid p x →
      (∑ s, if G.Accurate (ε / (128 * Fintype.card E * (Fintype.card E + 1))) x (O.answer x s)
        then 0 else (O.law x).value s) ≤ γ) :
    (G.cycleAlgorithm p bits n).exp O (fun z =>
        if ε * G.cycleMass (edgeLaw p hp0 hp1).toMass <
          |z - G.cycleMass (edgeLaw p hp0 hp1).toMass| then 1 else 0) ≤
      1 / ((n : ℝ) * (ε / (16 * Fintype.card E)) ^ 2) +
        ((Fintype.card E + n * (2 * Fintype.card E) : ℕ) : ℝ) * γ := by
  set α := ε / (128 * (Fintype.card E : ℝ) * (Fintype.card E + 1)) with hαdef
  have hα0 : 0 ≤ α := by positivity
  have hfix : ∀ x, G.Good p α x (G.exact x) := by
    intro x hx
    unfold Accurate
    rw [sub_self, abs_zero]
    exact mul_nonneg hα0 hx.2.le
  have hγ : ∀ x, (∑ s, if G.Good p α x (O.answer x s) then 0 else (O.law x).value s) ≤ γ := by
    intro x
    by_cases hx : G.Valid p x
    · refine le_trans (Finset.sum_le_sum fun s _ => ?_) (hO x hx)
      by_cases ha : G.Accurate α x (O.answer x s)
      · have hg : G.Good p α x (O.answer x s) := fun _ => ha
        rw [ite_eq_left hg, ite_eq_left ha]
      · rw [ite_eq_right ha]
        split_ifs
        · exact (O.law x).nonneg s
        · exact le_refl _
    · have hall : ∀ s, G.Good p α x (O.answer x s) := fun s h => absurd h hx
      simp only [hall, ite_true, Finset.sum_const_zero]
      exact hγ0
  have hcouple := Prog.exp_le_repair O (G.Good p α) G.exact hγ0 hγ
    (f := fun z => if ε * G.cycleMass (edgeLaw p hp0 hp1).toMass <
      |z - G.cycleMass (edgeLaw p hp0 hp1).toMass| then (1 : ℝ) else 0)
    (fun z => by split_ifs <;> norm_num) (fun z => by split_ifs <;> norm_num)
    (G.cycleAlgorithm_queryBound p bits n)
  have hideal := G.cycleAlgorithm_ideal p hp0 hp1 (O.repair (G.Good p α) G.exact) hε hε1 hn
    hbits (O.repair_good (G.Good p α) G.exact hfix)
  linarith

end Digraph

/-- Constant-confidence sample budget for the full reduction; the Chebyshev
failure term is at most 1/8. -/
def reductionBudget (m : ℕ) (ε : ℝ) : ℕ := ⌈2048 * (m : ℝ) ^ 2 / ε ^ 2⌉₊

theorem reductionBudget_pos {m : ℕ} {ε : ℝ} (hm : 0 < m) (hε : 0 < ε) :
    0 < reductionBudget m ε := by
  unfold reductionBudget
  apply Nat.ceil_pos.mpr
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  positivity

theorem reductionBudget_failure {m : ℕ} {ε : ℝ} (hm : 0 < m) (hε : 0 < ε) :
    1 / ((reductionBudget m ε : ℝ) * (ε / (16 * m)) ^ 2) ≤ 1 / 8 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hbound := Nat.le_ceil (2048 * (m : ℝ) ^ 2 / ε ^ 2)
  change 2048 * (m : ℝ) ^ 2 / ε ^ 2 ≤ (reductionBudget m ε : ℝ) at hbound
  have hmult := mul_le_mul_of_nonneg_right hbound (sq_nonneg (ε / (16 * m)))
  have heq : (2048 * (m : ℝ) ^ 2 / ε ^ 2) * (ε / (16 * m)) ^ 2 = 8 := by
    field_simp
    norm_num
  rw [heq] at hmult
  have hden : 0 < (reductionBudget m ε : ℝ) * (ε / (16 * m)) ^ 2 := by linarith
  apply (div_le_iff₀ hden).mpr
  linarith

/-- Random bits per discrete choice: logarithmic in `m` and `1/ε`. -/
def bitBudget (m : ℕ) (ε : ℝ) : ℕ := Nat.clog 2 ⌈32 * (m : ℝ) * (3 * m + 1) / ε⌉₊

theorem bitBudget_spec {m : ℕ} {ε : ℝ} (hm : 0 < m) (hε : 0 < ε) :
    (3 * (m : ℝ) + 1) / (2 : ℝ) ^ bitBudget m ε ≤ ε / (32 * m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : 32 * (m : ℝ) * (3 * m + 1) / ε ≤ (⌈32 * (m : ℝ) * (3 * m + 1) / ε⌉₊ : ℝ) :=
    Nat.le_ceil _
  have h2 : ⌈32 * (m : ℝ) * (3 * m + 1) / ε⌉₊ ≤ 2 ^ bitBudget m ε :=
    Nat.le_pow_clog (by norm_num) _
  have h2' : (⌈32 * (m : ℝ) * (3 * m + 1) / ε⌉₊ : ℝ) ≤ (2 : ℝ) ^ bitBudget m ε := by
    exact_mod_cast h2
  have h3 := h1.trans h2'
  rw [div_le_iff₀ hε] at h3
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

namespace Digraph

variable (G : Digraph V E) (p : E → ℝ)

/-- With no edges the algorithm returns exactly zero, which is correct. -/
theorem cycleAlgorithm_no_edges (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (O : Oracle (Query V E)) (ε : ℝ) (bits n : ℕ) (hm : ¬ 0 < Fintype.card E) :
    (G.cycleAlgorithm p bits n).exp O (fun z =>
        if ε * G.cycleMass (edgeLaw p hp0 hp1).toMass <
          |z - G.cycleMass (edgeLaw p hp0 hp1).toMass| then 1 else 0) = 0 := by
  have hE : IsEmpty E := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hm)
  have hc : ¬ G.Cyclic {e | 0 < p e} := by
    rintro ⟨v, hv⟩
    obtain ⟨u, ⟨e, -⟩, -⟩ := Relation.TransGen.head'_iff.mp hv
    exact hE.elim e
  have hZ : G.cycleMass (edgeLaw p hp0 hp1).toMass = 0 := by
    have hnn : 0 ≤ G.cycleMass (edgeLaw p hp0 hp1).toMass := by
      rw [G.cycleMass_eq_unionMass]
      exact Mass.unionMass_nonneg _ G.event
    exact le_antisymm (not_lt.mp fun h => hc ((G.cycleMass_pos_iff p hp0 hp1).mp h)) hnn
  unfold cycleAlgorithm
  rw [ite_eq_right hc]
  simp only [Prog.exp, hZ]
  norm_num

/-- **The zero case is exact.** If the cycle probability is zero, the
algorithm is literally the program that returns 0: it makes no oracle call and
uses no randomness, whatever the oracle. -/
theorem cycleAlgorithm_of_cycleMass_eq_zero (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (bits n : ℕ) (hZ : G.cycleMass (edgeLaw p hp0 hp1).toMass = 0) :
    G.cycleAlgorithm p bits n = .ret 0 := by
  have hc : ¬ G.Cyclic {e | 0 < p e} := by
    intro hc
    have hpos := (G.cycleMass_pos_iff p hp0 hp1).mpr hc
    rw [hZ] at hpos
    exact lt_irrefl _ hpos
  unfold cycleAlgorithm
  rw [ite_eq_right hc]

/-- **The reduction with explicit budgets.** With
`n = ⌈2048 * m^2 / ε^2⌉` samples, `bitBudget m ε` random bits per discrete
choice and at most `T = m + 2*m*n` oracle calls, if each call on a valid query
has relative error more than `ε / (128 * m * (m + 1))` with probability at most
`γ`, where `T * γ ≤ 1/8`, then the output has relative error at most `ε` except
with probability at most 1/4. When the cycle probability is zero the output is
exactly zero by `cycleAlgorithm_of_cycleMass_eq_zero`. -/
theorem cycle_fpras_reduction (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (O : Oracle (Query V E)) {ε γ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hγ0 : 0 ≤ γ)
    (hγ : ((Fintype.card E + reductionBudget (Fintype.card E) ε * (2 * Fintype.card E) : ℕ) : ℝ)
      * γ ≤ 1 / 8)
    (hO : ∀ x, G.Valid p x →
      (∑ s, if G.Accurate (ε / (128 * Fintype.card E * (Fintype.card E + 1))) x (O.answer x s)
        then 0 else (O.law x).value s) ≤ γ) :
    (G.cycleAlgorithm p (bitBudget (Fintype.card E) ε)
        (reductionBudget (Fintype.card E) ε)).exp O (fun z =>
        if ε * G.cycleMass (edgeLaw p hp0 hp1).toMass <
          |z - G.cycleMass (edgeLaw p hp0 hp1).toMass| then 1 else 0) ≤ 1 / 4 := by
  by_cases hm : 0 < Fintype.card E
  · have h := G.cycleAlgorithm_failure p hp0 hp1 O hε hε1 hγ0
      (reductionBudget_pos hm hε) (bitBudget_spec hm hε) hO
    have hb := reductionBudget_failure hm hε
    linarith
  · rw [G.cycleAlgorithm_no_edges p hp0 hp1 O ε _ _ hm]
    norm_num

/-- Relative accuracy is an interval condition on the answer. -/
theorem accurate_interval (α : ℝ) (x : Query V E) (a b c : ℝ)
    (ha : G.Accurate α x a) (hc : G.Accurate α x c) (hab : a ≤ b) (hbc : b ≤ c) :
    G.Accurate α x b := by
  unfold Accurate at *
  rw [abs_le] at *
  exact ⟨by linarith [ha.1], by linarith [hc.2]⟩

/-- **The reduction from a constant-confidence reliability oracle.** Suppose
each oracle call on a valid residual instance has relative error at most
`ε / (128 * m * (m + 1))` with probability at least 3/4, using fresh randomness.
Run the algorithm with `n = ⌈2048 * m^2 / ε^2⌉` samples and `bitBudget m ε`
random bits per discrete choice, answering each of its at most
`T = m + 2*m*n` queries by the median of `6 * ⌈log₂ (8 * T)⌉` independent
oracle calls. Then the output has relative error at most `ε` except with
probability at most 1/4. When the cycle probability is zero the output is
exactly zero by `cycleAlgorithm_of_cycleMass_eq_zero`. -/
theorem cycle_fpras_of_constant_confidence (hp0 : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1) (O : Oracle (Query V E)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hO : ∀ x, G.Valid p x →
      (∑ s, if G.Accurate (ε / (128 * Fintype.card E * (Fintype.card E + 1))) x (O.answer x s)
        then 0 else (O.law x).value s) ≤ 1 / 4) :
    (G.cycleAlgorithm p (bitBudget (Fintype.card E) ε)
        (reductionBudget (Fintype.card E) ε)).exp
        (O.amplify (amplifyRounds (Fintype.card E +
          reductionBudget (Fintype.card E) ε * (2 * Fintype.card E))))
        (fun z =>
          if ε * G.cycleMass (edgeLaw p hp0 hp1).toMass <
            |z - G.cycleMass (edgeLaw p hp0 hp1).toMass| then 1 else 0) ≤ 1 / 4 := by
  apply G.cycle_fpras_reduction p hp0 hp1 _ hε hε1
    (γ := (7 / 8 : ℝ) ^ amplifyRounds (Fintype.card E +
      reductionBudget (Fintype.card E) ε * (2 * Fintype.card E)))
    (by positivity) (amplifyRounds_bound _)
  intro x hx
  exact O.amplify_failure _ x (G.accurate_interval _ x) (hO x hx)

/-! ## The hypotheses are satisfiable -/

/-- The deterministic oracle returning the exact reliability. -/
def exactOracle : Oracle (Query V E) where
  Seed := Unit
  law _ := { value := fun _ => 1, nonneg := fun _ => zero_le_one, sum_one := by simp }
  answer x _ := G.exact x

/-- Sanity check that the oracle contract is not vacuous: the exact oracle
meets it, so the algorithm run with exact reliabilities succeeds with
probability at least 3/4. -/
theorem cycleAlgorithm_exactOracle (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (G.cycleAlgorithm p (bitBudget (Fintype.card E) ε)
        (reductionBudget (Fintype.card E) ε)).exp G.exactOracle (fun z =>
        if ε * G.cycleMass (edgeLaw p hp0 hp1).toMass <
          |z - G.cycleMass (edgeLaw p hp0 hp1).toMass| then 1 else 0) ≤ 1 / 4 := by
  apply G.cycle_fpras_reduction p hp0 hp1 G.exactOracle hε hε1 (γ := 0) (le_refl _)
    (by norm_num)
  intro x hx
  have hacc : ∀ s : G.exactOracle.Seed, G.Accurate
      (ε / (128 * Fintype.card E * (Fintype.card E + 1))) x (G.exactOracle.answer x s) := by
    intro s
    change |G.exact x - G.exact x| ≤ _
    rw [sub_self, abs_zero]
    exact mul_nonneg (by positivity) hx.2.le
  simp only [hacc, ite_true, Finset.sum_const_zero]
  exact le_refl _

end Digraph
end
end DirectedCycleFPRAS
