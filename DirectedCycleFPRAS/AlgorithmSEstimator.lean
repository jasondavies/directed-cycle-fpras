module

public import DirectedCycleFPRAS.AlgorithmS
public import DirectedCycleFPRAS.PositiveOracle

@[expose] public section

set_option linter.unusedSectionVars false

/-! The discretized Algorithm S reliability estimator. Its accuracy is
conditional on the explicit external hypothesis `AlgSAccurate`; its finite
randomness and rational output bounds are proved here. -/

namespace DirectedCycleFPRAS

open scoped BigOperators
open Classical

noncomputable section

/-- The oracle for programs that make no calls. -/
def noOracle : Oracle Empty where
  Seed _ := Unit
  law x := x.elim
  answer x := x.elim

/-- The law on a one-point space. -/
def unitLaw : Law Unit where
  value _ := 1
  nonneg _ := zero_le_one
  sum_one := by simp

/-- Choose an index, then a seed of the corresponding law. -/
def Law.sigma {ι : Type} [Fintype ι] (p : Law ι) {S : ι → Type} [∀ i, Fintype (S i)]
    (L : ∀ i, Law (S i)) : Law (Σ i, S i) where
  value z := p.value z.1 * (L z.1).value z.2
  nonneg z := mul_nonneg (p.nonneg _) ((L z.1).nonneg _)
  sum_one := by
    rw [Fintype.sum_sigma]
    have hi : ∀ i, (∑ y : S i, p.value i * (L i).value y) = p.value i := by
      intro i
      rw [← Finset.mul_sum, (L i).sum_one, mul_one]
    exact (Finset.sum_congr rfl fun i _ => hi i).trans p.sum_one

namespace Prog

/-- The finite randomized real computed by a program without oracle calls:
a seed is a sequence of outcomes of its random choices. -/
def toRand : Prog Empty ℝ → RandReal
  | .ret a => { Seed := Unit, law := unitLaw, value := fun _ => a }
  | .query x _ => x.elim
  | @Prog.choose _ _ ι _ p k =>
    { Seed := Σ i : ι, (toRand (k i)).Seed
      law := p.sigma fun i => (toRand (k i)).law
      value := fun z => (toRand (k z.1)).value z.2 }
  | .work _ m => toRand m

/-- The randomized real has the law of the program's result. -/
theorem exp_eq_toRand (O : Oracle Empty) (m : Prog Empty ℝ) (f : ℝ → ℝ) :
    m.exp O f = ∑ z, m.toRand.law.value z * f (m.toRand.value z) := by
  induction m with
  | ret a =>
    change f a = ∑ _z : Unit, (1 : ℝ) * f a
    simp
  | query x k ih => exact x.elim
  | @choose ι _ p k ih =>
    change (∑ i, p.value i * (k i).exp O f) =
      ∑ z : (Σ i : ι, (toRand (k i)).Seed),
        (p.value z.1 * (toRand (k z.1)).law.value z.2) * f ((toRand (k z.1)).value z.2)
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    rw [ih i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  | work c m ih => exact ih

/-- Every value of the randomized real is a possible result of the program. -/
theorem toRand_value_of_sat {R : ℝ → Prop} {m : Prog Empty ℝ}
    (h : Sat (fun _ => True) (fun _ => True) R m) (z : m.toRand.Seed) :
    R (m.toRand.value z) := by
  induction h with
  | ret a ha => exact ha
  | query x k _ _ _ => exact x.elim
  | choose p k _ ih => exact ih z.1 z.2
  | work c m _ ih => exact ih z

end Prog

/-- Samples per round: the paper's `M = ⌈2 n³ m / (ε² δ)⌉` at `δ = 1/8`. -/
def algSSamples (n m : ℕ) (α : ℝ) : ℕ := ⌈16 * (n : ℝ) ^ 3 * m / α ^ 2⌉₊

/-- Random bits per choice for the discretised Algorithm S. -/
def algSBits (n m M : ℕ) : ℕ := Nat.clog 2 (8 * Digraph.algSChoices n m M)

theorem algSBits_spec (n m M : ℕ) :
    (Digraph.algSChoices n m M : ℝ) / (2 : ℝ) ^ algSBits n m M ≤ 1 / 8 := by
  have h := Nat.le_pow_clog (b := 2) (by norm_num) (8 * Digraph.algSChoices n m M)
  have h' : (8 : ℝ) * Digraph.algSChoices n m M ≤ (2 : ℝ) ^ algSBits n m M := by
    unfold algSBits
    exact_mod_cast h
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **Theorem 9 of Feng, Fu and Guo, as a hypothesis about the transcription.**
On every finite directed multigraph with probabilities in `(0,1]` and positive
reliability, the exact Algorithm S with `algSSamples` samples per round has
relative error more than `α` with probability at most 1/8. -/
def AlgSAccurate (α : ℝ) : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq E] (G : Digraph V E) (q : E → ℝ)
    (s t : V), (∀ e, 0 < q e ∧ q e ≤ 1) → 0 < G.reliability q s t →
    (G.algS (Q := Empty) q s t (algSSamples (Fintype.card V) (Fintype.card E) α)).exp noOracle
      (fun z => if |z - G.reliability q s t| ≤ α * G.reliability q s t then 0 else 1) ≤ 1 / 8

/-- The discretised Algorithm S, as a reliability estimator with a finite
seed space. -/
def algSEstimator (α : ℝ) : ReliabilityEstimator := fun V E _ _ _ G q s t =>
  ((G.algS (Q := Empty) q s t (algSSamples (Fintype.card V) (Fintype.card E) α)).discretise
    (algSBits (Fintype.card V) (Fintype.card E)
      (algSSamples (Fintype.card V) (Fintype.card E) α))).toRand

/-- If the exact Algorithm S is accurate, its discretised version meets the
estimator contract of the reduction. -/
theorem algSEstimator_correct {α : ℝ} (h : AlgSAccurate α) : (algSEstimator α).Correct α := by
  intro V E _ _ _ G q s t hq hpos
  set M := algSSamples (Fintype.card V) (Fintype.card E) α
  set bits := algSBits (Fintype.card V) (Fintype.card E) M
  have hexp := Prog.exp_eq_toRand noOracle
    ((G.algS (Q := Empty) q s t M).discretise bits)
    (fun z => if |z - G.reliability q s t| ≤ α * G.reliability q s t then 0 else 1)
  have hd := Prog.exp_discretise_le noOracle bits
    (f := fun z : ℝ => if |z - G.reliability q s t| ≤ α * G.reliability q s t then 0 else 1)
    (fun z => by split_ifs <;> norm_num) (fun z => by split_ifs <;> norm_num)
    (G.algS_choiceBound (Q := Empty) q s t M)
  have hb := algSBits_spec (Fintype.card V) (Fintype.card E) M
  have hex := h V E G q s t hq hpos
  have hle := (abs_le.mp hd).2
  have hfinal : ((G.algS (Q := Empty) q s t M).discretise bits).exp noOracle
      (fun z => if |z - G.reliability q s t| ≤ α * G.reliability q s t then 0 else 1) ≤
      1 / 4 := by linarith
  rw [hexp] at hfinal
  refine le_trans (le_of_eq ?_) hfinal
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : |((G.algS (Q := Empty) q s t M).discretise bits).toRand.value z -
      G.reliability q s t| ≤ α * G.reliability q s t
  · rw [ite_eq_left hz, mul_zero]
    exact ite_eq_left hz
  · rw [ite_eq_right hz, mul_one]
    exact ite_eq_right hz

/-- With rational input probabilities, every answer of the estimator is a
fraction of the size bounded in `algS_sat`. -/
theorem algSEstimator_height (α : ℝ) {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (G : Digraph V E) (q : E → ℝ) (s t : V) (a b : E → ℕ) (hb : ∀ e, 0 < b e)
    (ha : ∀ e, a e ≤ b e) (hq : ∀ e, q e = (a e : ℝ) / (b e : ℝ))
    (hM : 0 < algSSamples (Fintype.card V) (Fintype.card E) α)
    (z : (algSEstimator α V E G q s t).Seed) :
    Height (Digraph.sizeBase (Fintype.card V) (Fintype.card E)
        (algSSamples (Fintype.card V) (Fintype.card E) α) (∏ e, b e) ^ Fintype.card V)
      ((algSEstimator α V E G q s t).value z) :=
  Prog.toRand_value_of_sat
    ((G.algS_sat (Q := Empty) q a b hb ha hq s t hM).discretise _) z

namespace Digraph

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]

/-- With zero samples every update is zero, so rationality still holds. -/
theorem sRounds_zero_sat (G : Digraph V E) (q : E → ℝ) (t : V) (f : ℕ)
    (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V))
    (hqh : ∀ u, Height 1 (qh u)) :
    Prog.Sat (fun _ => True) (fun _ => True) (Height 1)
      (G.sRounds (Q := Empty) q t 0 f R qh pools) := by
  induction f generalizing R qh pools with
  | zero => exact .ret _ (hqh t)
  | succ f ih =>
    unfold sRounds
    split_ifs
    · exact .ret _ (hqh t)
    · generalize (((arcOrder E).filter fun e => G.source e ∈ R ∧ G.target e ∉ R).argmax
        fun e => qh (G.source e) * q e) = o
      cases o with
      | none => exact .ret _ (height_zero (by omega))
      | some e =>
        change Prog.Sat _ _ _ (if _ then _ else _)
        split_ifs
        · exact .ret _ (height_zero (by omega))
        · simp only [sGenerate, Prog.bind, Nat.cast_zero, div_zero]
          apply ih
          intro u
          by_cases hu : u = G.target e
          · subst u
            simpa using height_zero (H := 1) (by omega)
          · simpa [Function.update_of_ne hu] using hqh u

theorem algS_zero_sat (G : Digraph V E) (q : E → ℝ) (s t : V) :
    Prog.Sat (fun _ => True) (fun _ => True) (Height 1)
      (G.algS (Q := Empty) q s t 0) := by
  apply G.sRounds_zero_sat
  intro u
  split_ifs
  · exact height_one (by omega)
  · exact height_zero (by omega)

/-- Equal terminals return one for every budget, including zero. -/
theorem algS_self (G : Digraph V E) (q : E → ℝ) (s : V) (M : ℕ) :
    G.algS (Q := Empty) q s s M = .ret 1 := by
  unfold algS
  cases Fintype.card V <;> simp [sRounds]

end Digraph

/-- Total answer-size bound, also covering zero samples and edgeless queries. -/
theorem algSEstimator_height_total (α : ℝ) {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq E] (G : Digraph V E) (q : E → ℝ) (s t : V) (a b : E → ℕ)
    (hb : ∀ e, 0 < b e) (ha : ∀ e, a e ≤ b e)
    (hq : ∀ e, q e = (a e : ℝ) / (b e : ℝ))
    (z : (algSEstimator α V E G q s t).Seed) :
    Height (max 1 (Digraph.sizeBase (Fintype.card V) (Fintype.card E)
      (algSSamples (Fintype.card V) (Fintype.card E) α) (∏ e, b e) ^ Fintype.card V))
      ((algSEstimator α V E G q s t).value z) := by
  by_cases hM : 0 < algSSamples (Fintype.card V) (Fintype.card E) α
  · exact (algSEstimator_height α G q s t a b hb ha hq hM z).mono (le_max_right _ _)
  · have hzero : algSSamples (Fintype.card V) (Fintype.card E) α = 0 := by omega
    have hs : Prog.Sat (fun _ => True) (fun _ => True) (Height 1)
        ((G.algS (Q := Empty) q s t (algSSamples (Fintype.card V) (Fintype.card E) α)).discretise
          (algSBits (Fintype.card V) (Fintype.card E)
            (algSSamples (Fintype.card V) (Fintype.card E) α))) := by
      rw [hzero]
      exact (G.algS_zero_sat q s t).discretise _
    have hz := Prog.toRand_value_of_sat hs z
    exact hz.mono (le_max_left _ _)

end
end DirectedCycleFPRAS
