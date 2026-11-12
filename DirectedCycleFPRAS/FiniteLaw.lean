module

public import DirectedCycleFPRAS.Perturbation

@[expose] public section

namespace DirectedCycleFPRAS

open scoped BigOperators
noncomputable section

/-- A finite probability law with real-valued masses. -/
structure Law (Ω : Type*) [Fintype Ω] extends Mass Ω where
  sum_one : ∑ x, value x = 1

namespace Law

variable {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]

def expectation (p : Law Ω) (f : Ω → ℝ) : ℝ := ∑ x, p.value x * f x

/-- Sequential random choice, allowing the second choice to depend on the first. -/
def bind (p : Law Ω) (K : Ω → Law Ψ) : Law Ψ where
  value y := ∑ x, p.value x * (K x).value y
  nonneg y := Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) ((K x).nonneg y)
  sum_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, Law.sum_one, mul_one]
    exact p.sum_one

/-- Finite Markov inequality, with no measure-theory side conditions. -/
theorem markov (p : Law Ω) (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x)
    {a : ℝ} (ha : 0 < a) :
    (∑ x, if a ≤ f x then p.value x else 0) ≤ p.expectation f / a := by
  apply (le_div_iff₀ ha).mpr
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  split_ifs with hx
  · exact mul_le_mul_of_nonneg_left hx (p.nonneg x)
  · simpa using mul_nonneg (p.nonneg x) (hf x)

/-- Chebyshev's bound around any supplied centre, expressed using its second moment. -/
theorem chebyshev (p : Law Ω) (f : Ω → ℝ) (c : ℝ)
    {a : ℝ} (ha : 0 < a) :
    (∑ x, if a ≤ |f x - c| then p.value x else 0) ≤
      p.expectation (fun x => (f x - c)^2) / a^2 := by
  have h := p.markov (fun x => (f x - c)^2) (fun x => sq_nonneg _) (sq_pos_of_pos ha)
  have heq (x : Ω) : (a ≤ |f x - c|) ↔ a^2 ≤ (f x - c)^2 := by
    rw [← sq_abs (f x - c)]
    exact (sq_le_sq₀ ha.le (abs_nonneg _)).symm
  simp_rw [heq]
  exact h

end Law

/-- The ideal witness mixture is an actual normalised probability law. -/
def Mass.mixtureLaw {Ω I : Type*} [Fintype Ω] [Fintype I]
    (μ : Mass Ω) (A : I → Ω → Prop) [∀ i, DecidablePred (A i)]
    (hW : 0 < μ.totalWeight A) : Law Ω where
  value := μ.mixture A
  nonneg := μ.mixture_nonneg A hW
  sum_one := μ.mixture_sum A hW

/-- L1 triangle inequality. -/
theorem l1_triangle {Ω : Type*} [Fintype Ω] (p q r : Ω → ℝ) :
    l1 p r ≤ l1 p q + l1 q r := by
  rw [l1, l1, l1, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  exact abs_sub_le _ _ _

/-- Sequential composition accumulates previous-law error and the uniform
conditional-law error. States may contain the full adaptive transcript. -/
theorem bind_stability {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]
    (p q : Law Ω) (K L : Ω → Law Ψ) {η : ℝ}
    (hKL : ∀ x, l1 (K x).value (L x).value ≤ η) :
    l1 (p.bind K).value (q.bind L).value ≤ l1 p.value q.value + η := by
  calc
    l1 (p.bind K).value (q.bind L).value ≤
        l1 (p.bind K).value (q.bind K).value + l1 (q.bind K).value (q.bind L).value :=
      l1_triangle _ _ _
    _ ≤ l1 p.value q.value + ∑ x, q.value x * l1 (K x).value (L x).value := by
      apply add_le_add
      · exact selection_stability _ _ _ (fun x => (K x).nonneg) (fun x => (K x).sum_one)
      · exact mixture_stability _ _ _ q.nonneg
    _ ≤ l1 p.value q.value + η := by
      apply add_le_add_right
      calc
        (∑ x, q.value x * l1 (K x).value (L x).value) ≤ ∑ x, q.value x * η :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hKL x) (q.nonneg x)
        _ = η := by rw [← Finset.sum_mul, q.sum_one, one_mul]

/-- A finite-state sequential sampling process. State may record previous choices. -/
def Law.run {Ω : Type*} [Fintype Ω] (p : Law Ω) (K : ℕ → Ω → Law Ω) : ℕ → Law Ω
  | 0 => p
  | n + 1 => (p.run K n).bind (K n)

/-- Uniform conditional error accumulates linearly over the number of choices;
no independence between successive states is required. -/
theorem sequential_stability {Ω : Type*} [Fintype Ω]
    (p : Law Ω) (K L : ℕ → Ω → Law Ω) {η : ℝ}
    (hKL : ∀ j x, l1 (K j x).value (L j x).value ≤ η) (n : ℕ) :
    l1 (p.run K n).value (p.run L n).value ≤ n * η := by
  induction n with
  | zero => simp [Law.run, l1]
  | succ n ih =>
    calc
      _ ≤ l1 (p.run K n).value (p.run L n).value + η :=
        bind_stability _ _ _ _ (hKL n)
      _ ≤ n * η + η := add_le_add_left ih η
      _ = (n + 1 : ℕ) * η := by push_cast; ring

end
end DirectedCycleFPRAS
