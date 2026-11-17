module

public import DirectedCycleFPRAS.RationalVertexOracle

@[expose] public section

/-! Purely natural parameter choices for executable counting and sampling.
Counting targets relative error `1/r` and failure `2⁻ᵈ`; sampling targets
variation error `2⁻ᵈ`. No real-number ceiling or logarithm is evaluated. -/
namespace DirectedCycleFPRAS

/-- Repetitions giving total oracle failure at most `2⁻ᵉ` in `T` calls. -/
def execInner (T e : ℕ) : ℕ := 6*(Nat.clog 2 (max 1 T)+e)

def execWidth (A e : ℕ) : ℕ := Nat.clog 2 (max 1 A)+e

def execCountSamples (k r : ℕ) : ℕ := 64*k*r^2

def execCountQueries (m k r : ℕ) : ℕ := k+2*m*execCountSamples k r

def execCountInner (m k r : ℕ) : ℕ := execInner (execCountQueries m k r) 4

def execCountOuter (d : ℕ) : ℕ := 6*(d+1)

def execOracleChoices (n m inner : ℕ) : ℕ :=
  inner*Digraph.algSChoices (n+1) m (Digraph.rationalVertexSamples n m)

/-- Total alternatives after inlining and amplification. -/
def execCountChoices (n m k r d : ℕ) : ℕ :=
  execCountOuter d*(execCountQueries m k r*execOracleChoices n m (execCountInner m k r)+
    execCountSamples k r*(k+2*m+2))

def execCountWidth (n m k r d : ℕ) : ℕ := execWidth (execCountChoices n m k r d) (d+1)

def execSampleBlocks (d : ℕ) : ℕ := d+2

def execSampleProposals (k d : ℕ) : ℕ := 4*k*execSampleBlocks d

def execSampleQueries (m k d : ℕ) : ℕ := k+2*m*execSampleProposals k d

def execSampleInner (m k d : ℕ) : ℕ := execInner (execSampleQueries m k d) (d+2)

def execSampleChoices (n m k d : ℕ) : ℕ :=
  execSampleQueries m k d*execOracleChoices n m (execSampleInner m k d)+
    execSampleProposals k d*(k+2*m+2)

def execSampleWidth (n m k d : ℕ) : ℕ := execWidth (execSampleChoices n m k d) (d+2)

noncomputable section

/-- Six median repetitions halve the failure upper bound. -/
theorem sixfold_confidence (j : ℕ) : (7/8 : ℝ)^(6*j) ≤ (1/2 : ℝ)^j := by
  rw [pow_mul]
  exact pow_le_pow_left₀ (by positivity) (by norm_num : (7/8 : ℝ)^6 ≤ 1/2) j

theorem execInner_bound (T e : ℕ) : (T : ℝ)*(7/8 : ℝ)^execInner T e ≤ (1/2 : ℝ)^e := by
  have hT : (T : ℝ) ≤ 2^Nat.clog 2 (max 1 T) := by
    exact_mod_cast (le_max_right 1 T).trans (Nat.le_pow_clog (b := 2) (by norm_num) (max 1 T))
  calc
    _ ≤ (2 : ℝ)^Nat.clog 2 (max 1 T)*(1/2 : ℝ)^(Nat.clog 2 (max 1 T)+e) :=
      mul_le_mul hT (sixfold_confidence _) (by positivity) (by positivity)
    _ = (1/2 : ℝ)^e := by
      rw [pow_add,← mul_assoc,← mul_pow]
      norm_num

theorem execWidth_bound (A e : ℕ) : (A : ℝ)/(2 : ℝ)^execWidth A e ≤ (1/2 : ℝ)^e := by
  have hA : (A : ℝ) ≤ 2^Nat.clog 2 (max 1 A) := by
    exact_mod_cast (le_max_right 1 A).trans (Nat.le_pow_clog (b := 2) (by norm_num) (max 1 A))
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<2^execWidth A e)).mpr
  have he : (1/2 : ℝ)^e*2^execWidth A e = 2^Nat.clog 2 (max 1 A) := by
    unfold execWidth
    rw [pow_add]
    calc
      _ = 2^Nat.clog 2 (max 1 A)*((1/2 : ℝ)^e*2^e) := by ring
      _ = _ := by rw [← mul_pow]; norm_num
  rw [he]
  exact hA

theorem execCountSamples_bound (k r : ℕ) (_hr : 0<r) :
    64*(k : ℝ)/(1/(r : ℝ))^2 ≤ execCountSamples k r := by
  unfold execCountSamples
  push_cast
  simp

theorem execCountInner_bound (m k r : ℕ) :
    (execCountQueries m k r : ℝ)*(7/8 : ℝ)^execCountInner m k r ≤ 1/16 := by
  exact (execInner_bound (execCountQueries m k r) 4).trans (by norm_num)

theorem execCount_error (n m k r d : ℕ) :
    (7/8 : ℝ)^execCountOuter d+
      (execCountChoices n m k r d : ℝ)/(2 : ℝ)^execCountWidth n m k r d ≤ (1/2 : ℝ)^d := by
  have h₁ := sixfold_confidence (d+1)
  have h₂ := execWidth_bound (execCountChoices n m k r d) (d+1)
  unfold execCountOuter execCountWidth
  calc
    _ ≤ (1/2 : ℝ)^(d+1)+(1/2 : ℝ)^(d+1) := add_le_add h₁ h₂
    _ = _ := by rw [pow_succ]; ring

theorem execSample_error (n m k d : ℕ) :
    (1/2 : ℝ)^execSampleBlocks d+
      (execSampleQueries m k d : ℝ)*(7/8 : ℝ)^execSampleInner m k d+
      (execSampleChoices n m k d : ℝ)/(2 : ℝ)^execSampleWidth n m k d ≤ (1/2 : ℝ)^d := by
  have h₁ := execInner_bound (execSampleQueries m k d) (d+2)
  have h₂ := execWidth_bound (execSampleChoices n m k d) (d+2)
  unfold execSampleBlocks execSampleInner execSampleWidth
  calc
    _ ≤ (1/2 : ℝ)^(d+2)+(1/2 : ℝ)^(d+2)+(1/2 : ℝ)^(d+2) :=
      add_le_add (add_le_add (le_refl _) h₁) h₂
    _ ≤ _ := by rw [pow_add]; norm_num; nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) d]

end
end DirectedCycleFPRAS
