module

public import DirectedCycleFPRAS.ProgramComposition

@[expose] public section

/-! Finite-program martingale estimates used in FFG Theorem 9. States may
contain real estimates and snapshot lists; they need not form a finite type.
All randomness comes from the finite choices of `Prog`. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
namespace Prog
variable {Q S : Type}

/-- Iterate a fresh randomized transition. Absorbing states handle early
termination without changing the number of analysis rounds. -/
def steps (K : S → Prog Q S) : ℕ → S → Prog Q S
  | 0, x => .ret x
  | n+1, x => (K x).bind (steps K n)

/-- Change the centre of a second moment. -/
theorem exp_square_shift (O : Oracle Q) (m : Prog Q S) (f : S → ℝ)
    (b c : ℝ) (hm : m.exp O f = b) :
    m.exp O (fun x => (f x-c)^2) =
      m.exp O (fun x => (f x-b)^2) + (b-c)^2 := by
  have he : (fun x => (f x-c)^2) = fun x =>
      (f x-b)^2 + (2*(b-c))*f x + (c^2-b^2) := by funext x; ring
  rw [he, exp_add, exp_add, exp_mul_left, exp_const, hm]
  ring

theorem steps_mean (O : Oracle Q) (K : S → Prog Q S) (f : S → ℝ)
    (hm : ∀ x, (K x).exp O f = f x) (n : ℕ) (x : S) :
    (steps K n x).exp O f = f x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [steps, exp_bind, ih, hm]

/-- Local conditional variance controls the multiplicative growth of the
second moment of the total prediction. -/
theorem steps_secondMoment (O : Oracle Q) (K : S → Prog Q S) (ψ : S → ℝ)
    {c : ℝ} (hc : 0 ≤ c)
    (hm : ∀ x, (K x).exp O ψ = ψ x)
    (hv : ∀ x, (K x).exp O (fun y => (ψ y-ψ x)^2) ≤ c*(ψ x)^2)
    (n : ℕ) (x : S) :
    (steps K n x).exp O (fun y => (ψ y)^2) ≤ (1+c)^n*(ψ x)^2 := by
  have hstep (x : S) : (K x).exp O (fun y => (ψ y)^2) ≤ (1+c)*(ψ x)^2 := by
    have he := exp_square_shift O (K x) ψ (ψ x) 0 (hm x)
    simp only [sub_zero] at he
    rw [he]
    nlinarith [hv x]
  induction n generalizing x with
  | zero => simp [steps, exp]
  | succ n ih =>
    simp only [steps, exp_bind]
    calc
      _ ≤ (K x).exp O (fun y => (1+c)^n*(ψ y)^2) := exp_mono O _ (ih ·)
      _ = (1+c)^n * (K x).exp O (fun y => (ψ y)^2) := exp_mul_left _ _ _ _
      _ ≤ (1+c)^n * ((1+c)*(ψ x)^2) :=
        mul_le_mul_of_nonneg_left (hstep x) (pow_nonneg (by linarith) _)
      _ = (1+c)^(n+1)*(ψ x)^2 := by rw [pow_succ]; ring

/-- Accumulation of the target prediction's variance. No independence of
successive rounds is assumed: the transition depends on the entire state. -/
theorem steps_variance (O : Oracle Q) (K : S → Prog Q S) (f ψ : S → ℝ)
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hm : ∀ x, (K x).exp O f = f x)
    (hψ : ∀ x, (K x).exp O ψ = ψ x)
    (hv : ∀ x, (K x).exp O (fun y => (f y-f x)^2) ≤ d*(ψ x)^2)
    (hvψ : ∀ x, (K x).exp O (fun y => (ψ y-ψ x)^2) ≤ c*(ψ x)^2)
    (n : ℕ) (x : S) :
    (steps K n x).exp O (fun y => (f y-f x)^2) ≤ d*n*(1+c)^n*(ψ x)^2 := by
  have hbase : 1 ≤ 1+c := by linarith
  have hψstep (x : S) : (K x).exp O (fun y => (ψ y)^2) ≤ (1+c)*(ψ x)^2 := by
    simpa [steps, exp_bind, exp] using steps_secondMoment O K ψ hc hψ hvψ 1 x
  induction n generalizing x with
  | zero => simp [steps, exp]
  | succ n ih =>
    simp only [steps, exp_bind]
    have he (y : S) := exp_square_shift O (steps K n y) f (f y) (f x)
      (steps_mean O K f hm n y)
    simp_rw [he]
    rw [exp_add]
    have hfirst : (K x).exp O (fun y => (steps K n y).exp O (fun z => (f z-f y)^2)) ≤
        d*n*(1+c)^(n+1)*(ψ x)^2 := by
      calc
        _ ≤ (K x).exp O (fun y => (d*n*(1+c)^n)*(ψ y)^2) := exp_mono O _ (ih ·)
        _ = (d*n*(1+c)^n)*(K x).exp O (fun y => (ψ y)^2) := exp_mul_left _ _ _ _
        _ ≤ (d*n*(1+c)^n)*((1+c)*(ψ x)^2) :=
          mul_le_mul_of_nonneg_left (hψstep x) (by positivity)
        _ = _ := by rw [pow_succ]; ring
    have hsecond : (K x).exp O (fun y => (f y-f x)^2) ≤ d*(1+c)^(n+1)*(ψ x)^2 := by
      apply (hv x).trans
      have hp : 1 ≤ (1+c)^(n+1) := one_le_pow₀ hbase
      nlinarith [mul_nonneg hd (sq_nonneg (ψ x)),
        mul_nonneg (mul_nonneg hd (sq_nonneg (ψ x))) (sub_nonneg.mpr hp)]
    push_cast
    nlinarith

/-- A purely algebraic replacement for the exponential estimate in FFG's
second-moment calculation. -/
theorem pow_one_add_le_two {c : ℝ} (hc : 0 ≤ c) (n : ℕ)
    (hn : (n : ℝ)*c ≤ 1/2) : (1+c)^n ≤ 2 := by
  have stronger : ∀ n : ℕ, (n : ℝ)*c ≤ 1/2 → (1+c)^n ≤ 1+2*n*c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro h
      have hn' : (n : ℝ)*c ≤ 1/2 := by push_cast at h; nlinarith
      have hi := ih hn'
      rw [pow_succ]
      have hp := mul_le_mul_of_nonneg_right hi (show 0 ≤ 1+c by linarith)
      have hc' := mul_nonneg hc (show 0 ≤ 1-2*(n : ℝ)*c by linarith)
      push_cast
      nlinarith
  have h := stronger n hn
  linarith

/-- FFG's factor-two variance bound from the local prediction estimates. -/
theorem steps_variance_le (O : Oracle Q) (K : S → Prog Q S) (f ψ : S → ℝ)
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hm : ∀ x, (K x).exp O f = f x)
    (hψ : ∀ x, (K x).exp O ψ = ψ x)
    (hv : ∀ x, (K x).exp O (fun y => (f y-f x)^2) ≤ d*(ψ x)^2)
    (hvψ : ∀ x, (K x).exp O (fun y => (ψ y-ψ x)^2) ≤ c*(ψ x)^2)
    (n : ℕ) (hn : (n : ℝ)*c ≤ 1/2) (x : S) :
    (steps K n x).exp O (fun y => (f y-f x)^2) ≤ 2*d*n*(ψ x)^2 := by
  apply (steps_variance O K f ψ hc hd hm hψ hv hvψ n x).trans
  have hp := pow_one_add_le_two hc n hn
  have hs : 0 ≤ d*n*(ψ x)^2 := by positivity
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hp)]

/-- Chebyshev for finite decision trees, including infinite result types. -/
theorem chebyshev (O : Oracle Q) (m : Prog Q S) (f : S → ℝ) (b : ℝ)
    {a : ℝ} (ha : 0 < a) :
    m.exp O (fun x => if |f x-b| ≤ a then 0 else 1) ≤
      m.exp O (fun x => (f x-b)^2) / a^2 := by
  have hpoint (x : S) : (if |f x-b| ≤ a then (0 : ℝ) else 1) ≤ (a^2)⁻¹*(f x-b)^2 := by
    split_ifs with h
    · positivity
    · have hs : a^2 ≤ (f x-b)^2 := by
        have hlt := lt_of_not_ge h
        nlinarith [sq_abs (f x-b), abs_nonneg (f x-b)]
      calc
        1 = (a^2)⁻¹*a^2 := by rw [inv_mul_cancel₀ (ne_of_gt (sq_pos_of_pos ha))]
        _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
  have h := exp_mono O m hpoint
  rw [exp_mul_left] at h
  simpa [div_eq_mul_inv, mul_comm] using h

/-- The quantitative conclusion of FFG Theorem 9, from its local prediction
identities and variance bounds. The sample count is arbitrary: only the two
numerical lower bounds are used, so an unreduced budget is admissible. -/
theorem steps_relative_tail (O : Oracle Q) (K : S → Prog Q S) (f ψ : S → ℝ)
    (n m M : ℕ) (hM : 0 < M) (q α δ : ℝ) (hq : 0 < q) (hα : 0 < α)
    (hm : ∀ x, (K x).exp O f = f x)
    (hψ : ∀ x, (K x).exp O ψ = ψ x)
    (hv : ∀ x, (K x).exp O (fun y => (f y-f x)^2) ≤ (m/M)*q^2*(ψ x)^2)
    (hvψ : ∀ x, (K x).exp O (fun y => (ψ y-ψ x)^2) ≤ (n*m/M)*(ψ x)^2)
    (hgrowth : 2*(n : ℝ)^2*m ≤ M)
    (hbudget : 2*(n : ℝ)^3*m ≤ δ*α^2*M)
    (x : S) (hfx : f x = q) (hψx : ψ x = n) :
    (steps K n x).exp O (fun y => if |f y-q| ≤ α*q then 0 else 1) ≤ δ := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hc : 0 ≤ (n : ℝ)*m/M := by positivity
  have hd : 0 ≤ ((m : ℝ)/M)*q^2 := by positivity
  have hn : (n : ℝ)*(n*m/M) ≤ 1/2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have he : (n : ℝ)*(n*m/M)*2 = (2*n^2*m)/M := by ring
    rw [he]
    exact (div_le_one hMr).mpr hgrowth
  have hvn := steps_variance_le O K f ψ hc hd hm hψ hv hvψ n hn x
  rw [hfx, hψx] at hvn
  apply (chebyshev O (steps K n x) f q (mul_pos hα hq)).trans
  apply (div_le_iff₀ (sq_pos_of_pos (mul_pos hα hq))).mpr
  apply hvn.trans
  have hb := mul_le_mul_of_nonneg_right hbudget (sq_nonneg q)
  apply (mul_le_mul_iff_left₀ hMr).mp
  convert hb using 1 <;> field_simp

/-- The concrete 1/8-accuracy sample budget satisfies both lower bounds in
`steps_relative_tail`, including when the budget uses larger graph counts. -/
theorem algSSamples_bounds {n m N J : ℕ} (hn : 0 < n) (hnN : n ≤ N) (hmJ : m ≤ J)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    2*(n : ℝ)^2*m ≤ algSSamples N J α ∧
    2*(n : ℝ)^3*m ≤ (1/8 : ℝ)*α^2*algSSamples N J α := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hmJ' : (m : ℝ) ≤ J := by exact_mod_cast hmJ
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have ha2 : α^2 ≤ 1 := by nlinarith
  have hb : 16*(N : ℝ)^3*J ≤ (algSSamples N J α : ℝ)*α^2 := by
    exact (div_le_iff₀ (sq_pos_of_pos hα)).mp (Nat.le_ceil _)
  have hnm : (n : ℝ)^3*m ≤ (N : ℝ)^3*J :=
    mul_le_mul (pow_le_pow_left₀ (by positivity) hnN' 3) hmJ' hm0 (by positivity)
  have hsmall : (n : ℝ)^2*m ≤ (n : ℝ)^3*m := by
    apply mul_le_mul_of_nonneg_right _ hm0
    nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (sub_nonneg.mpr hn')]
  have hceil : (algSSamples N J α : ℝ)*α^2 ≤ algSSamples N J α :=
    mul_le_of_le_one_right (by positivity) ha2
  constructor <;> nlinarith

/-- Sum of independent executions, in the order used by Generate. -/
def sumRuns (m : Prog Q S) (f : S → ℝ) : ℕ → Prog Q ℝ
  | 0 => .ret 0
  | n+1 => (sumRuns m f n).bind fun a => m.bind fun x => .ret (a+f x)

theorem sumRuns_mean (O : Oracle Q) (m : Prog Q S) (f : S → ℝ) (n : ℕ) :
    (sumRuns m f n).exp O id = n*m.exp O f := by
  induction n with
  | zero => simp [sumRuns, exp]
  | succ n ih =>
    simp only [sumRuns, exp_bind, exp, id_eq]
    simp_rw [exp_add, exp_const]
    change (sumRuns m f n).exp O id + m.exp O f = _
    rw [ih]
    push_cast
    ring

theorem sumRuns_variance (O : Oracle Q) (m : Prog Q S) (f : S → ℝ) (n : ℕ) :
    (sumRuns m f n).exp O (fun a => (a-n*m.exp O f)^2) =
      n*m.exp O (fun x => (f x-m.exp O f)^2) := by
  induction n with
  | zero => simp [sumRuns, exp]
  | succ n ih =>
    simp only [sumRuns, exp_bind, exp]
    have he (a : ℝ) : m.exp O (fun x => (a+f x-(n+1)*m.exp O f)^2) =
        m.exp O (fun x => (f x-m.exp O f)^2) + (a-n*m.exp O f)^2 := by
      have h := exp_square_shift O m f (m.exp O f) ((n+1)*m.exp O f-a) rfl
      convert h using 1 <;> congr 1 <;> (try funext x) <;> ring
    push_cast
    simp_rw [he]
    rw [exp_add, exp_const, ih]
    ring

/-- The bounded-record estimate used in FFG Lemma 11. -/
theorem variance_le_bound_mul_mean (O : Oracle Q) (m : Prog Q S) (f : S → ℝ)
    (B : ℝ) (h0 : ∀ x, 0 ≤ f x) (hB : ∀ x, f x ≤ B) :
    m.exp O (fun x => (f x-m.exp O f)^2) ≤ B*m.exp O f := by
  have he := exp_square_shift O m f (m.exp O f) 0 rfl
  simp only [sub_zero] at he
  have hp (x : S) : (f x)^2 ≤ B*f x := by nlinarith [mul_nonneg (h0 x) (sub_nonneg.mpr (hB x))]
  have h := exp_mono O m hp
  rw [exp_mul_left, he] at h
  nlinarith [sq_nonneg (m.exp O f)]

/-- A pool replaces its old predicted contribution by an unbiased empirical
contribution. The removed contribution is `Φ E f`. -/
theorem prediction_update_mean (O : Oracle Q) (m : Prog Q S) (f : S → ℝ)
    (Φ q : ℝ) {M : ℕ} (hM : 0 < M) :
    (sumRuns m f M).exp O (fun a => q-Φ*m.exp O f+(Φ/M)*a) = q := by
  rw [exp_add, exp_const, exp_mul_left]
  change q-Φ*m.exp O f+(Φ/M)*(sumRuns m f M).exp O id = q
  rw [sumRuns_mean]
  have hn : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  field_simp
  ring

/-- One-round variance for the empirical prediction update, prior to the
outflow and Harris bounds. -/
theorem prediction_update_variance (O : Oracle Q) (m : Prog Q S) (f : S → ℝ)
    (Φ q B : ℝ) {M : ℕ} (hM : 0 < M)
    (h0 : ∀ x, 0 ≤ f x) (hB : ∀ x, f x ≤ B) :
    (sumRuns m f M).exp O (fun a => (q-Φ*m.exp O f+(Φ/M)*a-q)^2) ≤
      Φ^2/M*(B*m.exp O f) := by
  have hn : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  have he : (fun a => (q-Φ*m.exp O f+(Φ/M)*a-q)^2) =
      fun a => (Φ/M)^2*(a-M*m.exp O f)^2 := by
    funext a
    field_simp
    ring
  rw [he, exp_mul_left, sumRuns_variance]
  have hv := variance_le_bound_mul_mean O m f B h0 hB
  have hp : (Φ/M)^2*(M : ℝ) = Φ^2/M := by field_simp
  rw [← mul_assoc, hp]
  exact mul_le_mul_of_nonneg_left hv (by positivity)

/-- FFG Lemma 11's variance calculation after inserting the record and
outflow bounds. `Φ E f ≤ q` expresses the removed part of the old prediction. -/
theorem prediction_update_variance_le (O : Oracle Q) (m : Prog Q S) (f : S → ℝ)
    (Φ q C r b : ℝ) {M : ℕ} (hM : 0 < M) (hΦ : 0 ≤ Φ)
    (hq : 0 ≤ q) (hr : 0 < r) (hb : 0 ≤ b)
    (h0 : ∀ x, 0 ≤ f x) (hB : ∀ x, f x ≤ b/r)
    (hout : Φ ≤ C*r) (hpart : Φ*m.exp O f ≤ q) :
    (sumRuns m f M).exp O (fun a => (q-Φ*m.exp O f+(Φ/M)*a-q)^2) ≤ (C/M)*b*q := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  apply (prediction_update_variance O m f Φ q (b/r) hM h0 hB).trans
  have hΦb : Φ*(b/r) ≤ C*b := by
    have h := mul_le_mul_of_nonneg_right hout (div_nonneg hb hr.le)
    have he : C*r*(b/r) = C*b := by field_simp
    exact he ▸ h
  calc
    Φ^2/M*((b/r)*m.exp O f) = ((Φ/M)*(b/r))*(Φ*m.exp O f) := by ring
    _ ≤ ((Φ/M)*(b/r))*q := mul_le_mul_of_nonneg_left hpart (by positivity)
    _ = (Φ*(b/r))*(q/M) := by ring
    _ ≤ (C*b)*(q/M) := mul_le_mul_of_nonneg_right hΦb (div_nonneg hq hMr.le)
    _ = _ := by ring

end Prog
end
end DirectedCycleFPRAS
