module

public import DirectedCycleFPRAS.RejectionHeight

@[expose] public section

/-! Rational height bounds for the temporary arithmetic of self-reduction and
rejection. These hold even when bounded oracle answers are inaccurate. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false

/-- Inversion preserves height, including the totalized value at zero. -/
theorem Height.inv {H : ℕ} {x : ℝ} (hx : Height H x) : Height H x⁻¹ := by
  obtain ⟨a, d, hd, rfl, ha, hdH⟩ := hx
  cases a with
  | ofNat n =>
    by_cases hn : n = 0
    · subst n
      simpa using height_zero (show 1 ≤ H by omega)
    · refine ⟨d, n, Nat.pos_of_ne_zero hn, ?_, by simpa using hdH, by simpa using ha⟩
      push_cast
      simp [inv_div]
  | negSucc n =>
    refine ⟨-(d : ℤ), n+1, by omega, ?_, by simpa using hdH, by simpa using ha⟩
    push_cast
    simp only [inv_div]
    rw [div_neg, neg_div]

theorem Height.div {H K : ℕ} {x y : ℝ} (hx : Height H x) (hy : Height K y) :
    Height (H*K) (x/y) := by simpa [div_eq_mul_inv] using hx.mul hy.inv

theorem height_nat (n : ℕ) : Height (max 1 n) (n : ℝ) :=
  ⟨n, 1, by omega, by simp, by simp, le_max_left 1 n⟩

theorem Height.clamp {H : ℕ} {x : ℝ} (hx : Height H x) (hH : 1 ≤ H) :
    Height H (max 0 (min 1 x)) := by
  rcases le_total 1 x with h | h
  · simpa [min_eq_left h] using height_one hH
  · rw [min_eq_right h]
    rcases le_total 0 x with h | h
    · simpa [max_eq_right h] using hx
    · simpa [max_eq_left h] using height_zero hH

theorem height_prod {ι : Type} (s : Finset ι) (f : ι → ℝ) {H : ℕ}
    (hf : ∀ i ∈ s, Height H (f i)) : Height (H^s.card) (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using height_one (le_refl 1)
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ']
    exact (hf i (by simp)).mul (ih (fun j hj => hf j (by simp [hj])))

/-- Every cumulative sum used in a finite-choice comparison has a controlled
height, with no positivity or accuracy assumption on the input weights. -/
theorem cumulativeWeight_height {ι : Type} [Fintype ι] (w : ι → ℝ) {H : ℕ}
    (hH : 1 ≤ H) (hw : ∀ i, Height H (w i)) (P : ι → Prop) :
    Height ((2*H)^Fintype.card ι) (∑ i, if P i then w i else 0) := by
  apply height_sum
  intro i _
  split_ifs
  · exact hw i
  · exact height_zero hH

/-- Raw sums and clipped sums in normalization share the same height bound. -/
theorem positiveWeight_sum_height {ι : Type} [Fintype ι] (w : ι → ℝ) {H : ℕ}
    (hH : 1 ≤ H) (hw : ∀ i, Height H (w i)) :
    Height ((2*H)^Fintype.card ι) (∑ i, max 0 (w i)) := by
  apply height_sum
  intro i _
  rcases le_total 0 (w i) with h | h
  · simpa [max_eq_right h] using hw i
  · simpa [max_eq_left h] using height_zero hH

/-- Height of the nominal normalized branch probabilities, including the
fallback when the weights are invalid. -/
theorem normLaw_height {ι : Type} [Fintype ι] (w : ι → ℝ) (d : ι) {H : ℕ}
    (hH : 1 ≤ H) (hw : ∀ i, Height H (w i)) (i : ι) :
    Height (H*(2*H)^Fintype.card ι) ((normLaw w d).value i) := by
  have hpow : 1 ≤ (2*H)^Fintype.card ι := Nat.one_le_pow _ _ (by omega)
  have hsize : 1 ≤ H*(2*H)^Fintype.card ι := by nlinarith
  unfold normLaw
  split_ifs
  · exact (hw i).div (height_sum Finset.univ w (fun i _ => hw i))
  · change Height _ (if i=d then (1 : ℝ) else 0)
    split_ifs
    · exact height_one hsize
    · exact height_zero hsize

/-- Branch masses before normalization. -/
theorem exposure_weight_height {P H : ℕ} {q r₁ r₀ : ℝ}
    (hq : Height P q) (h₁ : Height H r₁) (h₀ : Height H r₀) (b : Bool) :
    Height (2*P*H) (if b then q*r₁ else (1-q)*r₀) := by
  cases b
  · exact hq.one_sub.mul h₀
  · exact (hq.mul h₁).mono (by nlinarith)

def exposureBranchHeight (P H : ℕ) : ℕ := (2*P*H)*(2*(2*P*H))^2

theorem exposure_branch_height {P H : ℕ} {q r₁ r₀ : ℝ}
    (hP : 1 ≤ P) (hH : 1 ≤ H) (hq : Height P q)
    (h₁ : Height H r₁) (h₀ : Height H r₀) (b : Bool) :
    Height (exposureBranchHeight P H)
      ((normLaw (fun b : Bool => if b then q*r₁ else (1-q)*r₀) true).value b) := by
  simpa [exposureBranchHeight] using normLaw_height
    (fun b : Bool => if b then q*r₁ else (1-q)*r₀) true
    (show 1 ≤ 2*P*H by nlinarith) (exposure_weight_height hq h₁ h₀) b

/-- Residual pinning never enlarges an edge parameter. -/
theorem derived_height {E : Type} {p q : E → ℝ} {P : ℕ} (hP : 1 ≤ P)
    (hp : ∀ e, Height P (p e)) (hq : Derived p q) (e : E) : Height P (q e) := by
  rcases hq e with h | h | h
  · rw [h]; exact hp e
  · rw [h]; exact height_zero hP
  · rw [h]; exact height_one hP

/-- Every nominal proposal product has polynomial bit length, on every
execution whose oracle answers satisfy the height bound, including failures. -/
theorem recordedExpose_height {Q E : Type} [Fintype E] [DecidableEq E]
    (mk : (E → ℝ) → Q) (feas : (E → ℝ) → Prop) (p : E → ℝ)
    {P H : ℕ} (hP : 1 ≤ P) (hH : 1 ≤ H) (hp : ∀ e, Height P (p e))
    (l : List E) (q : E → ℝ) (hq : Derived p q) :
    Prog.Sat (Height H) (fun _ => True)
      (fun r => Height ((exposureBranchHeight P H)^l.length) r.2)
      (recordedExpose mk feas l q) := by
  induction l generalizing q with
  | nil => exact .ret _ (height_one (by simp))
  | cons e l ih =>
    unfold recordedExpose
    apply Prog.Sat.guarded (fun _ => trivial) (height_zero hH)
    intro r₁ h₁
    apply Prog.Sat.guarded (fun _ => trivial) (height_zero hH)
    intro r₀ h₀
    apply Prog.Sat.choose
    intro b
    apply (ih _ (derived_pin hq e b)).bind
    intro r hr
    apply Prog.Sat.ret
    simpa only [List.length_cons, pow_succ'] using
      (exposure_branch_height hP hH (derived_height hP hp hq e) h₁ h₀ b).mul hr

/-- Product-law numerator used in the rejection calculation. -/
theorem edgeWeight_height {E : Type} [Fintype E] (p : E → ℝ) {P : ℕ}
    (hp : ∀ e, Height P (p e)) (ω : E → Bool) :
    Height ((2*P)^Fintype.card E) (edgeWeight p ω) := by
  apply height_prod
  intro e _
  split_ifs
  · exact (hp e).mono (by omega)
  · exact (hp e).one_sub

/-- Multiplicity is an integer bounded by the number of witnesses. -/
theorem multiplicity_height {I Ω : Type} [Fintype I] (A : I → Ω → Prop) (x : Ω) :
    Height (max 1 (Fintype.card I)) (Mass.multiplicity A x) := by
  let c := (Finset.univ.filter (fun i => A i x)).card
  have he : Mass.multiplicity A x = (c : ℝ) := by
    simp [Mass.multiplicity, c]
  rw [he]
  exact (height_nat c).mono (max_le_max_left 1 (Finset.card_le_univ _))

/-- Size of the unrounded rejection denominator, before inversion. -/
theorem rejection_denominator_height {I Ω : Type} [Fintype I]
    (A : I → Ω → Prop) (x : Ω) {H K : ℕ} {w g : ℝ}
    (hw : Height H w) (hg : Height K g) :
    Height (2*max 1 (Fintype.card I)*H*K) (2*Mass.multiplicity A x*w*g) := by
  have htwo : Height 2 (2 : ℝ) := (height_nat 2)
  exact ((htwo.mul (multiplicity_height A x)).mul hw).mul hg

/-- Size of the quotient before clipping, even if a denominator vanishes. -/
theorem rejection_quotient_height {I Ω : Type} [Fintype I]
    (A : I → Ω → Prop) (x : Ω) {P H K : ℕ} {μ w g : ℝ}
    (hμ : Height P μ) (hw : Height H w) (hg : Height K g) :
    Height (P*(2*max 1 (Fintype.card I)*H*K)) (μ/(2*Mass.multiplicity A x*w*g)) :=
  hμ.div (rejection_denominator_height A x hw hg)

/-- The actual clipped rejection bias has the same height bound as its
unclipped quotient, on accurate and inaccurate executions alike. -/
theorem rejectionProbability_height {I Ω : Type} [Fintype I] [Fintype Ω]
    (μ : Mass Ω) (A : I → Ω → Prop) (w : I → ℝ) (i : I) (r : Ω × ℝ)
    {P H K : ℕ} (hP : 1 ≤ P) (hH : 1 ≤ H) (hK : 1 ≤ K)
    (hμ : Height P (μ.value r.1)) (hw : Height H (w i)) (hg : Height K r.2) :
    Height (P*(2*max 1 (Fintype.card I)*H*K)) (rejectionProbability μ A w i r) := by
  have hsize : 1 ≤ P*(2*max 1 (Fintype.card I)*H*K) := by
    have hm := le_max_left 1 (Fintype.card I)
    have h1 : 1 ≤ 2*max 1 (Fintype.card I) := by omega
    have h2 := Nat.mul_le_mul h1 hH
    have h3 := Nat.mul_le_mul h2 hK
    have h4 := Nat.mul_le_mul hP h3
    simpa using h4
  unfold rejectionProbability
  split_ifs
  · exact (rejection_quotient_height A r.1 hμ hw hg).clamp hsize
  · exact height_zero hsize

/-- All integer-scaled operands in cumulative-interval selection have height
bounded by the bit-grid size times the cumulative-weight bound. -/
theorem choice_comparison_height {ι : Type} [Fintype ι] (w : ι → ℝ) {H : ℕ}
    (hH : 1 ≤ H) (hw : ∀ i, Height H (w i)) (b u : ℕ) (hu : u < 2^b)
    (P : ι → Prop) :
    Height (2^b*(2*H)^Fintype.card ι) ((2 : ℝ)^b*(∑ i, if P i then w i else 0)) ∧
    Height (2^b*(2*H)^Fintype.card ι) ((u : ℝ)*(∑ i, w i)) := by
  have hb : 1 ≤ 2^b := Nat.one_le_pow _ _ (by omega)
  have ht : Height (2^b) ((2 : ℝ)^b) := by
    simpa [max_eq_right hb] using height_nat (2^b)
  have hu' : Height (2^b) (u : ℝ) := (height_nat u).mono (max_le hb hu.le)
  exact ⟨ht.mul (cumulativeWeight_height w hH hw P),
    hu'.mul (height_sum Finset.univ w (fun i _ => hw i))⟩

/-- The branch-height bound is exponential only in operand bit lengths. -/
theorem exposureBranchHeight_bits (L K : ℕ) :
    exposureBranchHeight (2^L) (2^K) = 2^(5+3*(L+K)) := by
  unfold exposureBranchHeight
  calc
    _ = 2^5*(2^L*2^K)^3 := by ring
    _ = 2^5*(2^(L+K))^3 := by rw [pow_add]
    _ = 2^(5+3*(L+K)) := by rw [← pow_mul, ← pow_add]; congr 1; omega

/-- Explicit linear-in-exposures bit exponent for the recorded product. -/
theorem recordedExpose_bits {Q E : Type} [Fintype E] [DecidableEq E]
    (mk : (E → ℝ) → Q) (feas : (E → ℝ) → Prop) (p : E → ℝ)
    (L K : ℕ) (hp : ∀ e, Height (2^L) (p e))
    (l : List E) (q : E → ℝ) (hq : Derived p q) :
    Prog.Sat (Height (2^K)) (fun _ => True)
      (fun r => Height (2^((5+3*(L+K))*l.length)) r.2)
      (recordedExpose mk feas l q) := by
  have h := recordedExpose_height (P := 2^L) (H := 2^K) mk feas p
    (Nat.one_le_pow _ _ (by omega)) (Nat.one_le_pow _ _ (by omega)) hp l q hq
  simpa [exposureBranchHeight_bits, pow_mul] using h

/-- Combine the all-path product invariant with the actual rejection bias. -/
theorem recordedExpose_acceptance_height {Q E I : Type}
    [Fintype E] [DecidableEq E] [Fintype I]
    (mk : (E → ℝ) → Q) (feas : (E → ℝ) → Prop) (p : E → ℝ) (hp01 : Prob01 p)
    (A : I → (E → Bool) → Prop) (w : I → ℝ) (i : I)
    {P H : ℕ} (hP : 1 ≤ P) (hH : 1 ≤ H) (hp : ∀ e, Height P (p e))
    (hw : Height H (w i)) (l : List E) :
    Prog.Sat (Height H) (fun _ => True)
      (fun r => Height ((2*P)^Fintype.card E *
          (2*max 1 (Fintype.card I)*H*(exposureBranchHeight P H)^l.length))
        (rejectionProbability (edgeLaw p (fun e => (hp01 e).1) (fun e => (hp01 e).2)).toMass A w i r))
      (recordedExpose mk feas l p) := by
  apply (recordedExpose_height mk feas p hP hH hp l p (derived_self p)).imp
  intro r hr
  have hbranch : 1 ≤ exposureBranchHeight P H := by
    unfold exposureBranchHeight
    have h1 : 1 ≤ 2*P*H := by nlinarith
    exact Nat.mul_le_mul h1 (Nat.one_le_pow _ _ (by omega))
  exact rejectionProbability_height _ A w i r
    (Nat.one_le_pow _ _ (by omega)) hH (Nat.one_le_pow _ _ hbranch)
    (edgeWeight_height p hp r.1) hw hr

namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [ArcEnumeration E] [DecidableEq E]
variable (G : Digraph V E) (p : E → ℝ)

/-- The first-open weights have the common input denominator. -/
theorem firstOpenWeight_height (a b : E → ℕ) (hb : ∀ e, 0 < b e)
    (ha : ∀ e, a e ≤ b e) (hp : ∀ e, p e = (a e : ℝ)/b e)
    (R : Finset V) (u : V) (e : E) :
    Height (∏ e, b e) (G.firstOpenWeight p R u e) := by
  obtain ⟨c,hc,he⟩ := G.firstOpenWeight_frac p a b hb ha hp R u e
  exact ⟨c,∏ e, b e,Finset.prod_pos (fun e _ => hb e),by simpa using he,by simpa using hc,le_rfl⟩

/-- The outflow weights used by Algorithm S have bounded numerators and
retain the common input denominator. -/
theorem gammaS_height (a b : E → ℕ) (hb : ∀ e, 0 < b e)
    (ha : ∀ e, a e ≤ b e) (hp : ∀ e, p e = (a e : ℝ)/b e)
    (R : Finset V) (u : V) :
    Height ((Fintype.card E+1)*(∏ e, b e)) (G.gammaS p R u) := by
  obtain ⟨c,hc,he⟩ := G.gammaS_frac p a b hb ha hp R u
  refine ⟨c,∏ e, b e,Finset.prod_pos (fun e _ => hb e),by simpa using he,?_,?_⟩
  · simp only [Int.natAbs_natCast]
    exact hc.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))
  · exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

/-- Height of Algorithm S's actual source-selection weights. -/
theorem sourceWeight_height (R : Finset V) (qh : V → ℝ) {H K : ℕ}
    (hH : 1 ≤ H) (hK : 1 ≤ K) (hq : ∀ u, Height H (qh u))
    (hγ : ∀ u, Height K (G.gammaS p R u)) (o : Option V) :
    Height (H*K) (o.elim 0 (fun u => if u∈R then qh u*G.gammaS p R u else 0)) := by
  cases o with
  | none => exact height_zero (Nat.mul_le_mul hH hK)
  | some u =>
    simp only [Option.elim_some]
    split_ifs
    · exact (hq u).mul (hγ u)
    · exact height_zero (Nat.mul_le_mul hH hK)

/-- All sums in the outflow calculation have polynomial-length fractions. -/
theorem phiS_height (R : Finset V) (qh : V → ℝ) {H K : ℕ}
    (hH : 1 ≤ H) (hK : 1 ≤ K) (hq : ∀ u, Height H (qh u))
    (hγ : ∀ u, Height K (G.gammaS p R u)) :
    Height ((2*(H*K))^Fintype.card V) (G.phiS p R qh) := by
  apply height_sum
  intro u _
  split_ifs
  · exact (hq u).mul (hγ u)
  · exact height_zero (Nat.mul_le_mul hH hK)

/-- The actual estimate-update arithmetic, including zero sample budgets. -/
theorem estimate_update_height {K : ℕ} {Φ : ℝ} (hΦ : Height K Φ) (N M : ℕ) :
    Height (K*max 1 N*max 1 M) (Φ*(N : ℝ)/M) :=
  (hΦ.mul (height_nat N)).div (height_nat M)

end Digraph

end
end DirectedCycleFPRAS
