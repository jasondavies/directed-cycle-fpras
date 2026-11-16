module

public import DirectedCycleFPRAS.ProposalLaws

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
variable {Q E : Type} [Fintype E] [DecidableEq E]

/-- Sequential reliability self-reduction, retaining the product of the nominal
branch probabilities. Rounding is applied to the whole program afterwards. -/
def recordedExpose (mk : (E → ℝ) → Q) (feas : (E → ℝ) → Prop) :
    List E → (E → ℝ) → Prog Q ((E → Bool) × ℝ)
  | [], q => .ret (pinned q, 1)
  | e :: l, q =>
    Prog.guarded (feas (pin q e true)) (mk (pin q e true)) fun r₁ =>
    Prog.guarded (feas (pin q e false)) (mk (pin q e false)) fun r₀ =>
    let law := normLaw (fun b : Bool => if b then q e * r₁ else (1 - q e) * r₀) true
    .choose law fun b =>
      (recordedExpose mk feas l (pin q e b)).bind fun r => .ret (r.1, law.value b * r.2)

def possible (q : E → ℝ) (B : (E → Bool) → Prop) (ω : E → Bool) : Prop :=
  B ω ∧ 0 < edgeWeight q ω

def completionSum (q : E → ℝ) (B : (E → Bool) → Prop) (f : (E → Bool) → ℝ) : ℝ :=
  ∑ ω, if possible q B ω then f ω else 0

def branchWeight (q : E → ℝ) (B : (E → Bool) → Prop) (e : E) (b : Bool) : ℝ :=
  (if b then q e else 1 - q e) * eventMass (pin q e b) B

theorem possible_mass_pos {q : E → ℝ} (hq : Prob01 q) {B : (E → Bool) → Prop}
    {ω : E → Bool} (h : possible q B ω) : 0 < eventMass q B := by
  have hl := Finset.single_le_sum (s := Finset.univ)
    (f := fun x => if B x then edgeWeight q x else 0)
    (fun x _ => by split_ifs; exact edgeWeight_nonneg hq x; rfl) (Finset.mem_univ ω)
  simp only [ite_eq_left h.1] at hl
  exact lt_of_lt_of_le h.2 hl

theorem possible_pin {q : E → ℝ} (hq : Prob01 q) (B : (E → Bool) → Prop)
    (e : E) (b : Bool) (ω : E → Bool) :
    (0 < branchWeight q B e b ∧ possible (pin q e b) B ω) ↔
      possible q B ω ∧ ω e = b := by
  have hr0 : 0 ≤ restWeight q e ω := by
    apply Finset.prod_nonneg
    intro f _
    split_ifs
    · exact (hq f).1
    · exact sub_nonneg.mpr (hq f).2
  have hfac0 : 0 ≤ (if b then q e else 1-q e) := by
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · exact sub_nonneg.mpr (hq e).2
    · exact (hq e).1
  constructor
  · rintro ⟨hb, hB, hw⟩
    have he : ω e = b := by
      by_contra hn
      rw [edgeWeight_pin, ite_eq_right hn, zero_mul] at hw
      exact (lt_irrefl 0) hw
    have hf : 0 < (if b then q e else 1-q e) :=
      by
        change 0 < (if b then q e else 1-q e) * eventMass (pin q e b) B at hb
        nlinarith [eventMass_nonneg (prob01_pin hq e b) B]
    rw [edgeWeight_pin, ite_eq_left he, one_mul] at hw
    refine ⟨⟨hB, ?_⟩, he⟩
    rw [edgeWeight_eq_mul_rest, he]
    exact mul_pos hf hw
  · rintro ⟨⟨hB, hw⟩, he⟩
    rw [edgeWeight_eq_mul_rest q e, he] at hw
    have hh : 0 < (if b then q e else 1-q e) ∧ 0 < restWeight q e ω := by
      constructor <;> nlinarith
    have hp : possible (pin q e b) B ω := ⟨hB, by
      rw [edgeWeight_pin, ite_eq_left he, one_mul]; exact hh.2⟩
    exact ⟨mul_pos hh.1 (possible_mass_pos (prob01_pin hq e b) hp), hp⟩

theorem completionSum_split {q : E → ℝ} (hq : Prob01 q) (B : (E → Bool) → Prop)
    (e : E) (f : (E → Bool) → ℝ) :
    completionSum q B f = ∑ b : Bool,
      if 0 < branchWeight q B e b then completionSum (pin q e b) B f else 0 := by
  have term (b : Bool) :
      (if 0 < branchWeight q B e b then completionSum (pin q e b) B f else 0) =
      ∑ ω, if 0 < branchWeight q B e b ∧ possible (pin q e b) B ω then f ω else 0 := by
    by_cases hb : 0 < branchWeight q B e b <;> simp [hb, completionSum]
  simp_rw [term, possible_pin hq B e]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : possible q B ω
  · simp [h]
  · simp [h]

theorem completionSum_bool {q : E → ℝ} (hq : ∀ e, q e = 0 ∨ q e = 1)
    {B : (E → Bool) → Prop} (hpos : 0 < eventMass q B) (f : (E → Bool) → ℝ) :
    completionSum q B f = f (pinned q) := by
  have hp : B (pinned q) := by
    by_contra hn
    have hz : eventMass q B = 0 := by
      simp only [eventMass, edgeWeight_bool hq]
      apply Finset.sum_eq_zero
      intro ω _
      by_cases he : ω = pinned q <;> simp [he, hn]
    rw [hz] at hpos
    linarith
  unfold completionSum
  rw [Finset.sum_eq_single (pinned q)]
  · simp [possible, hp, edgeWeight_bool hq]
  · intro ω _ hn
    simp [possible, edgeWeight_bool hq, hn]
  · simp

/-- Guarded estimates are relatively accurate even when the event has zero mass. -/
theorem guarded_accurate (O : Oracle Q) (B : (E → Bool) → Prop)
    (mk : (E → ℝ) → Q) (feas : (E → ℝ) → Prop) (Inv : (E → ℝ) → Prop)
    {a : ℝ} (hInv : ∀ q, Inv q → Prob01 q)
    (hfeas : ∀ q, Inv q → (feas q ↔ 0 < eventMass q B))
    (hacc : ∀ q, Inv q → 0 < eventMass q B → ∀ s,
      |O.answer (mk q) s - eventMass q B| ≤ a * eventMass q B)
    (q : E → ℝ) (hq : Inv q) (s : O.Seed (mk q)) :
    |(if feas q then O.answer (mk q) s else 0) - eventMass q B| ≤ a * eventMass q B := by
  by_cases hf : feas q
  · simpa [hf] using hacc q hq ((hfeas q hq).mp hf) s
  · have hz : eventMass q B = 0 := le_antisymm
      (not_lt.mp (fun h => hf ((hfeas q hq).mpr h))) (eventMass_nonneg (hInv q hq) B)
    simp [hf, hz]

/-- Accurate branch normalization, including exact zero branches. -/
theorem exposure_branch (q : E → ℝ) (hq : Prob01 q) (B : (E → Bool) → Prop)
    (e : E) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hp : 0 < eventMass q B)
    (r₁ r₀ : ℝ)
    (h₁ : |r₁ - eventMass (pin q e true) B| ≤ a * eventMass (pin q e true) B)
    (h₀ : |r₀ - eventMass (pin q e false) B| ≤ a * eventMass (pin q e false) B) :
    let law := normLaw (fun b : Bool => if b then q e * r₁ else (1-q e)*r₀) true
    (∀ b, law.value b ≠ 0 ↔ 0 < branchWeight q B e b) ∧
    (∀ b, (1-2*a)*(branchWeight q B e b / eventMass q B) ≤ law.value b) := by
  have ht0 (b : Bool) : 0 ≤ branchWeight q B e b := by
    apply mul_nonneg _ (eventMass_nonneg (prob01_pin hq e b) B)
    cases b
    · exact sub_nonneg.mpr (hq e).2
    · exact (hq e).1
  have hsum : (∑ b : Bool, branchWeight q B e b) = eventMass q B := by
    simpa [branchWeight] using (eventMass_split q e B).symm
  have h := normalized_lower (branchWeight q B e)
    (fun b : Bool => if b then q e*r₁ else (1-q e)*r₀) true ha0 ha1 ht0
    (hsum ▸ hp) (by
      intro b
      cases b
      · change |(1-q e)*r₀ - (1-q e)*eventMass (pin q e false) B| ≤ _
        rw [← mul_sub, abs_mul, abs_of_nonneg (sub_nonneg.mpr (hq e).2)]
        simp only [branchWeight, Bool.false_eq_true, ite_false]
        nlinarith [mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr (hq e).2)]
      · change |q e*r₁ - q e*eventMass (pin q e true) B| ≤ _
        rw [← mul_sub, abs_mul, abs_of_nonneg (hq e).1]
        simp only [branchWeight, ite_true]
        nlinarith [mul_le_mul_of_nonneg_left h₁ (hq e).1])
  refine ⟨?_, by simpa only [hsum] using h.2.2.2⟩
  intro b
  exact (not_congr (h.2.2.1 b)).trans
    ⟨fun hb => lt_of_le_of_ne (ht0 b) (Ne.symm hb), ne_of_gt⟩

/-- Pinning the current coordinate preserves the invariant that all coordinates
outside the remaining exposure list are already deterministic. -/
theorem remaining_pinned (l : List E) (q : E → ℝ) (e : E) (b : Bool)
    (hl : ∀ f, f ∉ e :: l → q f = 0 ∨ q f = 1) :
    ∀ f, f ∉ l → pin q e b f = 0 ∨ pin q e b f = 1 := by
  intro f hf
  by_cases he : f = e
  · subst f; cases b <;> simp [pin_self]
  · rw [pin_of_ne q b he]
    exact hl f (by simp [he, hf])

/-- Inverse nominal probability cancels each choice before averaging over
fresh oracle seeds. This is an adaptive-transcript identity, not an assumption
about the sampler's marginal law. -/
theorem recordedExpose_inverse (O : Oracle Q) (B : (E → Bool) → Prop)
    (mk : (E → ℝ) → Q) (feas : (E → ℝ) → Prop) (Inv : (E → ℝ) → Prop)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hInv : ∀ q, Inv q → Prob01 q) (hpin : ∀ q e b, Inv q → Inv (pin q e b))
    (hfeas : ∀ q, Inv q → (feas q ↔ 0 < eventMass q B))
    (hacc : ∀ q, Inv q → 0 < eventMass q B → ∀ s,
      |O.answer (mk q) s - eventMass q B| ≤ a * eventMass q B)
    (l : List E) (q : E → ℝ) (hqI : Inv q) (hp : 0 < eventMass q B)
    (hl : ∀ e, e ∉ l → q e = 0 ∨ q e = 1) (f : (E → Bool) → ℝ) :
    (recordedExpose mk feas l q).exp O (fun r => f r.1 / r.2) = completionSum q B f := by
  induction l generalizing q f with
  | nil =>
    simp only [recordedExpose, Prog.exp, div_one]
    exact (completionSum_bool (fun e => hl e (by simp)) hp f).symm
  | cons e l ih =>
    have hq := hInv q hqI
    have step (r₁ r₀ : ℝ)
        (h₁ : |r₁ - eventMass (pin q e true) B| ≤ a * eventMass (pin q e true) B)
        (h₀ : |r₀ - eventMass (pin q e false) B| ≤ a * eventMass (pin q e false) B) :
        let law := normLaw (fun b : Bool => if b then q e*r₁ else (1-q e)*r₀) true
        (∑ b, law.value b *
          ((recordedExpose mk feas l (pin q e b)).bind fun r =>
            Prog.ret (r.1, law.value b*r.2)).exp O (fun r => f r.1/r.2)) = completionSum q B f := by
      dsimp only
      let law := normLaw (fun b : Bool => if b then q e*r₁ else (1-q e)*r₀) true
      have hbr := exposure_branch q hq B e ha0 ha1 hp r₁ r₀ h₁ h₀
      rw [completionSum_split hq B e f]
      apply Finset.sum_congr rfl
      intro b _
      change law.value b * _ = _
      by_cases hb : law.value b = 0
      · have hn : ¬ 0 < branchWeight q B e b := fun h => (hbr.1 b).mpr h hb
        simp [hb, hn]
      · have hbp := (hbr.1 b).mp hb
        rw [ite_eq_left hbp, Prog.exp_bind]
        have hfac : 0 ≤ (if b then q e else 1-q e) := by
          cases b
          · exact sub_nonneg.mpr (hq e).2
          · exact (hq e).1
        have hpos : 0 < eventMass (pin q e b) B := pos_of_mul_pos_right hbp hfac
        have heq : (fun r : (E → Bool) × ℝ =>
            (Prog.ret (r.1, law.value b*r.2) : Prog Q ((E → Bool) × ℝ)).exp O
              (fun r => f r.1/r.2)) = fun r => (law.value b)⁻¹ * (f r.1/r.2) := by
          funext r
          simp only [Prog.exp]
          ring
        rw [heq, Prog.exp_mul_left, ih (pin q e b) (hpin q e b hqI) hpos
          (remaining_pinned l q e b hl) f]
        field_simp
    rw [recordedExpose, Prog.exp_guarded]
    simp_rw [Prog.exp_guarded]
    change (∑ s₁, (O.law (mk (pin q e true))).value s₁ *
      ∑ s₀, (O.law (mk (pin q e false))).value s₀ * _) = _
    have hs : ∀ s₁ : O.Seed (mk (pin q e true)), ∀ s₀ : O.Seed (mk (pin q e false)),
        _ := fun s₁ s₀ => step
          (if feas (pin q e true) then O.answer (mk (pin q e true)) s₁ else 0)
          (if feas (pin q e false) then O.answer (mk (pin q e false)) s₀ else 0)
          (guarded_accurate O B mk feas Inv hInv hfeas hacc _ (hpin q e true hqI) s₁)
          (guarded_accurate O B mk feas Inv hInv hfeas hacc _ (hpin q e false hqI) s₀)
    simp only [Prog.exp]
    simp_rw [show ∀ s₁ : O.Seed (mk (pin q e true)), ∀ s₀ : O.Seed (mk (pin q e false)), _ from hs]
    simp only [← Finset.sum_mul, Law.sum_one, one_mul]

theorem condWeight_pin_factor {q : E → ℝ} (hq : Prob01 q) (B : (E → Bool) → Prop)
    (e : E) (b : Bool) {ω : E → Bool} (hp : possible (pin q e b) B ω)
    (hqpos : 0 < eventMass q B) :
    condWeight q B ω = (branchWeight q B e b / eventMass q B) * condWeight (pin q e b) B ω := by
  have hpinpos := possible_mass_pos (prob01_pin hq e b) hp
  have he : ω e = b := by
    by_contra hn
    have h := hp.2
    rw [edgeWeight_pin, ite_eq_right hn, zero_mul] at h
    linarith
  have hw : edgeWeight q ω = (if b then q e else 1-q e) * edgeWeight (pin q e b) ω := by
    rw [edgeWeight_pin, ite_eq_left he, one_mul, edgeWeight_eq_mul_rest q e, he]
  simp only [condWeight, ite_eq_left hp.1, branchWeight, hw]
  field_simp

/-- Every supported output is feasible, records a positive nominal probability,
and obeys the pointwise likelihood lower bound used by rejection. -/
theorem recordedExpose_envelope (O : Oracle Q) (B : (E → Bool) → Prop)
    (mk : (E → ℝ) → Q) (feas : (E → ℝ) → Prop) (Inv : (E → ℝ) → Prop)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1/2)
    (hInv : ∀ q, Inv q → Prob01 q) (hpin : ∀ q e b, Inv q → Inv (pin q e b))
    (hfeas : ∀ q, Inv q → (feas q ↔ 0 < eventMass q B))
    (hacc : ∀ q, Inv q → 0 < eventMass q B → ∀ s,
      |O.answer (mk q) s - eventMass q B| ≤ a * eventMass q B)
    (l : List E) (q : E → ℝ) (hqI : Inv q) (hp : 0 < eventMass q B)
    (hl : ∀ e, e ∉ l → q e = 0 ∨ q e = 1) :
    Prog.Holds O (fun r => possible q B r.1 ∧ 0 < r.2 ∧
      (1-2*a)^l.length * condWeight q B r.1 ≤ r.2) (recordedExpose mk feas l q) := by
  have hc : 0 ≤ 1-2*a := by linarith
  induction l generalizing q with
  | nil =>
    have hbool := fun e => hl e (by simp)
    have cw := condWeight_bool hbool hp (pinned q)
    simp only [ite_true] at cw
    have hB : B (pinned q) := by
      by_contra hn
      simp [condWeight, hn] at cw
    refine .ret _ ⟨⟨hB, ?_⟩, by norm_num, ?_⟩
    · simp [edgeWeight_bool hbool]
    · simp [cw]
  | cons e l ih =>
    have hq := hInv q hqI
    unfold recordedExpose
    apply Prog.Holds.guarded
    intro s₁
    apply Prog.Holds.guarded
    intro s₀
    let r₁ := if feas (pin q e true) then O.answer (mk (pin q e true)) s₁ else 0
    let r₀ := if feas (pin q e false) then O.answer (mk (pin q e false)) s₀ else 0
    let law := normLaw (fun b : Bool => if b then q e*r₁ else (1-q e)*r₀) true
    have hbr := exposure_branch q hq B e ha0 (by linarith) hp r₁ r₀
      (guarded_accurate O B mk feas Inv hInv hfeas hacc _ (hpin q e true hqI) s₁)
      (guarded_accurate O B mk feas Inv hInv hfeas hacc _ (hpin q e false hqI) s₀)
    refine Prog.Holds.choose law _ fun b hb => ?_
    have hbp := (hbr.1 b).mp hb
    have hfac : 0 ≤ (if b then q e else 1-q e) := by
      cases b
      · exact sub_nonneg.mpr (hq e).2
      · exact (hq e).1
    have hpos : 0 < eventMass (pin q e b) B := pos_of_mul_pos_right hbp hfac
    apply (ih (pin q e b) (hpin q e b hqI) hpos (remaining_pinned l q e b hl)).bind
    intro r hr
    have hout := (possible_pin hq B e b r.1).mp ⟨hbp, hr.1⟩
    have hprob : 0 < law.value b := lt_of_le_of_ne (law.nonneg b) (Ne.symm hb)
    refine .ret _ ⟨hout.1, mul_pos hprob hr.2.1, ?_⟩
    have hcw : 0 ≤ condWeight (pin q e b) B r.1 := by
      simp only [condWeight, ite_eq_left hr.1.1]
      exact div_nonneg hr.1.2.le hpos.le
    calc
      (1-2*a)^(e :: l).length * condWeight q B r.1 =
          ((1-2*a)*(branchWeight q B e b/eventMass q B)) *
            ((1-2*a)^l.length * condWeight (pin q e b) B r.1) := by
        rw [condWeight_pin_factor hq B e b hr.1 hp]
        simp only [List.length_cons, pow_succ]
        ring
      _ ≤ law.value b*r.2 := mul_le_mul (hbr.2 b) hr.2.2
        (mul_nonneg (pow_nonneg hc _) hcw) (law.nonneg b)

end
end DirectedCycleFPRAS
