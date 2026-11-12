module

public import DirectedCycleFPRAS.Reduction

@[expose] public section

/-!
# Resource bounds for the reduction

There is no machine model here. Instead this file bounds, on every execution
path, the three quantities from which a running-time bound is assembled:

* `Prog.WorkBound`: the number of charged local operations. The charges are
  annotations in the definitions of `Prog.guarded` (one support-reachability
  test), `Prog.draw` (one step per alternative) and `cycleAlgorithm` (the final
  aggregation). They are trusted in the same sense as a `TimeM` tick: Lean
  proves the total, not that each charge matches a real cost.
* `Prog.Sat`: every query asked is a feasible residual instance of the input,
  so oracle inputs are never larger than the input.
* `Height`: every possible output is a rational whose numerator and
  denominator are explicitly bounded, given such bounds on the input
  probabilities and on the oracle's answers.

Selection among alternatives is shown to need only sums, products and
comparisons of the weights (`hit_normLaw_iff`).
-/

namespace DirectedCycleFPRAS

open scoped BigOperators Nat
open Classical

noncomputable section

namespace Prog

variable {Q α β : Type}

/-- At most the stated number of charged local operations on every path. -/
inductive WorkBound : Prog Q α → ℕ → Prop
  | ret (a : α) (n : ℕ) : WorkBound (.ret a) n
  | query (x : Q) (k : ℝ → Prog Q α) (n : ℕ) :
      (∀ r, WorkBound (k r) n) → WorkBound (.query x k) n
  | choose {ι : Type} [Fintype ι] (p : Law ι) (k : ι → Prog Q α) (n : ℕ) :
      (∀ i, WorkBound (k i) n) → WorkBound (.choose p k) n
  | work (c : ℕ) (m : Prog Q α) (n : ℕ) : WorkBound m n → WorkBound (.work c m) (c + n)

theorem WorkBound.mono {m : Prog Q α} {a b : ℕ} (h : WorkBound m a) (hab : a ≤ b) :
    WorkBound m b := by
  induction h generalizing b with
  | ret a n => exact .ret a b
  | query x k n _ ih => exact .query x k b fun r => ih r hab
  | choose p k n _ ih => exact .choose p k b fun i => ih i hab
  | work c m n _ ih =>
    obtain ⟨b', rfl⟩ : ∃ b', b = c + b' := ⟨b - c, by omega⟩
    exact .work c m b' (ih (by omega))

theorem WorkBound.bind {m : Prog Q α} {g : α → Prog Q β} {a b : ℕ}
    (hm : WorkBound m a) (hg : ∀ x, WorkBound (g x) b) : WorkBound (m.bind g) (a + b) := by
  induction hm with
  | ret x n => exact (hg x).mono (by omega)
  | query x k n _ ih => exact .query x _ _ ih
  | choose p k n _ ih => exact .choose p _ _ ih
  | work c m n _ ih =>
    rw [Nat.add_assoc]
    exact .work c _ _ ih

theorem WorkBound.guarded {c : Prop} {x : Q} {k : ℝ → Prog Q α} {n : ℕ}
    (h : ∀ r, WorkBound (k r) n) : WorkBound (Prog.guarded c x k) (1 + n) := by
  unfold Prog.guarded
  refine .work _ _ _ ?_
  split_ifs
  · exact .query x k n h
  · exact h 0

theorem WorkBound.draw {ι : Type} [Fintype ι] {b : ℕ} {p : Law ι} {k : ι → Prog Q α} {n : ℕ}
    (h : ∀ i, WorkBound (k i) n) : WorkBound (Prog.draw b p k) (Fintype.card ι + n) :=
  .work _ _ _ (.choose _ _ _ fun u => h (decode b p u))

theorem WorkBound.replicate {Ω : Type} {m : Prog Q Ω} {a : ℕ} (h : WorkBound m a) (n : ℕ) :
    WorkBound (m.replicate n) (n * a) := by
  induction n with
  | zero => exact .ret _ _
  | succ n ih =>
    have hb : WorkBound (m.replicate (n + 1)) (a + (n * a + 0)) :=
      h.bind fun x => ih.bind fun xs => .ret _ 0
    exact hb.mono (by rw [Nat.succ_mul]; omega)

/-- On every path whose oracle answers satisfy `A`, every query asked
satisfies `Qp` and the result satisfies `R`. -/
inductive Sat (A : ℝ → Prop) (Qp : Q → Prop) (R : α → Prop) : Prog Q α → Prop
  | ret (a : α) : R a → Sat A Qp R (.ret a)
  | query (x : Q) (k : ℝ → Prog Q α) :
      Qp x → (∀ r, A r → Sat A Qp R (k r)) → Sat A Qp R (.query x k)
  | choose {ι : Type} [Fintype ι] (p : Law ι) (k : ι → Prog Q α) :
      (∀ i, Sat A Qp R (k i)) → Sat A Qp R (.choose p k)
  | work (c : ℕ) (m : Prog Q α) : Sat A Qp R m → Sat A Qp R (.work c m)

variable {A : ℝ → Prop} {Qp : Q → Prop}

theorem Sat.bind {R' : α → Prop} {R : β → Prop} {m : Prog Q α} {g : α → Prog Q β}
    (hm : Sat A Qp R' m) (hg : ∀ a, R' a → Sat A Qp R (g a)) : Sat A Qp R (m.bind g) := by
  induction hm with
  | ret a ha => exact hg a ha
  | query x k hx _ ih => exact .query x _ hx ih
  | choose p k _ ih => exact .choose p _ ih
  | work c m _ ih => exact .work c _ ih

theorem Sat.guarded {R : α → Prop} {c : Prop} {x : Q} {k : ℝ → Prog Q α}
    (hx : c → Qp x) (h0 : A 0) (h : ∀ r, A r → Sat A Qp R (k r)) :
    Sat A Qp R (Prog.guarded c x k) := by
  unfold Prog.guarded
  refine .work _ _ ?_
  split_ifs with hc
  · exact .query x k (hx hc) h
  · exact h 0 h0

theorem Sat.draw {R : α → Prop} {ι : Type} [Fintype ι] {b : ℕ} {p : Law ι}
    {k : ι → Prog Q α} (h : ∀ i, Sat A Qp R (k i)) : Sat A Qp R (Prog.draw b p k) :=
  .work _ _ (.choose _ _ fun u => h (decode b p u))

theorem Sat.replicate {Ω : Type} {m : Prog Q Ω} (h : Sat A Qp (fun _ => True) m) (n : ℕ) :
    Sat A Qp (fun _ => True) (m.replicate n) := by
  induction n with
  | zero => exact .ret _ trivial
  | succ n ih => exact h.bind fun x _ => ih.bind fun xs _ => .ret _ trivial

end Prog

/-! ## Rational numbers of bounded size -/

/-- `x` is a fraction whose numerator, in absolute value, and denominator are
at most `H`. Its binary description has about `2 * log₂ H` bits. -/
def Height (H : ℕ) (x : ℝ) : Prop :=
  ∃ (a : ℤ) (d : ℕ), 0 < d ∧ x = a / d ∧ a.natAbs ≤ H ∧ d ≤ H

theorem Height.mono {H H' : ℕ} {x : ℝ} (h : Height H x) (hH : H ≤ H') : Height H' x := by
  obtain ⟨a, d, hd, hx, ha, hdH⟩ := h
  exact ⟨a, d, hd, hx, ha.trans hH, hdH.trans hH⟩

theorem height_zero {H : ℕ} (hH : 1 ≤ H) : Height H 0 :=
  ⟨0, 1, one_pos, by simp, by simp, hH⟩

theorem height_one {H : ℕ} (hH : 1 ≤ H) : Height H 1 :=
  ⟨1, 1, one_pos, by simp, by simpa using hH, hH⟩

theorem Height.mul {H₁ H₂ : ℕ} {x y : ℝ} (hx : Height H₁ x) (hy : Height H₂ y) :
    Height (H₁ * H₂) (x * y) := by
  obtain ⟨a, d, hd, rfl, ha, hdH⟩ := hx
  obtain ⟨a', d', hd', rfl, ha', hdH'⟩ := hy
  refine ⟨a * a', d * d', Nat.mul_pos hd hd', ?_, ?_, Nat.mul_le_mul hdH hdH'⟩
  · push_cast
    rw [div_mul_div_comm]
  · rw [Int.natAbs_mul]
    exact Nat.mul_le_mul ha ha'

theorem Height.add {H₁ H₂ : ℕ} {x y : ℝ} (hx : Height H₁ x) (hy : Height H₂ y) :
    Height (2 * (H₁ * H₂)) (x + y) := by
  obtain ⟨a, d, hd, rfl, ha, hdH⟩ := hx
  obtain ⟨a', d', hd', rfl, ha', hdH'⟩ := hy
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdR' : (d' : ℝ) ≠ 0 := by exact_mod_cast hd'.ne'
  refine ⟨a * d' + a' * d, d * d', Nat.mul_pos hd hd', ?_, ?_, ?_⟩
  · push_cast
    field_simp
  · have h1 : (a * d' + a' * d).natAbs ≤ a.natAbs * d' + a'.natAbs * d := by
      refine (Int.natAbs_add_le _ _).trans ?_
      simp [Int.natAbs_mul]
    have h2 := Nat.mul_le_mul ha hdH'
    have h3 := Nat.mul_le_mul ha' hdH
    nlinarith
  · have := Nat.mul_le_mul hdH hdH'
    omega

theorem Height.one_sub {H : ℕ} {x : ℝ} (hx : Height H x) : Height (2 * H) (1 - x) := by
  obtain ⟨a, d, hd, rfl, ha, hdH⟩ := hx
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  refine ⟨d - a, d, hd, ?_, ?_, by omega⟩
  · push_cast
    field_simp
  · have h := Int.natAbs_sub_le (d : ℤ) a
    simp only [Int.natAbs_natCast] at h
    omega

/-- A sum of `k` fractions of size `H` has size at most `(2H)^k`. -/
theorem height_sum {ι : Type} (s : Finset ι) (f : ι → ℝ) {H : ℕ}
    (hf : ∀ i ∈ s, Height H (f i)) : Height ((2 * H) ^ s.card) (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using height_zero (le_refl 1)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    have h1 := hf i (Finset.mem_insert_self i s)
    have h2 := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    refine (h1.add h2).mono (le_of_eq ?_)
    ring

/-! ## Selection without division -/

/-- For normalised weights, deciding which alternative a `b`-bit integer
selects needs only partial sums of the weights, one multiplication by the
total and comparisons: no division is performed. -/
theorem hit_normLaw_iff {ι : Type} [Fintype ι] (b : ℕ) (w : ι → ℝ) (d : ι)
    (h0 : ∀ i, 0 ≤ w i) (hpos : 0 < ∑ i, w i) (u : ℕ) (i : ι) :
    Hit b (normLaw w d) u i ↔
      (2 : ℝ) ^ b * (∑ j, if position j < position i then w j else 0) ≤ u * ∑ j, w j ∧
      (u : ℝ) * ∑ j, w j <
        (2 : ℝ) ^ b * (∑ j, if position j < position i + 1 then w j else 0) := by
  have hcum : ∀ n, cumulative (normLaw w d) n =
      (∑ j, if position j < n then w j else 0) / ∑ j, w j := by
    intro n
    unfold cumulative
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    rw [normLaw_value w d h0 hpos]
    split_ifs
    · rfl
    · simp
  unfold Hit
  rw [hcum, hcum, ← mul_div_assoc, ← mul_div_assoc, div_le_iff₀ hpos, lt_div_iff₀ hpos]

/-! ## Scores and averages have a common denominator -/

/-- Every score is a multiple of `1 / m!`. -/
theorem score_eq_div_factorial {Ω I : Type} [Fintype I] (A : I → Ω → Prop)
    [∀ i, DecidablePred (A i)] (x : Ω) :
    ∃ c : ℕ, c ≤ (Fintype.card I)! ∧ Mass.score A x = (c : ℝ) / ((Fintype.card I)! : ℕ) := by
  have hmult : Mass.multiplicity A x = ((Finset.univ.filter fun i => A i x).card : ℝ) := by
    unfold Mass.multiplicity
    rw [Finset.sum_boole]
  have hle : (Finset.univ.filter fun i => A i x).card ≤ Fintype.card I :=
    (Finset.card_filter_le _ _).trans (le_of_eq Finset.card_univ)
  rcases Nat.eq_zero_or_pos (Finset.univ.filter fun i => A i x).card with h0 | hpos
  · refine ⟨0, Nat.zero_le _, ?_⟩
    simp [Mass.score, hmult, h0]
  · have hdvd := Nat.dvd_factorial hpos hle
    refine ⟨(Fintype.card I)! / (Finset.univ.filter fun i => A i x).card,
      Nat.div_le_self _ _, ?_⟩
    have hne : ((Finset.univ.filter fun i => A i x).card : ℝ) ≠ 0 := by
      exact_mod_cast hpos.ne'
    have hf : (((Fintype.card I)! : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos _).ne'
    rw [Mass.score, hmult, Nat.cast_div hdvd hne]
    field_simp

/-- The sum of `n` values with common denominator `F` has numerator at most `n * F`. -/
theorem sampleSum_common_denominator {Ω : Type} (f : Ω → ℝ) (F : ℕ)
    (hf : ∀ x, ∃ c : ℕ, c ≤ F ∧ f x = (c : ℝ) / F) (n : ℕ) (xs : Samples Ω n) :
    ∃ C : ℕ, C ≤ n * F ∧ Law.sampleSum f n xs = (C : ℝ) / F := by
  induction n with
  | zero => exact ⟨0, by simp, by simp [Law.sampleSum]⟩
  | succ n ih =>
    obtain ⟨c, hc, hfc⟩ := hf xs.1
    obtain ⟨C, hC, hsum⟩ := ih xs.2
    refine ⟨c + C, by rw [Nat.succ_mul]; omega, ?_⟩
    change f xs.1 + Law.sampleSum f n xs.2 = _
    rw [hfc, hsum]
    push_cast
    ring

namespace Digraph

variable {V E : Type} [Fintype E] [DecidableEq E] (G : Digraph V E) (p : E → ℝ)

/-! ## Local-operation count -/

omit [Fintype E] in
theorem initWeights_workBound (l : List E) (acc : E → ℝ) :
    Prog.WorkBound (G.initWeights p l acc) l.length := by
  induction l generalizing acc with
  | nil => exact .ret _ _
  | cons e l ih =>
    have h : Prog.WorkBound (G.initWeights p (e :: l) acc) (1 + l.length) :=
      Prog.WorkBound.guarded fun r => ih _
    exact h.mono (by simp only [List.length_cons]; omega)

omit [Fintype E] in
theorem expose_workBound {Q : Type} (bits : ℕ) (mk : (E → ℝ) → Q) (feas : (E → ℝ) → Prop)
    (l : List E) (q : E → ℝ) : Prog.WorkBound (expose bits mk feas l q) (4 * l.length) := by
  induction l generalizing q with
  | nil => exact .ret _ _
  | cons f l ih =>
    have h : Prog.WorkBound (expose bits mk feas (f :: l) q)
        (1 + (1 + (Fintype.card Bool + 4 * l.length))) :=
      Prog.WorkBound.guarded fun r₁ => Prog.WorkBound.guarded fun r₀ =>
        Prog.WorkBound.draw fun b => ih (pin q f b)
    exact h.mono (by simp only [List.length_cons, Fintype.card_bool]; omega)

theorem sampler_workBound (bits : ℕ) (w : E → ℝ) :
    Prog.WorkBound (G.sampler p bits w) (5 * Fintype.card E + 1) := by
  have hbr : ∀ o : Option E, Prog.WorkBound
      (o.elim (Prog.ret fun _ => false) (G.sampleWitness p bits)) (4 * Fintype.card E) := by
    intro o
    cases o with
    | none => exact .ret _ _
    | some e =>
      have h := expose_workBound bits (fun q => G.returnQuery q e)
        (fun q => G.Feasible (G.returnQuery q e)) Finset.univ.toList (pin p e true)
      rw [Finset.length_toList, Finset.card_univ] at h
      exact h
  have h : Prog.WorkBound (G.sampler p bits w)
      (Fintype.card (Option E) + 4 * Fintype.card E) := Prog.WorkBound.draw hbr
  exact h.mono (by rw [Fintype.card_option]; omega)

/-- **Local-operation bound.** On every execution path the algorithm performs
at most `2*m + n*(6*m + 2)` charged local operations: support-reachability
tests, witness tests, and one step per alternative of each discrete choice. -/
theorem cycleAlgorithm_workBound (bits n : ℕ) :
    Prog.WorkBound (G.cycleAlgorithm p bits n)
      (2 * Fintype.card E + n * (6 * Fintype.card E + 2)) := by
  unfold cycleAlgorithm
  split_ifs
  · have hinit := G.initWeights_workBound p Finset.univ.toList fun _ => 0
    rw [Finset.length_toList, Finset.card_univ] at hinit
    have hrep : ∀ w, Prog.WorkBound
        (((G.sampler p bits w).replicate n).bind fun xs =>
          Prog.work (aggregationWork (Fintype.card E) n)
            (Prog.ret ((∑ e, w e) * Law.sampleAverage (Mass.score G.event) n xs)))
        (n * (5 * Fintype.card E + 1) + (aggregationWork (Fintype.card E) n + 0)) :=
      fun w => ((G.sampler_workBound p bits w).replicate n).bind
        fun xs => .work _ _ _ (.ret _ _)
    refine (hinit.bind hrep).mono ?_
    unfold aggregationWork
    ring_nf
    omega
  · exact .ret _ _

/-! ## Queries are residual instances; outputs have bounded size -/

omit [Fintype E] in
theorem expose_sat {Q : Type} {A : ℝ → Prop} {Qp : Q → Prop} (bits : ℕ)
    (mk : (E → ℝ) → Q) (feas : (E → ℝ) → Prop) (Inv : (E → ℝ) → Prop)
    (hpin : ∀ q f b, Inv q → Inv (pin q f b)) (hQ : ∀ q, Inv q → feas q → Qp (mk q))
    (h0 : A 0) (l : List E) (q : E → ℝ) (hq : Inv q) :
    Prog.Sat A Qp (fun _ => True) (expose bits mk feas l q) := by
  induction l generalizing q with
  | nil => exact .ret _ trivial
  | cons f l ih =>
    exact Prog.Sat.guarded (hQ _ (hpin q f true hq)) h0 fun r₁ _ =>
      Prog.Sat.guarded (hQ _ (hpin q f false hq)) h0 fun r₀ _ =>
        Prog.Sat.draw fun b => ih (pin q f b) (hpin q f b hq)

/-- **Query and output-size bound.** Suppose the input probabilities are
fractions of size at most `Hp` and the oracle's answers are fractions of size
at most `Ho`. Then on every execution path

* every query asked is a residual instance (each probability is an input
  probability, 0 or 1) passing the support-reachability test, so oracle inputs
  are no larger than the input; and
* the output is a fraction of size at most `(2*Hp*Ho)^m * (n * m!)`, that is,
  about `m * log₂(2*Hp*Ho) + log₂ n + m * log₂ m` bits per component. -/
theorem cycleAlgorithm_sat {Hp Ho : ℕ} (hHp : 1 ≤ Hp) (hHo : 1 ≤ Ho)
    (hp : ∀ e, Height Hp (p e)) (bits : ℕ) {n : ℕ} (hn : 0 < n) :
    Prog.Sat (Height Ho) (fun x : Query V E => Derived p x.1 ∧ G.Feasible x)
      (Height ((2 * (Hp * Ho)) ^ Fintype.card E * (n * (Fintype.card E)!)))
      (G.cycleAlgorithm p bits n) := by
  have hprod : 1 ≤ Hp * Ho := Nat.mul_pos hHp hHo
  have hbig : 1 ≤ (2 * (Hp * Ho)) ^ Fintype.card E * (n * (Fintype.card E)!) :=
    Nat.mul_pos (pow_pos (by omega) _) (Nat.mul_pos hn (Nat.factorial_pos _))
  have h0 : Height Ho 0 := height_zero hHo
  unfold cycleAlgorithm
  split_ifs
  · -- initial weights
    have hinit : ∀ (l : List E) (acc : E → ℝ), (∀ e, Height (Hp * Ho) (acc e)) →
        Prog.Sat (Height Ho) (fun x : Query V E => Derived p x.1 ∧ G.Feasible x)
          (fun w : E → ℝ => ∀ e, Height (Hp * Ho) (w e)) (G.initWeights p l acc) := by
      intro l
      induction l with
      | nil => exact fun acc hacc => .ret _ hacc
      | cons e l ih =>
        intro acc hacc
        refine Prog.Sat.guarded
          (fun hf => ⟨derived_pin (derived_self p) e false, hf⟩) h0 fun r hr => ?_
        apply ih
        intro e'
        by_cases hee : e' = e
        · subst hee
          rw [Function.update_self]
          exact (hp e').mul hr
        · rw [Function.update_of_ne hee]
          exact hacc e'
    refine (hinit _ _ fun _ => height_zero hprod).bind fun w hw => ?_
    -- samples
    have hsampler : Prog.Sat (Height Ho)
        (fun x : Query V E => Derived p x.1 ∧ G.Feasible x) (fun _ => True)
        (G.sampler p bits w) := by
      refine Prog.Sat.draw fun o => ?_
      cases o with
      | none => exact .ret _ trivial
      | some e =>
        exact expose_sat bits (fun q => G.returnQuery q e)
          (fun q => G.Feasible (G.returnQuery q e)) (Derived p)
          (fun q f b hq => derived_pin hq f b)
          (fun q hq hf => ⟨derived_pin hq e false, hf⟩) h0 _ _
          (derived_pin (derived_self p) e true)
    refine (hsampler.replicate n).bind fun xs _ => .work _ _ (.ret _ ?_)
    -- the output
    have hW : Height ((2 * (Hp * Ho)) ^ Fintype.card E) (∑ e, w e) := by
      have := height_sum Finset.univ w fun e _ => hw e
      rwa [Finset.card_univ] at this
    obtain ⟨C, hC, hsum⟩ := sampleSum_common_denominator (Mass.score G.event)
      (Fintype.card E)! (score_eq_div_factorial G.event) n xs
    have havg : Height (n * (Fintype.card E)!)
        (Law.sampleAverage (Mass.score G.event) n xs) := by
      refine ⟨C, (Fintype.card E)! * n, Nat.mul_pos (Nat.factorial_pos _) hn, ?_,
        by simpa using hC, by rw [Nat.mul_comm]⟩
      rw [Law.sampleAverage, hsum]
      push_cast
      rw [div_div]
    exact hW.mul havg
  · exact .ret _ (height_zero hbig)

end Digraph

/-! ## Every weight used in a discrete choice has bounded size -/

namespace Prog

variable {Q α β : Type}

/-- The program is built from oracle calls and weighted `b`-bit draws only,
and on every path whose oracle answers satisfy `A`, every weight handed to a
draw satisfies `Hw` and the result satisfies `R`. A derivation exhibits the
weight vector of each draw. -/
inductive WeightSat (A Hw : ℝ → Prop) (R : α → Prop) : Prog Q α → Prop
  | ret (a : α) : R a → WeightSat A Hw R (.ret a)
  | query (x : Q) (k : ℝ → Prog Q α) :
      (∀ r, A r → WeightSat A Hw R (k r)) → WeightSat A Hw R (.query x k)
  | draw {ι : Type} [Fintype ι] (b : ℕ) (w : ι → ℝ) (d : ι) (k : ι → Prog Q α) :
      (∀ i, Hw (w i)) → (∀ i, WeightSat A Hw R (k i)) →
      WeightSat A Hw R (Prog.draw b (normLaw w d) k)
  | work (c : ℕ) (m : Prog Q α) : WeightSat A Hw R m → WeightSat A Hw R (.work c m)

variable {A Hw : ℝ → Prop}

theorem WeightSat.bind {R' : α → Prop} {R : β → Prop} {m : Prog Q α} {g : α → Prog Q β}
    (hm : WeightSat A Hw R' m) (hg : ∀ a, R' a → WeightSat A Hw R (g a)) :
    WeightSat A Hw R (m.bind g) := by
  induction hm with
  | ret a ha => exact hg a ha
  | query x k _ ih => exact .query x _ ih
  | draw b w d k hw _ ih => exact .draw b w d (fun i => (k i).bind g) hw ih
  | work c m _ ih => exact .work c _ ih

theorem WeightSat.guarded {R : α → Prop} {c : Prop} {x : Q} {k : ℝ → Prog Q α}
    (h0 : A 0) (h : ∀ r, A r → WeightSat A Hw R (k r)) :
    WeightSat A Hw R (Prog.guarded c x k) := by
  unfold Prog.guarded
  refine .work _ _ ?_
  split_ifs
  · exact .query x k h
  · exact h 0 h0

theorem WeightSat.replicate {Ω : Type} {m : Prog Q Ω} (h : WeightSat A Hw (fun _ => True) m)
    (n : ℕ) : WeightSat A Hw (fun _ => True) (m.replicate n) := by
  induction n with
  | zero => exact .ret _ trivial
  | succ n ih => exact h.bind fun x _ => ih.bind fun xs _ => .ret _ trivial

end Prog

/-- Partial sums of weights of size `H`, as used by the selection rule
`hit_normLaw_iff`, have size at most `(2H)^k` for `k` alternatives. -/
theorem height_partialSum {ι : Type} [Fintype ι] (w : ι → ℝ) {H : ℕ} (hH : 1 ≤ H)
    (hw : ∀ i, Height H (w i)) (n : ℕ) :
    Height ((2 * H) ^ Fintype.card ι) (∑ j, if position j < n then w j else 0) := by
  rw [← Finset.sum_filter]
  refine (height_sum _ w fun i _ => hw i).mono ?_
  exact Nat.pow_le_pow_right (by omega)
    ((Finset.card_filter_le _ _).trans (le_of_eq Finset.card_univ))

namespace Digraph

variable {V E : Type} [Fintype E] [DecidableEq E] (G : Digraph V E) (p : E → ℝ)

omit [Fintype E] in
theorem expose_weightSat {Q : Type} {Hp Ho : ℕ} (hHp : 1 ≤ Hp) (hHo : 1 ≤ Ho) (bits : ℕ)
    (mk : (E → ℝ) → Q) (feas : (E → ℝ) → Prop) (l : List E) (q : E → ℝ)
    (hq : ∀ e, Height Hp (q e)) :
    Prog.WeightSat (Height Ho) (Height (2 * (Hp * Ho))) (fun _ => True)
      (expose bits mk feas l q) := by
  induction l generalizing q with
  | nil => exact .ret _ trivial
  | cons f l ih =>
    refine Prog.WeightSat.guarded (height_zero hHo) fun r₁ hr₁ =>
      Prog.WeightSat.guarded (height_zero hHo) fun r₀ hr₀ => ?_
    refine .draw bits _ true _ ?_ fun b => ih (pin q f b) ?_
    · intro b
      cases b
      · exact ((hq f).one_sub.mul hr₀).mono (le_of_eq (by ring))
      · exact ((hq f).mul hr₁).mono (by omega)
    · intro e
      by_cases he : e = f
      · subst he
        rw [pin_self]
        cases b
        · simpa using height_zero hHp
        · simpa using height_one hHp
      · rw [pin_of_ne q b he]
        exact hq e

/-- **Size of the selection weights.** Under the size hypotheses of
`cycleAlgorithm_sat`, the algorithm consists of oracle calls and weighted
draws only, and every weight handed to a draw is a fraction of size at most
`2 * Hp * Ho`. By `height_partialSum` the partial sums compared by the
selection rule then have size at most `(4 * Hp * Ho)^(m + 1)`. -/
theorem cycleAlgorithm_weightSat {Hp Ho : ℕ} (hHp : 1 ≤ Hp) (hHo : 1 ≤ Ho)
    (hp : ∀ e, Height Hp (p e)) (bits n : ℕ) :
    Prog.WeightSat (Height Ho) (Height (2 * (Hp * Ho))) (fun _ => True)
      (G.cycleAlgorithm p bits n) := by
  have hprod : 1 ≤ Hp * Ho := Nat.mul_pos hHp hHo
  have h0 : Height Ho 0 := height_zero hHo
  unfold cycleAlgorithm
  split_ifs
  · have hinit : ∀ (l : List E) (acc : E → ℝ), (∀ e, Height (Hp * Ho) (acc e)) →
        Prog.WeightSat (Height Ho) (Height (2 * (Hp * Ho)))
          (fun w : E → ℝ => ∀ e, Height (Hp * Ho) (w e)) (G.initWeights p l acc) := by
      intro l
      induction l with
      | nil => exact fun acc hacc => .ret _ hacc
      | cons e l ih =>
        intro acc hacc
        refine Prog.WeightSat.guarded h0 fun r hr => ?_
        apply ih
        intro e'
        by_cases hee : e' = e
        · subst hee
          rw [Function.update_self]
          exact (hp e').mul hr
        · rw [Function.update_of_ne hee]
          exact hacc e'
    refine (hinit _ _ fun _ => height_zero hprod).bind fun w hw => ?_
    have hsampler : Prog.WeightSat (Height Ho) (Height (2 * (Hp * Ho))) (fun _ => True)
        (G.sampler p bits w) := by
      refine .draw bits _ none _ ?_ fun o => ?_
      · intro o
        cases o with
        | none => exact height_zero (by omega)
        | some e => exact (hw e).mono (by omega)
      · cases o with
        | none => exact .ret _ trivial
        | some e =>
          refine expose_weightSat hHp hHo bits _ _ _ _ fun e' => ?_
          by_cases he : e' = e
          · subst he
            rw [pin_self]
            simpa using height_one hHp
          · rw [pin_of_ne p true he]
            exact hp e'
    exact (hsampler.replicate n).bind fun xs _ => .work _ _ (.ret _ trivial)
  · exact .ret _ trivial

end Digraph
end
end DirectedCycleFPRAS
