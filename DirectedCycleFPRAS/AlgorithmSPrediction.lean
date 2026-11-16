module

public import DirectedCycleFPRAS.AlgorithmSKernel
public import DirectedCycleFPRAS.AlgorithmSMoments
public import DirectedCycleFPRAS.AlgorithmSOutflow

@[expose] public section

/-! The DFS reach scores and empirical predictions of FFG §2.4, defined
using the concrete program. Resolved-vertex predictions equal their stored
estimates. `AlgorithmSUnbiased` proves the DFS splitting identity and applies
the algebraic update formula here to obtain unconditional unbiasedness. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E) (p : E → ℝ)

/-- Probability that restarting DFS at `(A,x)` records `w` with a tree path
avoiding R apart from its root. -/
def reachScore (R A : Finset V) (x w : V) : ℝ :=
  (G.sDfs (Q := Empty) p R (fun _ => none) w (Fintype.card V+1) A [(x,true)]).exp
    noOracle (fun o => o.elim 0 (fun _ => 1))

/-- The current empirical prediction for reachability of w. -/
def prediction (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V)) (w : V) : ℝ :=
  ∑ x, if x ∈ R then qh x * ((pools x).map (fun A => G.reachScore p R A x w)).sum /
    (pools x).length else 0

theorem reachScore_nonneg (R A : Finset V) (x w : V) : 0 ≤ G.reachScore p R A x w :=
  Prog.exp_nonneg _ _ fun o => by cases o <;> norm_num

theorem reachScore_le_one (R A : Finset V) (x w : V) : G.reachScore p R A x w ≤ 1 :=
  Prog.exp_le_of_le _ _ fun o => by cases o <;> norm_num

theorem reachScore_self (R A : Finset V) (x : V) : G.reachScore p R A x x = 1 := by
  simp [reachScore, sDfs, Prog.exp]

/-- A scan cannot give a resolved vertex a true nonroot path flag. -/
theorem sScan_resolved_flags (R : Finset V) (w : V) (hw : w ∈ R)
    (pre : E → Option Bool) (z : V) (flag : Bool) (l : List E)
    (D : Finset V) (st : List (V × Bool))
    (hst : ∀ a ∈ st, a.1 = w → a.2 = false) :
    Prog.Sat (fun _ => True) (fun _ => True)
      (fun r : Finset V × List (V × Bool) => ∀ a ∈ r.2, a.1 = w → a.2 = false)
      (G.sScan (Q := Empty) p R pre z flag l D st) := by
  induction l generalizing D st with
  | nil => exact .ret _ hst
  | cons e l ih =>
    unfold sScan
    split_ifs
    · refine (Prog.Sat.trivial _).bind fun o _ => ?_
      cases o with
      | false => exact ih D st hst
      | true =>
        apply ih
        intro a ha haw
        rcases List.mem_cons.mp ha with rfl | ha
        · simp_all
        · exact hst a ha haw
    · exact ih D st hst

/-- A resolved target with no true flag on the initial stack is never recorded. -/
theorem sDfs_resolved_not_recorded (R : Finset V) (w : V) (hw : w ∈ R)
    (pre : E → Option Bool) (fuel : ℕ) (D : Finset V) (st : List (V × Bool))
    (hst : ∀ a ∈ st, a.1 = w → a.2 = false) :
    Prog.Sat (fun _ => True) (fun _ => True) (fun o => o = none)
      (G.sDfs (Q := Empty) p R pre w fuel D st) := by
  induction fuel generalizing D st with
  | zero => exact .ret _ rfl
  | succ fuel ih =>
    cases st with
    | nil => exact .ret _ rfl
    | cons zf st =>
      obtain ⟨z, flag⟩ := zf
      unfold sDfs
      by_cases hz : z = w
      · have hf : flag = false := hst (z,flag) (by simp) hz
        simp only [hz, ite_true, hf, Bool.false_eq_true, ite_false]
        exact .ret _ rfl
      · simp only [hz, ite_false]
        apply (G.sScan_resolved_flags p R w hw pre z flag (arcOrder E) D st
          (fun a ha => hst a (by simp [ha]))).bind
        intro r hr
        exact ih r.1 r.2 hr

theorem reachScore_resolved (R A : Finset V) (x w : V) (hw : w ∈ R) (hx : x ≠ w) :
    G.reachScore p R A x w = 0 := by
  have h := (G.sDfs_resolved_not_recorded p R w hw (fun _ => none)
    (Fintype.card V+1) A [(x,true)] (by simp [hx])).supported
  have he := h.exp_congr (f := fun o => o.elim 0 (fun _ => (1 : ℝ)))
    (g := fun _ => 0) (fun o ho => by simp [ho])
  exact he.trans (Prog.exp_const _ _ _)

theorem prediction_nonneg (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V))
    (hq : ∀ x, 0 ≤ qh x) (w : V) : 0 ≤ G.prediction p R qh pools w := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · apply div_nonneg
    · apply mul_nonneg (hq x)
      exact List.sum_nonneg (fun a ha => by
        obtain ⟨A, _, rfl⟩ := List.mem_map.mp ha
        exact G.reachScore_nonneg p R A x w)
    · positivity
  · exact le_rfl

/-- On resolved vertices the prediction equals the stored estimate, even
if that estimate and its empirical pool are both zero. -/
theorem prediction_resolved (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V))
    (M : ℕ) (hpool : PoolInvariant R qh pools M) (w : V) (hw : w ∈ R) :
    G.prediction p R qh pools w = qh w := by
  unfold prediction
  rw [Finset.sum_eq_single w]
  · simp only [ite_eq_left hw]
    have he : (pools w).map (fun A => G.reachScore p R A w w) =
        (pools w).map (fun _ => (1 : ℝ)) := by
      apply List.map_congr_left
      intro A _
      exact G.reachScore_self p R A w
    rw [he]
    simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one]
    by_cases hl : pools w = []
    · have hz : qh w = 0 := by
        apply le_antisymm _ (hpool.nonneg w)
        by_contra h
        exact ((hpool.positive w hw).mp (lt_of_not_ge h)) hl
      simp [hl, hz]
    · have hn : ((pools w).length : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt (List.length_pos_iff_ne_nil.mpr hl)
      field_simp
  · intro x _ hx
    by_cases hxR : x ∈ R
    · simp only [ite_eq_left hxR]
      have he : (pools x).map (fun A => G.reachScore p R A x w) = (pools x).map (fun _ => (0 : ℝ)) := by
        apply List.map_congr_left
        intro A _
        exact G.reachScore_resolved p R A x w hw hx
      simp [he]
    · simp [hxR]
  · simp

/-- The prediction as a sum over exactly the resolved vertices. -/
theorem prediction_eq_sum (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V)) (w : V) :
    G.prediction p R qh pools w = ∑ x ∈ R,
      qh x*((pools x).map (fun A => G.reachScore p R A x w)).sum/(pools x).length := by
  simp [prediction]

/-- The algebra of a real round update: old pools use the enlarged resolved
set, and the new pool contributes its score sum times Φ/M. -/
theorem prediction_after_update (R : Finset V) (qh : V → ℝ)
    (pools : V → List (Finset V)) (v w : V) (hv : v ∉ R)
    (Φ : ℝ) (M : ℕ) (l : List (Finset V)) :
    G.prediction p (insert v R) (Function.update qh v (Φ*l.length/M))
      (Function.update pools v l) w =
      (∑ x ∈ R, qh x*((pools x).map (fun A => G.reachScore p (insert v R) A x w)).sum /
        (pools x).length) + (Φ/M)*(l.map (fun A => G.reachScore p (insert v R) A v w)).sum := by
  rw [G.prediction_eq_sum, Finset.sum_insert hv]
  simp only [Function.update_self]
  have hs : (∑ x ∈ R, (Function.update qh v (Φ*l.length/M)) x *
      (((Function.update pools v l) x).map (fun A => G.reachScore p (insert v R) A x w)).sum /
      ((Function.update pools v l) x).length) =
      ∑ x ∈ R, qh x*((pools x).map (fun A => G.reachScore p (insert v R) A x w)).sum/(pools x).length := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxv : x ≠ v := by intro h; exact hv (h ▸ hx)
    simp [Function.update_of_ne hxv]
  rw [hs]
  have hc := pool_contribution Φ M l (fun A => G.reachScore p (insert v R) A v w)
  rw [← mul_div_assoc] at hc
  rw [hc, add_comm]

/-- The exact expected prediction after the concrete Generate/update pair.
This is the program side of the martingale identity; the DFS splitting
identity must identify the right side with the old prediction. -/
theorem prediction_generate_expectation (R : Finset V) (qh : V → ℝ)
    (pools : V → List (Finset V)) (v w : V) (hv : v ∉ R) {M : ℕ} (hM : 0 < M)
    (Φ : ℝ) :
    (G.sGenerate p R qh pools M v M).exp noOracle
      (fun r => G.prediction p (insert v R) (Function.update qh v (Φ*r.1/M))
        (Function.update pools v r.2) w) =
      (∑ x ∈ R, qh x*((pools x).map (fun A => G.reachScore p (insert v R) A x w)).sum/
        (pools x).length) + Φ * (G.sIter p R qh pools M v).exp noOracle
          (fun o => o.elim 0 (fun A => G.reachScore p (insert v R) A v w)) := by
  let base := ∑ x ∈ R, qh x*((pools x).map (fun A => G.reachScore p (insert v R) A x w)).sum/
    (pools x).length
  let f := fun A => G.reachScore p (insert v R) A v w
  have he := (G.sGenerate_pool p R qh pools M v M).supported.exp_congr
    (f := fun r => G.prediction p (insert v R) (Function.update qh v (Φ*r.1/M))
      (Function.update pools v r.2) w)
    (g := fun r => base+(Φ/M)*(r.2.map f).sum) (fun r hr => by
      rw [hr.1]
      exact G.prediction_after_update p R qh pools v w hv Φ M r.2)
  rw [he, Prog.exp_add, Prog.exp_const, Prog.exp_mul_left,
    G.sGenerate_score_mean p noOracle R qh pools M v f M]
  have hn : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  dsimp [base, f]
  field_simp

/-- The concrete round is unbiased once the DFS last-resolved-vertex
splitting identity is supplied on the stored snapshots. No further
probabilistic assumptions about Generate or the empirical pools are needed. -/
theorem prediction_generate_unbiased_of_split (hp : Prob01 p) (R : Finset V)
    (qh : V → ℝ) (pools : V → List (Finset V)) (v w : V) (hv : v ∉ R)
    {M : ℕ} (hM : 0 < M) (hpool : PoolInvariant R qh pools M)
    (hsplit : ∀ x ∈ R, ∀ A ∈ pools x,
      G.reachScore p R A x w = G.reachScore p (insert v R) A x w +
        G.recordWeight p R x v A (fun D => G.reachScore p (insert v R) D v w)) :
    (G.sGenerate p R qh pools M v M).exp noOracle
      (fun r => G.prediction p (insert v R)
        (Function.update qh v (G.phiS p R qh*r.1/M)) (Function.update pools v r.2) w) =
      G.prediction p R qh pools w := by
  rw [G.prediction_generate_expectation p R qh pools v w hv hM,
    G.sIter_weighted_score p hp R qh pools M hpool,
    G.prediction_eq_sum]
  have hk : (∑ u, if u ∈ R then qh u *
      ((pools u).map (fun A => G.recordWeight p R u v A
        (fun D => G.reachScore p (insert v R) D v w))).sum/(pools u).length else 0) =
      ∑ u ∈ R, qh u*((pools u).map (fun A => G.recordWeight p R u v A
        (fun D => G.reachScore p (insert v R) D v w))).sum/(pools u).length := by simp
  rw [hk, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have he : ((pools x).map (fun A => G.reachScore p R A x w)).sum =
      ((pools x).map (fun A => G.reachScore p (insert v R) A x w)).sum +
      ((pools x).map (fun A => G.recordWeight p R x v A
        (fun D => G.reachScore p (insert v R) D v w))).sum := by
    calc
      _ = ((pools x).map (fun A => G.reachScore p (insert v R) A x w +
          G.recordWeight p R x v A (fun D => G.reachScore p (insert v R) D v w))).sum := by
        congr 1
        exact List.map_congr_left (hsplit x hx)
      _ = _ := List.sum_map_add
  rw [he]
  ring

end Digraph
end
end DirectedCycleFPRAS
