module

public import DirectedCycleFPRAS.AlgorithmSUnbiased
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-! Conditional variance estimates for the concrete pool updates, including
unreachable vertices whose true reliability is zero. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
namespace Prog
variable {Q S : Type}
theorem exp_div (O : Oracle Q) (m : Prog Q S) (f : S → ℝ) (c : ℝ) :
    m.exp O (fun x => f x/c) = m.exp O f/c := by
  simpa [div_eq_mul_inv,mul_comm] using exp_mul_left O m c⁻¹ f

theorem exp_square_sum_le (O : Oracle Q) (m : Prog Q S) {I : Type} [Fintype I] (f : I → S → ℝ) :
    m.exp O (fun x => (∑ i, f i x)^2) ≤ Fintype.card I * ∑ i, m.exp O (fun x => (f i x)^2) := by
  have h := exp_mono O m (fun x => sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => f i x))
  simpa only [Finset.card_univ,exp_mul_left,exp_sum] using h
end Prog

namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [ArcEnumeration E] [DecidableEq E]
variable (G : Digraph V E) (p : E → ℝ)

def totalPrediction (s : V) (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V)) : ℝ :=
  ∑ w, G.prediction p R qh pools w / G.reliability p s w

theorem reliability_nonneg (hp : Prob01 p) (s w : V) : 0 ≤ G.reliability p s w :=
  eventMass_nonneg hp _

theorem phiS_nonneg (hp : Prob01 p) (R : Finset V) (qh : V → ℝ) (hq : ∀ x, 0 ≤ qh x) :
    0 ≤ G.phiS p R qh := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact mul_nonneg (hq x) (G.gammaS_nonneg p (fun e => (hp e).1) (fun e => (hp e).2) R x)
  · exact le_rfl

theorem totalPrediction_nonneg (hp : Prob01 p) (s : V) (R : Finset V) (qh : V → ℝ)
    (pools : V → List (Finset V)) (hq : ∀ x, 0 ≤ qh x) :
    0 ≤ G.totalPrediction p s R qh pools :=
  Finset.sum_nonneg fun w _ => div_nonneg (G.prediction_nonneg p R qh pools hq w) (G.reliability_nonneg p hp s w)

theorem prediction_div_le_total (hp : Prob01 p) (s : V) (R : Finset V) (qh : V → ℝ)
    (pools : V → List (Finset V)) (hq : ∀ x, 0 ≤ qh x) (w : V) :
    G.prediction p R qh pools w / G.reliability p s w ≤ G.totalPrediction p s R qh pools :=
  Finset.single_le_sum (fun u _ => div_nonneg (G.prediction_nonneg p R qh pools hq u)
    (G.reliability_nonneg p hp s u)) (Finset.mem_univ w)

theorem totalPrediction_initial (hp : Prob01 p) (s : V) :
    G.totalPrediction p s {s} (fun x => if x=s then 1 else 0)
      (fun x => if x=s then [{s}] else []) ≤ Fintype.card V := by
  unfold totalPrediction
  simp_rw [G.prediction_initial p hp]
  calc
    _ ≤ ∑ _w : V, (1 : ℝ) := Finset.sum_le_sum fun w _ => div_self_le_one _
    _ = _ := by simp

/-- The complete concrete one-round prediction variance, FFG Lemma 11.
Only the selected arc's max-score property and positive true source/target
reliability are required; other vertices may be unreachable. -/
theorem prediction_generate_variance (hp : Prob01 p) (s : V) (R : Finset V)
    (qh : V → ℝ) (pools : V → List (Finset V)) {M : ℕ} (hM : 0 < M)
    (hpool : PoolInvariant R qh pools M) (e : E) (he : G.source e∈R ∧ G.target e∉R)
    (hmax : ∀ j, G.source j∈R ∧ G.target j∉R → qh (G.source j)*p j ≤ qh (G.source e)*p e)
    (hu : 0 < G.reliability p s (G.source e)) (hv : 0 < G.reliability p s (G.target e)) (w : V) :
    (G.sGenerate p R qh pools M (G.target e) M).exp noOracle
      (fun r => (G.prediction p (insert (G.target e) R)
        (Function.update qh (G.target e) (G.phiS p R qh*r.1/M))
        (Function.update pools (G.target e) r.2) w - G.prediction p R qh pools w)^2) ≤
      (Fintype.card E/M)*(qh (G.source e)/G.reliability p s (G.source e))*
        G.reliability p s w * G.prediction p R qh pools w := by
  let v := G.target e
  let Φ := G.phiS p R qh
  let q := G.prediction p R qh pools w
  let f : Finset V → ℝ := fun D => if v∈D then G.reachScore p (insert v R) D v w else 0
  let μ := (G.sIter p R qh pools M v).exp noOracle (fun o => o.elim 0 f)
  let base := ∑ x ∈ R, qh x*((pools x).map (fun A => G.reachScore p (insert v R) A x w)).sum/(pools x).length
  have hμ : (G.sIter p R qh pools M v).exp noOracle
      (fun o => o.elim 0 (fun D => G.reachScore p (insert v R) D v w)) = μ := by
    apply (G.sIter_records p R qh pools M hpool v).exp_congr
    intro o ho
    cases o with
    | none => rfl
    | some D => simp [f,ho D (by simp)]
  have hmean : q=base+Φ*μ := by
    have h := G.prediction_generate_expectation p R qh pools v w he.2 hM Φ
    rw [G.prediction_generate_unbiased p hp R qh pools v w he.2 hM hpool, hμ] at h
    exact h
  have hb0 : 0 ≤ base := by
    apply Finset.sum_nonneg
    intro x _
    apply div_nonneg
    · apply mul_nonneg (hpool.nonneg x)
      apply List.sum_nonneg
      intro a ha
      obtain ⟨A,_,rfl⟩ := List.mem_map.mp ha
      exact G.reachScore_nonneg p _ _ _ _
    · positivity
  have hpoint (r : ℕ × List (Finset V))
      (hr : r.1=r.2.length ∧ r.1≤M ∧ ∀ D∈r.2, v∈D) :
      (G.prediction p (insert v R) (Function.update qh v (Φ*r.1/M))
        (Function.update pools v r.2) w-q)^2 = (q-Φ*μ+(Φ/M)*(r.2.map f).sum-q)^2 := by
    rw [hr.1, G.prediction_after_update p R qh pools v w he.2 Φ M]
    have hl : r.2.map f = r.2.map (fun D => G.reachScore p (insert v R) D v w) := by
      apply List.map_congr_left
      intro D hD
      simp [f,hr.2.2 D hD]
    rw [hl,hmean]
    dsimp only [base]
    ring
  rw [(G.sGenerate_records p R qh pools M hpool v M).exp_congr hpoint]
  apply (G.sGenerate_scored_law p noOracle R qh pools M v f M
    (fun a => (q-Φ*μ+(Φ/M)*a-q)^2)).trans_le
  have hvar := Prog.prediction_update_variance_le noOracle
    (G.sIter p R qh pools M v) (fun o => o.elim 0 f) Φ q
    (Fintype.card E*(qh (G.source e)/G.reliability p s (G.source e)))
    (G.reliability p s v) (G.reliability p s w) hM
    (G.phiS_nonneg p hp R qh hpool.nonneg) (G.prediction_nonneg p R qh pools hpool.nonneg w)
    hv (G.reliability_nonneg p hp s w)
    (by
      intro o; cases o with
      | none => exact le_rfl
      | some D => dsimp [f]; split_ifs; exact G.reachScore_nonneg p _ _ _ _; exact le_rfl)
    (by
      intro o; cases o with
      | none => exact div_nonneg (G.reliability_nonneg p hp s w) hv.le
      | some D =>
        dsimp [f]; split_ifs with hD
        · exact G.reachScore_le_ratio p hp _ D s v w hD hv
        · exact div_nonneg (G.reliability_nonneg p hp s w) hv.le)
    (by
      have h := G.phiS_le_reliability_ratio p hp s R qh hpool.nonneg e hmax hu
      dsimp [Φ,v]
      convert h using 1; ring)
    (by rw [hmean]; linarith)
  convert hvar using 1; ring

/-- Summing normalized predictions preserves the martingale identity. -/
theorem totalPrediction_generate_mean (hp : Prob01 p) (s : V) (R : Finset V)
    (qh : V → ℝ) (pools : V → List (Finset V)) (v : V) (hv : v∉R)
    {M : ℕ} (hM : 0<M) (hpool : PoolInvariant R qh pools M) :
    (G.sGenerate p R qh pools M v M).exp noOracle
      (fun r => G.totalPrediction p s (insert v R)
        (Function.update qh v (G.phiS p R qh*r.1/M)) (Function.update pools v r.2)) =
      G.totalPrediction p s R qh pools := by
  simp only [totalPrediction,Prog.exp_sum,Prog.exp_div,
    G.prediction_generate_unbiased p hp R qh pools v _ hv hM hpool]

/-- The normalized source estimate is a term of the total prediction. -/
theorem estimate_div_le_total (hp : Prob01 p) (s : V) (R : Finset V)
    (qh : V → ℝ) (pools : V → List (Finset V)) (M : ℕ)
    (hpool : PoolInvariant R qh pools M) (u : V) (hu : u∈R) :
    qh u/G.reliability p s u ≤ G.totalPrediction p s R qh pools := by
  rw [← G.prediction_resolved p R qh pools M hpool u hu]
  exact G.prediction_div_le_total p hp s R qh pools hpool.nonneg u

/-- The two local variance bounds used by the quantitative martingale
argument. Cauchy--Schwarz handles correlations between vertex predictions. -/
theorem prediction_generate_variance_bounds (hp : Prob01 p) (s : V) (R : Finset V)
    (qh : V → ℝ) (pools : V → List (Finset V)) {M : ℕ} (hM : 0<M)
    (hpool : PoolInvariant R qh pools M) (e : E) (he : G.source e∈R ∧ G.target e∉R)
    (hmax : ∀ j, G.source j∈R ∧ G.target j∉R → qh (G.source j)*p j ≤ qh (G.source e)*p e)
    (hu : 0<G.reliability p s (G.source e)) (hv : 0<G.reliability p s (G.target e))
    (t : V) (ht : 0<G.reliability p s t) :
    let gen := G.sGenerate (Q := Empty) p R qh pools M (G.target e) M
    let next := fun r w => G.prediction p (insert (G.target e) R)
      (Function.update qh (G.target e) (G.phiS p R qh*r.1/M))
      (Function.update pools (G.target e) r.2) w
    let Ψ := G.totalPrediction p s R qh pools
    gen.exp noOracle (fun r => (next r t-G.prediction p R qh pools t)^2) ≤
      (Fintype.card E/M)*(G.reliability p s t)^2*Ψ^2 ∧
    gen.exp noOracle (fun r => ((∑ w, next r w/G.reliability p s w)-Ψ)^2) ≤
      (Fintype.card V*Fintype.card E/M)*Ψ^2 := by
  dsimp only
  let Ψ := G.totalPrediction p s R qh pools
  let c := qh (G.source e)/G.reliability p s (G.source e)
  let q := fun w => G.reliability p s w
  let old := fun w => G.prediction p R qh pools w
  let gen := G.sGenerate (Q := Empty) p R qh pools M (G.target e) M
  let next := fun (r : ℕ × List (Finset V)) w => G.prediction p (insert (G.target e) R)
    (Function.update qh (G.target e) (G.phiS p R qh*r.1/M))
    (Function.update pools (G.target e) r.2) w
  have hc0 : 0≤c := div_nonneg (hpool.nonneg _) hu.le
  have hΨ0 : 0≤Ψ := G.totalPrediction_nonneg p hp s R qh pools hpool.nonneg
  have hcΨ : c≤Ψ := G.estimate_div_le_total p hp s R qh pools M hpool _ he.1
  have hMr : (0 : ℝ)<M := by exact_mod_cast hM
  have hfactor : 0≤(Fintype.card E : ℝ)/M := by positivity
  have hvar (w : V) : gen.exp noOracle (fun r => (next r w-old w)^2) ≤
      (Fintype.card E/M)*c*q w*old w :=
    G.prediction_generate_variance p hp s R qh pools hM hpool e he hmax hu hv w
  constructor
  · apply (hvar t).trans
    have hQ : old t ≤ q t*Ψ := by
      have h := (div_le_iff₀ ht).mp (G.prediction_div_le_total p hp s R qh pools hpool.nonneg t)
      simpa [mul_comm] using h
    have h0 : 0≤old t := G.prediction_nonneg p R qh pools hpool.nonneg t
    have hprod := mul_le_mul hcΨ hQ h0 hΨ0
    have h := mul_le_mul_of_nonneg_left hprod (mul_nonneg hfactor ht.le)
    convert h using 1 <;> ring
  · change gen.exp noOracle (fun r => ((∑ w, next r w/q w)-Ψ)^2) ≤ _
    have hexpand (r) : (∑ w, next r w/q w)-Ψ = ∑ w, (next r w-old w)/q w := by
      simp [Ψ,totalPrediction,old,q,sub_div,Finset.sum_sub_distrib]
    simp_rw [hexpand]
    apply (Prog.exp_square_sum_le noOracle gen (fun w r => (next r w-old w)/q w)).trans
    have hn (w : V) : gen.exp noOracle (fun r => ((next r w-old w)/q w)^2) ≤
        ((Fintype.card E : ℝ)/M)*c*(old w/q w) := by
      by_cases hq : q w=0
      · simp [hq,Prog.exp_const]
      · have hqw : 0<q w := lt_of_le_of_ne (G.reliability_nonneg p hp s w) (Ne.symm hq)
        simp_rw [div_pow]
        rw [Prog.exp_div]
        apply (div_le_div_of_nonneg_right (hvar w) (sq_nonneg _)).trans_eq
        field_simp
    have hsum := Finset.sum_le_sum (fun w (_ : w∈Finset.univ) => hn w)
    rw [← Finset.mul_sum] at hsum
    change _ ≤ ((Fintype.card E : ℝ)/M)*c*Ψ at hsum
    have h := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (Fintype.card V))
    apply h.trans
    have hp' := mul_le_mul_of_nonneg_right hcΨ hΨ0
    have hh := mul_le_mul_of_nonneg_left hp' (mul_nonneg (Nat.cast_nonneg (Fintype.card V)) hfactor)
    convert hh using 1 <;> ring

end Digraph
end
end DirectedCycleFPRAS
