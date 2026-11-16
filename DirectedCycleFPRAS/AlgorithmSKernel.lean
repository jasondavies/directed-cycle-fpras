module

public import DirectedCycleFPRAS.AlgorithmSPools

@[expose] public section

/-! Exact weighted law of one Generate iteration. This separates the
normalization and pool bookkeeping from the DFS snapshot decomposition. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section

/-- Multiplying a normalized expectation by its total weight recovers the
weighted sum. Zero total weight is allowed. -/
theorem normLaw_weighted_expectation {I : Type} [Fintype I] (w : I → ℝ) (d : I)
    (hw : ∀ i, 0 ≤ w i) (f : I → ℝ) :
    (∑ i, w i) * (∑ i, (normLaw w d).value i * f i) = ∑ i, w i*f i := by
  have hs : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => hw i
  rcases hs.eq_or_lt with hz | hp
  · have hi (i : I) : w i = 0 := by
      have h := Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)
      rw [← hz] at h
      exact le_antisymm h (hw i)
    simp [hi]
  · simp_rw [normLaw_value w d hw hp]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp

namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E) (p : E → ℝ)

/-- First-open mixture of the DFS record score, before normalization. -/
def recordWeight (R : Finset V) (u v : V) (D : Finset V) (f : Finset V → ℝ) : ℝ :=
  ∑ e, G.firstOpenWeight p R u e *
    (G.sDfs (Q := Empty) p R (G.preState R u e) v (Fintype.card V+1)
      D [(u,true)]).exp noOracle (fun o => o.elim 0 f)

/-- The edge-choice normalization cancels against the cut probability,
including a zero-probability cut. -/
theorem recordWeight_eq (hp : Prob01 p) (R : Finset V) (u v : V)
    (D : Finset V) (f : Finset V → ℝ) :
    G.gammaS p R u *
      (Prog.choose (normLaw (fun j : Option E => j.elim 0 (G.firstOpenWeight p R u)) none)
        (fun j => j.elim (.ret none) fun e =>
          G.sDfs (Q := Empty) p R (G.preState R u e) v (Fintype.card V+1) D [(u,true)])).exp
        noOracle (fun o => o.elim 0 f) = G.recordWeight p R u v D f := by
  have hw (j : Option E) : 0 ≤ j.elim 0 (G.firstOpenWeight p R u) := by
    cases j with
    | none => exact le_rfl
    | some e => exact G.firstOpenWeight_nonneg p (fun e => (hp e).1) (fun e => (hp e).2) R u e
  have h := normLaw_weighted_expectation
    (fun j : Option E => j.elim 0 (G.firstOpenWeight p R u)) none hw
    (fun j => (j.elim (.ret none) fun e =>
      G.sDfs (Q := Empty) p R (G.preState R u e) v (Fintype.card V+1) D [(u,true)]).exp
      noOracle (fun o => o.elim 0 f))
  simpa only [Fintype.sum_option, Option.elim_none, Option.elim_some, zero_add,
    zero_mul, Prog.exp, gammaS, recordWeight] using h

/-- The complete weighted Generate proposal law. The right side retains
both duplicate snapshots and their empirical multiplicities. -/
theorem sIter_weighted_score (hp : Prob01 p) (R : Finset V) (qh : V → ℝ)
    (pools : V → List (Finset V)) (M : ℕ) (hpool : PoolInvariant R qh pools M)
    (v : V) (f : Finset V → ℝ) :
    G.phiS p R qh * (G.sIter p R qh pools M v).exp noOracle (fun o => o.elim 0 f) =
      ∑ u, if u ∈ R then qh u * ((pools u).map (fun D => G.recordWeight p R u v D f)).sum /
        (pools u).length else 0 := by
  let K (u : V) : Prog Empty (Option (Finset V)) :=
    .choose (normLaw (fun i : Fin (M+1) => if (i : ℕ) < (pools u).length then (1 : ℝ) else 0) 0)
      fun i => .choose (normLaw (fun j : Option E => j.elim 0 (G.firstOpenWeight p R u)) none)
        fun j => j.elim (.ret none) fun e =>
          G.sDfs p R (G.preState R u e) v (Fintype.card V+1) ((pools u).getD i ∅) [(u,true)]
  have hw (o : Option V) : 0 ≤ o.elim 0 (fun u => if u ∈ R then qh u*G.gammaS p R u else 0) := by
    cases o with
    | none => exact le_rfl
    | some u =>
      dsimp
      split_ifs
      · exact mul_nonneg (hpool.nonneg u) (G.gammaS_nonneg p (fun e => (hp e).1) (fun e => (hp e).2) R u)
      · exact le_rfl
  have hout := normLaw_weighted_expectation
    (fun o : Option V => o.elim 0 (fun u => if u ∈ R then qh u*G.gammaS p R u else 0)) none hw
    (fun o => (o.elim (.ret none) K).exp noOracle (fun o => o.elim 0 f))
  simp only [Fintype.sum_option, Option.elim_none, Option.elim_some, zero_add, zero_mul] at hout
  have houter : G.phiS p R qh * (G.sIter p R qh pools M v).exp noOracle (fun o => o.elim 0 f) =
      ∑ u, (if u ∈ R then qh u*G.gammaS p R u else 0)*(K u).exp noOracle (fun o => o.elim 0 f) := by
    simpa only [sIter, phiS, K, Prog.exp, Fintype.sum_option, Option.elim_none,
      Option.elim_some, mul_zero, zero_add] using hout
  rw [houter]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u ∈ R
  · simp only [ite_eq_left hu]
    by_cases hl : pools u = []
    · have hz : qh u = 0 := by
        apply le_antisymm _ (hpool.nonneg u)
        by_contra h
        exact ((hpool.positive u hu).mp (lt_of_not_ge h)) hl
      simp [hz]
    · have hpoint (i : Fin (M+1)) := G.recordWeight_eq p hp R u v ((pools u).getD i ∅) f
      have hinner : G.gammaS p R u * (K u).exp noOracle (fun o => o.elim 0 f) =
          ((pools u).map (fun D => G.recordWeight p R u v D f)).sum/(pools u).length := by
        change G.gammaS p R u * (∑ i : Fin (M+1), _ * _) = _
        rw [Finset.mul_sum]
        have he (i : Fin (M+1)) : G.gammaS p R u *
            ((normLaw (fun i : Fin (M+1) => if (i : ℕ) < (pools u).length then (1 : ℝ) else 0) 0).value i *
              (Prog.choose (normLaw (fun j : Option E => j.elim 0 (G.firstOpenWeight p R u)) none)
                (fun j => j.elim (.ret none) fun e => G.sDfs (Q := Empty) p R (G.preState R u e) v
                  (Fintype.card V+1) ((pools u).getD i ∅) [(u,true)])).exp noOracle (fun o => o.elim 0 f)) =
            (normLaw (fun i : Fin (M+1) => if (i : ℕ) < (pools u).length then (1 : ℝ) else 0) 0).value i *
              G.recordWeight p R u v ((pools u).getD i ∅) f := by
          rw [mul_left_comm, hpoint i]
        simp_rw [he]
        simpa using poolDraw_expectation (pools u) ∅ (M+1) (by omega)
          (Nat.le_succ_of_le (hpool.length_le u hu)) hl
          (fun D => G.recordWeight p R u v D f)
      rw [mul_assoc, hinner]
      ring
  · simp [hu]

end Digraph
end
end DirectedCycleFPRAS
