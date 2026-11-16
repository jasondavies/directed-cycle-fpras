module

public import DirectedCycleFPRAS.AlgorithmSParents
public import DirectedCycleFPRAS.AlgorithmSSubtypes

@[expose] public section
namespace DirectedCycleFPRAS
open Classical
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E) (p : E → ℝ)

/-- Generate's iteration using full DFS with explicit parent pointers. -/
def parentIter (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V)) (M : ℕ) (v : V) :
    Prog Empty (Option (Finset V)) :=
  .choose (normLaw (fun o : Option V =>
      o.elim 0 fun u => if u ∈ R then qh u * G.gammaS p R u else 0) none) fun o =>
    o.elim (.ret none) fun u =>
      .choose (normLaw (fun i : Fin (M + 1) =>
          if (i : ℕ) < (pools u).length then (1 : ℝ) else 0) 0) fun i =>
        .choose (normLaw (fun j : Option E => j.elim 0 (G.firstOpenWeight p R u)) none) fun j =>
          j.elim (.ret none) fun j =>
            G.parentDfs p R (G.preState R u j) u v (Fintype.card V + 1)
              ⟨(pools u).getD i ∅, [u], fun _ => none⟩

/-- Only supported choices need a valid pool; invalid zero-weight branches
never affect the output law. -/
theorem parentIter_law (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V))
    (M : ℕ) (hinv : PoolInvariant R qh pools M) (v : V) (f : Option (Finset V) → ℝ) :
    (G.parentIter p R qh pools M v).exp noOracle f =
      (G.sIter p R qh pools M v).exp noOracle f := by
  unfold parentIter sIter
  simp only [Prog.exp]
  apply Finset.sum_congr rfl
  intro o _
  cases o with
  | none => rfl
  | some u =>
    by_cases ho : (normLaw (fun o : Option V => o.elim 0 fun u =>
        if u ∈ R then qh u * G.gammaS p R u else 0) none).value (some u) = 0
    · simp only [ho, zero_mul]
    · have hu : u ∈ R := by
        by_contra hu
        exact ho (normLaw_zero _ none (some u) (by simp) (by simp [hu]))
      have hq : 0 < qh u := by
        apply lt_of_le_of_ne (hinv.nonneg u)
        intro hz
        exact ho (normLaw_zero _ none (some u) (by simp) (by simp [hz.symm]))
      have hlen : 0 < (pools u).length := List.length_pos_iff_ne_nil.mpr ((hinv.positive u hu).mp hq)
      simp only [Option.elim_some, Prog.exp]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : (i : ℕ) < (pools u).length
      · congr 1
        apply Finset.sum_congr rfl
        intro j _
        cases j with
        | none => rfl
        | some j =>
          simp only [Option.elim_some]
          congr 1
          apply G.parentDfs_initial_law
          rw [List.getD_eq_getElem _ _ hi]
          exact hinv.contains u hu _ (List.getElem_mem hi)
      · have hi0 : i ≠ 0 := by intro heq; subst i; exact hi hlen
        have hz := normLaw_zero (fun i : Fin (M + 1) =>
          if (i : ℕ) < (pools u).length then (1 : ℝ) else 0) 0 i hi0 (by simp [hi])
        simp only [hz, zero_mul]

def parentGenerate (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V)) (M : ℕ) (v : V) :
    ℕ → Prog Empty (ℕ × List (Finset V))
  | 0 => .ret (0, [])
  | i + 1 => (parentGenerate R qh pools M v i).bind fun acc =>
      (G.parentIter p R qh pools M v).bind fun o =>
        .ret (o.elim acc fun D => (acc.1 + 1, D :: acc.2))

theorem parentGenerate_law (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V))
    (M : ℕ) (hinv : PoolInvariant R qh pools M) (v : V) (i : ℕ) (f : ℕ × List (Finset V) → ℝ) :
    (G.parentGenerate p R qh pools M v i).exp noOracle f =
      (G.sGenerate p R qh pools M v i).exp noOracle f := by
  induction i generalizing f with
  | zero => rfl
  | succ i ih =>
    simp only [parentGenerate, sGenerate, Prog.exp_bind, G.parentIter_law p R qh pools M hinv]
    exact ih _

def parentRounds (t : V) (M : ℕ) :
    ℕ → Finset V → (V → ℝ) → (V → List (Finset V)) → Prog Empty ℝ
  | 0, _, qh, _ => .ret (qh t)
  | f + 1, R, qh, pools =>
    if t ∈ R then .ret (qh t)
    else
      (((arcOrder E).filter fun e => G.source e ∈ R ∧ G.target e ∉ R).argmax
          fun e => qh (G.source e) * p e).elim (.ret 0) fun e =>
        if qh (G.source e) * p e ≤ 0 then .ret 0
        else
          (G.parentGenerate p R qh pools M (G.target e) M).bind fun res =>
            parentRounds t M f (insert (G.target e) R)
              (Function.update qh (G.target e) (G.phiS p R qh * res.1 / M))
              (Function.update pools (G.target e) res.2)

/-- The explicit parent-pointer algorithm has the same output law through
all rounds, not just within an isolated DFS invocation. -/
theorem parentRounds_law (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (t : V) {M : ℕ} (hM : 0 < M) (fuel : ℕ) (R : Finset V) (qh : V → ℝ)
    (pools : V → List (Finset V)) (hinv : PoolInvariant R qh pools M) (f : ℝ → ℝ) :
    (G.parentRounds p t M fuel R qh pools).exp noOracle f =
      (G.sRounds p t M fuel R qh pools).exp noOracle f := by
  induction fuel generalizing R qh pools f with
  | zero => rfl
  | succ fuel ih =>
    simp only [parentRounds, sRounds]
    split_ifs
    · rfl
    · generalize he : (((arcOrder E).filter fun e => G.source e ∈ R ∧ G.target e ∉ R).argmax
        fun e => qh (G.source e) * p e) = o
      cases o with
      | none => rfl
      | some e =>
        have hmem := List.argmax_mem (show e ∈ (((arcOrder E).filter
          fun e => G.source e ∈ R ∧ G.target e ∉ R).argmax
          fun e => qh (G.source e) * p e) by rw [he]; simp)
        have hcut : G.source e ∈ R ∧ G.target e ∉ R := by
          simpa using (List.mem_filter.mp hmem).2
        simp only [Option.elim_some]
        split_ifs with hscore
        · rfl
        · symm
          apply (G.sGenerate_records p R qh pools M hinv (G.target e) M).exp_bind_congr
            (fun g => (G.parentGenerate_law p R qh pools M hinv (G.target e) M g).symm)
          intro res hres g
          exact (ih _ _ _ (hinv.update hM (G.target e) (G.phiS p R qh)
            (G.phiS_pos p hp0 hp1 R qh hinv.nonneg e hcut (lt_of_not_ge hscore))
            res.1 res.2 hres.1 hres.2.1 hres.2.2) g).symm

/-- Algorithm S with an explicit parent table and full exploration after recording. -/
def parentAlgS (s t : V) (M : ℕ) : Prog Empty ℝ :=
  G.parentRounds p t M (Fintype.card V) {s} (fun u => if u = s then 1 else 0)
    (fun u => if u = s then [{s}] else [])

theorem parentAlgS_law (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (s t : V) {M : ℕ} (hM : 0 < M) (f : ℝ → ℝ) :
    (G.parentAlgS p s t M).exp noOracle f = (G.algS p s t M).exp noOracle f :=
  G.parentRounds_law p hp0 hp1 t hM _ _ _ _ (initial_poolInvariant s hM) f

/-- Combining the two simulations: explicit parent-pointer Algorithm S on
the ambient graph agrees with the induced-subtype transcription. -/
theorem parentAlgS_inducedClosed (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (U : Finset V) (hU : ∀ e, G.source e ∈ U → G.target e ∈ U)
    (s t : U) {M : ℕ} (hM : 0 < M) (f : ℝ → ℝ) :
    (G.parentAlgS p s.val t.val M).exp noOracle f =
      ((G.inducedClosed U hU).orderedAlgS (fun e => p e.val) (G.subtypeOrder U (arcOrder E))
        (fun e => (arcOrder E).idxOf e.val) (Fintype.card V + 1) (Fintype.card V)
        s t M).exp noOracle f :=
  (G.parentAlgS_law p hp0 hp1 s.val t.val hM f).trans (G.algS_inducedClosed p U hU s t M f).symm

end Digraph
end
end DirectedCycleFPRAS
