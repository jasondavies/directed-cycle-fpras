module

public import DirectedCycleFPRAS.AlgorithmSRestriction
public import DirectedCycleFPRAS.FirstOpen

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
private theorem sum_valid_indices (N L : ℕ) (hL : L ≤ N) (f : ℕ → ℝ) :
    (∑ i : Fin N, if (i : ℕ) < L then f i else 0) = ∑ i : Fin L, f i := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin L))
  · intro i hi; exact Finset.mem_univ _
  · intro i hi j hj hij; exact Fin.ext (congrArg (fun i : Fin L => i.val) hij)
  · intro i _
    refine ⟨⟨i.val, lt_of_lt_of_le i.isLt hL⟩, by simp, rfl⟩
  · intro i hi; rfl

/-- The padded finite-index draw is exactly uniform on the actual list,
counting duplicate entries with their multiplicities. -/
theorem poolDraw_expectation {α : Type} (l : List α) (d : α) (N : ℕ)
    (hN : 0 < N) (hL : l.length ≤ N) (hl : l ≠ []) (f : α → ℝ) :
    (∑ i : Fin N, (normLaw (fun i : Fin N => if (i : ℕ) < l.length then (1 : ℝ) else 0)
      ⟨0, hN⟩).value i * f (l.getD i d)) = (l.map f).sum / l.length := by
  have hsum : (∑ i : Fin N, if (i : ℕ) < l.length then (1 : ℝ) else 0) = l.length := by
    rw [sum_valid_indices N l.length hL (fun _ => 1)]; simp
  have hpos : (0 : ℝ) < l.length := by exact_mod_cast List.length_pos_iff_ne_nil.mpr hl
  simp_rw [normLaw_value _ _ (fun i => by split_ifs <;> norm_num) (hsum.symm ▸ hpos)]
  rw [hsum]
  have hterm : ∀ i : Fin N,
      (if (i : ℕ) < l.length then (1 : ℝ) else 0) / l.length * f (l.getD i d) =
      (if (i : ℕ) < l.length then f (l.getD i d) else 0) / l.length := by
    intro i
    split_ifs <;> ring
  simp_rw [hterm]
  rw [← Finset.sum_div, sum_valid_indices N l.length hL (fun i => f (l.getD i d))]
  congr 1
  have hget : (fun i : Fin l.length => f (l.getD i d)) = fun i => f (l[i.val]) := by
    funext i; rw [List.getD_eq_getElem _ _ i.isLt]
  rw [hget, ← List.sum_ofFn]
  have hm := List.map_ofFn (f := fun i : Fin l.length => l[i.val]) (g := f)
  simp only [Function.comp_def] at hm
  rw [← hm, List.ofFn_getElem]

/-- Reordering stored snapshots, including prepending versus appending,
does not alter their uniform-sampling law. -/
theorem poolDraw_perm {α : Type} {l l' : List α} (hperm : l.Perm l') (d : α) (N : ℕ)
    (hN : 0 < N) (hL : l.length ≤ N) (hl : l ≠ []) (f : α → ℝ) :
    (∑ i : Fin N, (normLaw (fun i : Fin N => if (i : ℕ) < l.length then (1 : ℝ) else 0)
      ⟨0, hN⟩).value i * f (l.getD i d)) =
    (∑ i : Fin N, (normLaw (fun i : Fin N => if (i : ℕ) < l'.length then (1 : ℝ) else 0)
      ⟨0, hN⟩).value i * f (l'.getD i d)) := by
  have hl' : l' ≠ [] := by intro h; have := hperm.length_eq; simp [h] at this; exact hl this
  rw [poolDraw_expectation l d N hN hL hl f,
    poolDraw_expectation l' d N hN (hperm.length_eq ▸ hL) hl' f,
    (hperm.map f).sum_eq, hperm.length_eq]

namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E) (p : E → ℝ)

theorem firstOpenWeight_nonneg (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (R : Finset V) (u : V) (e : E) : 0 ≤ G.firstOpenWeight p R u e := by
  unfold firstOpenWeight
  split_ifs
  · exact mul_nonneg (hp0 e) (Finset.prod_nonneg fun e _ => sub_nonneg.mpr (hp1 e))
  · exact le_rfl

theorem gammaS_nonneg (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (R : Finset V) (u : V) : 0 ≤ G.gammaS p R u :=
  Finset.sum_nonneg fun e _ => G.firstOpenWeight_nonneg p hp0 hp1 R u e

/-- A positive cut edge gives a positive cut-event probability, even when
some other cut edges have probabilities zero or one. -/
theorem gammaS_pos (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (R : Finset V) (u : V) (e : E) (he : G.cutAt R u e) (hpe : 0 < p e) :
    0 < G.gammaS p R u := by
  let S := Finset.univ.filter fun j => G.cutAt R u j ∧ 0 < p j
  have hS : S.Nonempty := ⟨e, by simp [S, he, hpe]⟩
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image S (fun j => (arcOrder E).idxOf j) hS
  have hj' := (Finset.mem_filter.mp hj).2
  have hprod : (∏ e' ∈ Finset.univ.filter (fun e' => G.cutAt R u e' ∧ arcBefore e' j),
      (1 - p e')) = 1 := by
    apply Finset.prod_eq_one
    intro e' he'
    have he'' := (Finset.mem_filter.mp he').2
    have hz : p e' = 0 := by
      apply le_antisymm _ (hp0 e')
      by_contra hn
      have : e' ∈ S := by simp [S, he''.1, lt_of_not_ge hn]
      exact (not_lt_of_ge (hmin e' this)) he''.2
    simp [hz]
  have hjpos : 0 < G.firstOpenWeight p R u j := by
    simpa [firstOpenWeight, hj'.1, hprod] using hj'.2
  exact hjpos.trans_le (Finset.single_le_sum
    (fun e _ => G.firstOpenWeight_nonneg p hp0 hp1 R u e) (Finset.mem_univ j))

theorem phiS_pos (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (R : Finset V) (qh : V → ℝ) (hqh : ∀ u, 0 ≤ qh u) (e : E)
    (he : G.source e ∈ R ∧ G.target e ∉ R) (hscore : 0 < qh (G.source e) * p e) :
    0 < G.phiS p R qh := by
  have hq : 0 < qh (G.source e) := (mul_pos_iff.mp hscore).resolve_right
    (fun h => (not_lt_of_ge (hqh _)) h.1) |>.1
  have hp : 0 < p e := (mul_pos_iff.mp hscore).resolve_right
    (fun h => (not_lt_of_ge (hp0 _)) h.2) |>.2
  have hg := G.gammaS_pos p hp0 hp1 R (G.source e) e ⟨rfl, he.2⟩ hp
  have hterm : 0 < (if G.source e ∈ R then qh (G.source e) * G.gammaS p R (G.source e) else 0) := by
    simpa [he.1] using mul_pos hq hg
  exact hterm.trans_le (Finset.single_le_sum (f := fun u => if u ∈ R then qh u * G.gammaS p R u else 0) (fun u _ => by
    split_ifs
    · exact mul_nonneg (hqh u) (G.gammaS_nonneg p hp0 hp1 R u)
    · exact le_rfl) (Finset.mem_univ (G.source e)))

/-- Invariants needed to interpret indexed pools as the paper's snapshot pools. -/
structure PoolInvariant (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V)) (M : ℕ) : Prop where
  nonneg : ∀ u, 0 ≤ qh u
  positive : ∀ u ∈ R, 0 < qh u ↔ pools u ≠ []
  length_le : ∀ u ∈ R, (pools u).length ≤ M
  contains : ∀ u ∈ R, ∀ D ∈ pools u, u ∈ D

/-- Positive-probability iteration branches use a real pool entry, and each
accepted record contains the target, making n+1 DFS fuel sufficient. -/
theorem sIter_records (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V))
    (M : ℕ) (hinv : PoolInvariant R qh pools M) (v : V) :
    Prog.Supported (fun o : Option (Finset V) => ∀ D ∈ o, v ∈ D)
      (G.sIter p R qh pools M v) := by
  refine .choose _ _ ?_
  intro o ho
  cases o with
  | none => exact .ret _ (by simp)
  | some u =>
    have hu : u ∈ R := by
      by_contra hu
      exact ho (normLaw_zero _ none (some u) (by simp) (by simp [hu]))
    have hq : 0 < qh u := by
      apply lt_of_le_of_ne (hinv.nonneg u)
      intro hz
      exact ho (normLaw_zero _ none (some u) (by simp) (by simp [hz.symm]))
    have hlen : 0 < (pools u).length := List.length_pos_iff_ne_nil.mpr ((hinv.positive u hu).mp hq)
    refine .choose _ _ ?_
    intro i hi
    have hvalid : (i : ℕ) < (pools u).length := by
      by_contra hbad
      have hi0 : i ≠ 0 := by intro heq; subst i; exact hbad hlen
      exact hi (normLaw_zero _ 0 i hi0 (by simp [hbad]))
    refine .choose _ _ ?_
    intro j _
    cases j with
    | none => exact .ret _ (by simp)
    | some j =>
      have hentry : u ∈ (pools u).getD i ∅ := by
        rw [List.getD_eq_getElem _ _ hvalid]
        exact hinv.contains u hu _ (List.getElem_mem hvalid)
      exact ((G.sDfs_closed p Finset.univ R (by simp) _ v _ _ _
        (Finset.subset_univ _) (by simpa using hentry)).imp fun o ho D hD => (ho D hD).2).supported

/-- Generate preserves the exact pool count and target-membership invariant. -/
theorem sGenerate_records (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V))
    (M : ℕ) (hinv : PoolInvariant R qh pools M) (v : V) (i : ℕ) :
    Prog.Supported (fun r : ℕ × List (Finset V) =>
      r.1 = r.2.length ∧ r.1 ≤ i ∧ ∀ D ∈ r.2, v ∈ D)
      (G.sGenerate p R qh pools M v i) := by
  induction i with
  | zero => exact .ret _ (by simp)
  | succ i ih =>
    apply ih.bind
    intro acc hacc
    apply (G.sIter_records p R qh pools M hinv v).bind
    intro o ho
    cases o with
    | none => exact .ret _ ⟨hacc.1, by simpa using Nat.le_succ_of_le hacc.2.1, hacc.2.2⟩
    | some D =>
      refine .ret _ ⟨by simpa using congrArg Nat.succ hacc.1, by simpa using Nat.succ_le_succ hacc.2.1, ?_⟩
      simpa only [Option.elim_some, List.mem_cons, forall_eq_or_imp] using And.intro (ho D (by simp)) hacc.2.2

/-- Every continuing round preserves the pool invariants. -/
theorem PoolInvariant.update {R : Finset V} {qh : V → ℝ} {pools : V → List (Finset V)}
    {M : ℕ} (hinv : PoolInvariant R qh pools M) (hM : 0 < M)
    (v : V) (Φ : ℝ) (hΦ : 0 < Φ) (count : ℕ) (pool : List (Finset V))
    (hc : count = pool.length) (hcount : count ≤ M) (hpool : ∀ D ∈ pool, v ∈ D) :
    PoolInvariant (insert v R) (Function.update qh v (Φ * count / M))
      (Function.update pools v pool) M := by
  constructor
  · intro u
    by_cases hu : u = v
    · subst u; rw [Function.update_self]; positivity
    · rw [Function.update_of_ne hu]; exact hinv.nonneg u
  · intro u hu
    by_cases huv : u = v
    · subst u
      simpa using generated_positive_iff Φ hΦ hM pool hc
    · simpa [Function.update_of_ne huv] using
        hinv.positive u (Finset.mem_of_mem_insert_of_ne hu huv)
  · intro u hu
    by_cases huv : u = v
    · subst u; simpa using hc ▸ hcount
    · simpa [Function.update_of_ne huv] using
        hinv.length_le u (Finset.mem_of_mem_insert_of_ne hu huv)
  · intro u hu D hD
    by_cases huv : u = v
    · subst u; exact hpool D (by simpa using hD)
    · rw [Function.update_of_ne huv] at hD
      exact hinv.contains u (Finset.mem_of_mem_insert_of_ne hu huv) D hD

theorem initial_poolInvariant (s : V) {M : ℕ} (hM : 0 < M) :
    PoolInvariant {s} (fun u => if u = s then 1 else 0)
      (fun u => if u = s then [{s}] else []) M := by
  constructor
  · intro u; split_ifs <;> norm_num
  · intro u hu; have : u = s := by simpa using hu
    subst u; simp
  · intro u hu; have : u = s := by simpa using hu
    subst u; simpa using Nat.succ_le_of_lt hM
  · intro u hu D hD; have : u = s := by simpa using hu
    subst u
    simp only [ite_true, List.mem_singleton] at hD
    subst D
    exact Finset.mem_singleton_self s


/-- The pool invariants are used inductively through every continuing round. -/
theorem sRounds_nonneg (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (t : V) {M : ℕ} (hM : 0 < M) (fuel : ℕ) (R : Finset V) (qh : V → ℝ)
    (pools : V → List (Finset V)) (hinv : PoolInvariant R qh pools M) :
    Prog.Supported (fun z => 0 ≤ z) (G.sRounds p t M fuel R qh pools) := by
  induction fuel generalizing R qh pools with
  | zero => exact .ret _ (hinv.nonneg t)
  | succ fuel ih =>
    unfold sRounds
    split_ifs
    · exact .ret _ (hinv.nonneg t)
    · generalize he : (((arcOrder E).filter fun e => G.source e ∈ R ∧ G.target e ∉ R).argmax
        fun e => qh (G.source e) * p e) = o
      cases o with
      | none => exact .ret _ le_rfl
      | some e =>
        have hmem := List.argmax_mem (show e ∈ (((arcOrder E).filter
          fun e => G.source e ∈ R ∧ G.target e ∉ R).argmax
          fun e => qh (G.source e) * p e) by rw [he]; simp)
        have hcut : G.source e ∈ R ∧ G.target e ∉ R := by
          simpa using (List.mem_filter.mp hmem).2
        simp only [Option.elim_some]
        split_ifs with hscore
        · exact .ret _ le_rfl
        · apply (G.sGenerate_records p R qh pools M hinv (G.target e) M).bind
          intro res hres
          exact ih _ _ _ (hinv.update hM (G.target e) (G.phiS p R qh)
            (G.phiS_pos p hp0 hp1 R qh hinv.nonneg e hcut (lt_of_not_ge hscore))
            res.1 res.2 hres.1 hres.2.1 hres.2.2)

/-- The actual optional-edge choice in sIter realizes the conditional product
law whenever the outgoing-cut event has positive probability. -/
theorem firstOpen_normLaw_conditional (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (R : Finset V) (u : V) (hγ : 0 < G.gammaS p R u) (ω : E → Bool) :
    (∑ j : Option E, (normLaw (fun j : Option E => j.elim 0 (G.firstOpenWeight p R u)) none).value j *
      j.elim 0 (fun j => edgeWeight (forceProb p (G.preState R u j)) ω)) =
      condWeight p (fun ω => ∃ e, G.cutAt R u e ∧ ω e = true) ω := by
  have h0 : ∀ j : Option E, 0 ≤ j.elim 0 (G.firstOpenWeight p R u) := by
    intro j
    cases j with
    | none => exact le_rfl
    | some j => exact G.firstOpenWeight_nonneg p hp0 hp1 R u j
  have hsum : (∑ j : Option E, j.elim 0 (G.firstOpenWeight p R u)) = G.gammaS p R u := by
    simp [Fintype.sum_option, gammaS]
  simp_rw [normLaw_value _ none h0 (hsum.symm ▸ hγ)]
  rw [hsum]
  simpa [Fintype.sum_option] using G.firstOpen_conditional p R u ω

end Digraph
end
end DirectedCycleFPRAS
