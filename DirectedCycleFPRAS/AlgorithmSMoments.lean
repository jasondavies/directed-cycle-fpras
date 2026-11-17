module

public import DirectedCycleFPRAS.AlgorithmSPools
public import DirectedCycleFPRAS.PredictionMartingale

@[expose] public section

/-! Moments of the concrete Generate procedure. Snapshot lists retain
multiplicities; no independence of different rounds or pools is used. -/
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
namespace Digraph
variable {V E Q : Type} [Fintype V] [DecidableEq V] [Fintype E] [ArcEnumeration E] [DecidableEq E]
variable (G : Digraph V E) (p : E → ℝ)

/-- Scoring the stored records is exactly a sum of independent iterations.
A rejected iteration contributes zero. This identity holds for every test
function, not just the first two moments. -/
theorem sGenerate_scored_law (O : Oracle Q) (R : Finset V) (qh : V → ℝ)
    (pools : V → List (Finset V)) (M : ℕ) (v : V)
    (f : Finset V → ℝ) (n : ℕ) (g : ℝ → ℝ) :
    (G.sGenerate p R qh pools M v n).exp O (fun r => g (r.2.map f).sum) =
      (Prog.sumRuns (G.sIter p R qh pools M v) (fun o => o.elim 0 f) n).exp O g := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    simp only [sGenerate, Prog.sumRuns, Prog.exp_bind, Prog.exp]
    have he (r : ℕ × List (Finset V)) :
        (G.sIter p R qh pools M v).exp O
          (fun o => g ((o.elim r fun D => (r.1+1, D::r.2)).2.map f).sum) =
        (G.sIter p R qh pools M v).exp O (fun o => g ((r.2.map f).sum+o.elim 0 f)) := by
      congr 1
      funext o
      cases o <;> simp [add_comm]
    simp_rw [he]
    exact ih (fun a => (G.sIter p R qh pools M v).exp O (fun o => g (a+o.elim 0 f)))

/-- Generate's score sum has mean M times the single-record mean. -/
theorem sGenerate_score_mean (O : Oracle Q) (R : Finset V) (qh : V → ℝ)
    (pools : V → List (Finset V)) (M : ℕ) (v : V) (f : Finset V → ℝ) (n : ℕ) :
    (G.sGenerate p R qh pools M v n).exp O (fun r => (r.2.map f).sum) =
      n*(G.sIter p R qh pools M v).exp O (fun o => o.elim 0 f) := by
  have h := G.sGenerate_scored_law p O R qh pools M v f n id
  simp only [id_eq] at h
  exact h.trans (Prog.sumRuns_mean _ _ _ _)

/-- Exact variance additivity for the concrete snapshot generation loop. -/
theorem sGenerate_score_variance (O : Oracle Q) (R : Finset V) (qh : V → ℝ)
    (pools : V → List (Finset V)) (M : ℕ) (v : V) (f : Finset V → ℝ) (n : ℕ) :
    let μ := (G.sIter p R qh pools M v).exp O (fun o => o.elim 0 f)
    (G.sGenerate p R qh pools M v n).exp O (fun r => ((r.2.map f).sum-n*μ)^2) =
      n*(G.sIter p R qh pools M v).exp O (fun o => (o.elim 0 f-μ)^2) := by
  dsimp only
  exact (G.sGenerate_scored_law p O R qh pools M v f n
    (fun a => (a-n*(G.sIter p R qh pools M v).exp O (fun o => o.elim 0 f))^2)).trans
    (Prog.sumRuns_variance _ _ _ _)

omit [Fintype V] [DecidableEq V] in
/-- Multiplying the updated estimate by the uniform empirical snapshot
average cancels the random pool size, including the empty-pool case. -/
theorem pool_contribution (Φ : ℝ) (M : ℕ) (l : List (Finset V)) (f : Finset V → ℝ) :
    (Φ*l.length/M)*((l.map f).sum/l.length) = (Φ/M)*(l.map f).sum := by
  by_cases hl : l = []
  · simp [hl]
  · have hn : (l.length : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (List.length_pos_iff_ne_nil.mpr hl)
    field_simp

/-- Unbiased replacement of a predicted contribution by the actual pool
update. Instantiating this with DFS reach scores requires the last-resolved-
vertex decomposition. -/
theorem sGenerate_prediction_mean (O : Oracle Q) (R : Finset V) (qh : V → ℝ)
    (pools : V → List (Finset V)) {M : ℕ} (hM : 0 < M) (v : V)
    (f : Finset V → ℝ) (Φ q : ℝ) :
    let μ := (G.sIter p R qh pools M v).exp O (fun o => o.elim 0 f)
    (G.sGenerate p R qh pools M v M).exp O
      (fun r => q-Φ*μ+(Φ/M)*(r.2.map f).sum) = q := by
  dsimp only
  exact (G.sGenerate_scored_law p O R qh pools M v f M
    (fun a => q-Φ*(G.sIter p R qh pools M v).exp O (fun o => o.elim 0 f)+(Φ/M)*a)).trans
    (Prog.prediction_update_mean _ _ _ _ _ hM)

/-- One-round variance with arbitrary bounded nonnegative snapshot scores. -/
theorem sGenerate_prediction_variance (O : Oracle Q) (R : Finset V) (qh : V → ℝ)
    (pools : V → List (Finset V)) {M : ℕ} (hM : 0 < M) (v : V)
    (f : Finset V → ℝ) (Φ q B : ℝ) (hB : 0 ≤ B)
    (hf0 : ∀ D, 0 ≤ f D) (hfB : ∀ D, f D ≤ B) :
    let μ := (G.sIter p R qh pools M v).exp O (fun o => o.elim 0 f)
    (G.sGenerate p R qh pools M v M).exp O
      (fun r => (q-Φ*μ+(Φ/M)*(r.2.map f).sum-q)^2) ≤ Φ^2/M*(B*μ) := by
  dsimp only
  apply (G.sGenerate_scored_law p O R qh pools M v f M
    (fun a => (q-Φ*(G.sIter p R qh pools M v).exp O (fun o => o.elim 0 f)+(Φ/M)*a-q)^2)).trans_le
  apply Prog.prediction_update_variance _ _ _ _ _ _ hM
  · intro o; cases o with
    | none => exact le_rfl
    | some D => exact hf0 D
  · intro o; cases o with
    | none => exact hB
    | some D => exact hfB D

end Digraph
end
end DirectedCycleFPRAS
