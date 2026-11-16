module

public import DirectedCycleFPRAS.AlgorithmSPools

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E) (p : E → ℝ)

/-! An explicit arc list and rank let an induced graph inherit the ambient
order. Separate DFS and round fuel permits comparison of different vertex
types. The canonical specialization below is the existing Algorithm S. -/

def oFirst (rank : E → ℕ) (R : Finset V) (u : V) (e : E) : ℝ :=
  if G.cutAt R u e then
    p e * ∏ e' ∈ Finset.univ.filter (fun e' => G.cutAt R u e' ∧ rank e' < rank e), (1 - p e')
  else 0

def oGamma (rank : E → ℕ) (R : Finset V) (u : V) : ℝ := ∑ e, G.oFirst p rank R u e

def oPre (rank : E → ℕ) (R : Finset V) (u : V) (j e : E) : Option Bool :=
  if G.cutAt R u e then
    (if e = j then some true else if rank e < rank j then some false else none)
  else none

def oDfs (order : List E) (R : Finset V) (pre : E → Option Bool) (v : V) :
    ℕ → Finset V → List (V × Bool) → Prog Empty (Option (Finset V))
  | 0, _, _ => .ret none
  | _ + 1, _, [] => .ret none
  | f + 1, D, (z, flag) :: st =>
    if z = v then .ret (if flag then some D else none)
    else (G.sScan p R pre z flag order D st).bind fun r => oDfs order R pre v f r.1 r.2

def oIter (order : List E) (rank : E → ℕ) (dfsFuel : ℕ)
    (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V)) (M : ℕ) (v : V) :
    Prog Empty (Option (Finset V)) :=
  .choose (normLaw (fun o : Option V =>
      o.elim 0 fun u => if u ∈ R then qh u * G.oGamma p rank R u else 0) none) fun o =>
    o.elim (.ret none) fun u =>
      .choose (normLaw (fun i : Fin (M + 1) =>
          if (i : ℕ) < (pools u).length then (1 : ℝ) else 0) 0) fun i =>
        .choose (normLaw (fun j : Option E => j.elim 0 (G.oFirst p rank R u)) none) fun j =>
          j.elim (.ret none) fun j =>
            G.oDfs p order R (G.oPre rank R u j) v dfsFuel ((pools u).getD i ∅) [(u, true)]

def oGenerate (order : List E) (rank : E → ℕ) (dfsFuel : ℕ)
    (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V)) (M : ℕ) (v : V) :
    ℕ → Prog Empty (ℕ × List (Finset V))
  | 0 => .ret (0, [])
  | i + 1 => (oGenerate order rank dfsFuel R qh pools M v i).bind fun acc =>
      (G.oIter p order rank dfsFuel R qh pools M v).bind fun o =>
        .ret (o.elim acc fun D => (acc.1 + 1, D :: acc.2))

def oPhi (rank : E → ℕ) (R : Finset V) (qh : V → ℝ) : ℝ :=
  ∑ u, if u ∈ R then qh u * G.oGamma p rank R u else 0

def oRounds (order : List E) (rank : E → ℕ) (dfsFuel : ℕ) (t : V) (M : ℕ) :
    ℕ → Finset V → (V → ℝ) → (V → List (Finset V)) → Prog Empty ℝ
  | 0, _, qh, _ => .ret (qh t)
  | f + 1, R, qh, pools =>
    if t ∈ R then .ret (qh t)
    else
      ((order.filter fun e => G.source e ∈ R ∧ G.target e ∉ R).argmax
          fun e => qh (G.source e) * p e).elim (.ret 0) fun e =>
        if qh (G.source e) * p e ≤ 0 then .ret 0
        else
          (G.oGenerate p order rank dfsFuel R qh pools M (G.target e) M).bind fun res =>
            oRounds order rank dfsFuel t M f (insert (G.target e) R)
              (Function.update qh (G.target e) (G.oPhi p rank R qh * res.1 / M))
              (Function.update pools (G.target e) res.2)

def orderedAlgS (order : List E) (rank : E → ℕ) (dfsFuel rounds : ℕ) (s t : V) (M : ℕ) : Prog Empty ℝ :=
  G.oRounds p order rank dfsFuel t M rounds {s} (fun u => if u = s then 1 else 0)
    (fun u => if u = s then [{s}] else [])

theorem oDfs_canonical (R : Finset V) (pre : E → Option Bool) (v : V)
    (f : ℕ) (D : Finset V) (st : List (V × Bool)) :
    G.oDfs p (arcOrder E) R pre v f D st = G.sDfs p R pre v f D st := by
  induction f generalizing D st with
  | zero => rfl
  | succ f ih =>
    cases st with
    | nil => rfl
    | cons zf st => simp only [oDfs, sDfs, ih]

theorem oFirst_canonical (R : Finset V) (u : V) :
    G.oFirst p (fun e => (arcOrder E).idxOf e) R u = G.firstOpenWeight p R u := by
  funext e
  simp only [oFirst, firstOpenWeight, arcBefore]
  congr 2
  apply Finset.prod_congr
  · congr 1
  · intro x hx; rfl

theorem oGamma_canonical (R : Finset V) (u : V) :
    G.oGamma p (fun e => (arcOrder E).idxOf e) R u = G.gammaS p R u := by
  simp only [oGamma, gammaS, oFirst_canonical]

theorem oPre_canonical (R : Finset V) (u : V) (j : E) :
    G.oPre (fun e => (arcOrder E).idxOf e) R u j = G.preState R u j := by
  funext e
  simp only [oPre, preState, arcBefore]
  congr 3

theorem oPhi_canonical (R : Finset V) (qh : V → ℝ) :
    G.oPhi p (fun e => (arcOrder E).idxOf e) R qh = G.phiS p R qh := by
  simp only [oPhi, phiS, oGamma_canonical]

theorem oIter_canonical (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V))
    (M : ℕ) (v : V) :
    G.oIter p (arcOrder E) (fun e => (arcOrder E).idxOf e) (Fintype.card V + 1) R qh pools M v =
      G.sIter p R qh pools M v := by
  simp only [oIter, sIter, oDfs_canonical, oGamma_canonical, oFirst_canonical, oPre_canonical]

theorem oGenerate_canonical (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V))
    (M : ℕ) (v : V) (i : ℕ) :
    G.oGenerate p (arcOrder E) (fun e => (arcOrder E).idxOf e) (Fintype.card V + 1) R qh pools M v i =
      G.sGenerate p R qh pools M v i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [oGenerate, sGenerate, ih, oIter_canonical]

theorem oRounds_canonical (t : V) (M f : ℕ) (R : Finset V) (qh : V → ℝ)
    (pools : V → List (Finset V)) :
    G.oRounds p (arcOrder E) (fun e => (arcOrder E).idxOf e) (Fintype.card V + 1) t M f R qh pools =
      G.sRounds p t M f R qh pools := by
  induction f generalizing R qh pools with
  | zero => rfl
  | succ f ih =>
    simp only [oRounds, sRounds, oGenerate_canonical, ih, oPhi_canonical]

/-- The old program is the canonical specialization, not a new accuracy assumption. -/
theorem orderedAlgS_canonical (s t : V) (M : ℕ) :
    G.orderedAlgS p (arcOrder E) (fun e => (arcOrder E).idxOf e)
      (Fintype.card V + 1) (Fintype.card V) s t M = G.algS p s t M :=
  G.oRounds_canonical p t M _ _ _ _

end Digraph
end
end DirectedCycleFPRAS
