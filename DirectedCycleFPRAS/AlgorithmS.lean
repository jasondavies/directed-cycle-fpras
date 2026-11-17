module

public import DirectedCycleFPRAS.Discretise
public import DirectedCycleFPRAS.Resources

@[expose] public section

set_option linter.unusedSectionVars false

/-!
# Algorithm S as a program, and its discretisation

A transcription of Algorithm S of Feng, Fu and Guo (arXiv:2608.02523v2,
Section 2.3) into the program model, with exact discrete choices. It makes no
oracle calls. This file proves, about that transcription:

* `algS_choiceBound`: every random action is a finite choice, and along every
  execution the numbers of alternatives sum to at most an explicit polynomial
  (Step 1 of research/DISCRETISATION.md);
* `algS_sat`: with rational input probabilities, the output is a fraction of
  explicitly bounded size, by a common-denominator invariant (Step 3);
* `algS_discretised`: if the exact algorithm fails with probability at most
  1/8, the version run on `b`-bit draws fails with probability at most 1/4,
  uses only uniform `b`-bit draws, and has the same output size bound.

`AlgorithmSAccuracy` proves Theorem 9 for this exact transcription. The proof
uses the deferred-edge and snapshot-splitting laws, concrete pool moments,
and the finite-program martingale estimate. `AlgorithmSSubtypes` and
`AlgorithmSParentProgram` check the induced-subtype and parent-pointer
correspondences. The formalization map lists the supporting modules.
-/

namespace DirectedCycleFPRAS

open scoped BigOperators
open Classical

noncomputable section

/-- A complete edge order used by Algorithm S. Accuracy holds for every
such enumeration; executable programs supply their explicit input order. -/
class ArcEnumeration (E : Type) where
  order : List E
  nodup : order.Nodup
  complete : ∀ e, e ∈ order

noncomputable instance (priority := low) defaultArcEnumeration (E : Type) [Fintype E] :
    ArcEnumeration E where
  order := Finset.univ.toList
  nodup := Finset.nodup_toList _
  complete := by simp

namespace Digraph

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [ArcEnumeration E] [DecidableEq E] {Q : Type}
variable (G : Digraph V E) (p : E → ℝ)

/-- The fixed order in which arcs are examined. -/
def arcOrder (E : Type) [Fintype E] [ArcEnumeration E] : List E := ArcEnumeration.order

@[simp] theorem mem_arcOrder (e : E) : e ∈ arcOrder E := ArcEnumeration.complete e

theorem arcOrder_nodup (E : Type) [Fintype E] [ArcEnumeration E] : (arcOrder E).Nodup :=
  ArcEnumeration.nodup

@[simp] theorem arcOrder_length (E : Type) [Fintype E] [ArcEnumeration E] :
    (arcOrder E).length = Fintype.card E := by
  have he : (arcOrder E).toFinset = Finset.univ := by ext e; simp
  have hc := List.toFinset_card_of_nodup (arcOrder_nodup E)
  rw [he, Finset.card_univ] at hc
  exact hc.symm

/-- `e'` precedes `e` in the fixed order. -/
def arcBefore (e' e : E) : Prop := (arcOrder E).idxOf e' < (arcOrder E).idxOf e

/-- `e` is an arc of the outgoing cut of `R` leaving `u`. -/
def cutAt (R : Finset V) (u : V) (e : E) : Prop := G.source e = u ∧ G.target e ∉ R

/-- Probability that `e` is the first open cut arc leaving `u`. -/
def firstOpenWeight (R : Finset V) (u : V) (e : E) : ℝ :=
  if G.cutAt R u e then
    p e * ∏ e' ∈ Finset.univ.filter (fun e' => G.cutAt R u e' ∧ arcBefore e' e), (1 - p e')
  else 0

/-- `γ_u`: probability that some cut arc leaving `u` is open. -/
def gammaS (R : Finset V) (u : V) : ℝ := ∑ e, G.firstOpenWeight p R u e

/-- States of the cut arcs at `u` forced by the choice of the first open one. -/
def preState (R : Finset V) (u : V) (j e : E) : Option Bool :=
  if G.cutAt R u e then
    (if e = j then some true else if arcBefore e j then some false else none)
  else none

/-- A coin with bias `x`. -/
def coin (x : ℝ) : Law Bool := normLaw (fun b => if b then x else 1 - x) false

/-- Examine the listed arcs leaving the popped vertex `z`. -/
def sScan (R : Finset V) (pre : E → Option Bool) (z : V) (flag : Bool) :
    List E → Finset V → List (V × Bool) → Prog Q (Finset V × List (V × Bool))
  | [], D, st => .ret (D, st)
  | e :: l, D, st =>
    if G.source e = z ∧ G.target e ∉ D then
      ((pre e).elim (Prog.choose (coin (p e)) Prog.ret) Prog.ret).bind fun o =>
        if o then
          sScan R pre z flag l (insert (G.target e) D)
            ((G.target e, flag && decide (G.target e ∉ R)) :: st)
        else sScan R pre z flag l D st
    else sScan R pre z flag l D st

/-- The modified DFS of Generate, stopped when `v` is popped. It returns the
discovered set if the tree path to `v` avoids the resolved vertices. -/
def sDfs (R : Finset V) (pre : E → Option Bool) (v : V) :
    ℕ → Finset V → List (V × Bool) → Prog Q (Option (Finset V))
  | 0, _, _ => .ret none
  | _ + 1, _, [] => .ret none
  | f + 1, D, (z, flag) :: st =>
    if z = v then .ret (if flag then some D else none)
    else (G.sScan p R pre z flag (arcOrder E) D st).bind fun r => sDfs R pre v f r.1 r.2

/-- One iteration of Generate: Steps 1(a) to 1(d). -/
def sIter (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V)) (M : ℕ) (v : V) :
    Prog Q (Option (Finset V)) :=
  .choose (normLaw (fun o : Option V =>
      o.elim 0 fun u => if u ∈ R then qh u * G.gammaS p R u else 0) none) fun o =>
    o.elim (.ret none) fun u =>
      .choose (normLaw (fun i : Fin (M + 1) =>
          if (i : ℕ) < (pools u).length then (1 : ℝ) else 0) 0) fun i =>
        .choose (normLaw (fun j : Option E => j.elim 0 (G.firstOpenWeight p R u)) none) fun j =>
          j.elim (.ret none) fun j =>
            G.sDfs p R (G.preState R u j) v (Fintype.card V + 1)
              ((pools u).getD i ∅) [(u, true)]

/-- Generate: the number of records and the recorded snapshots. -/
def sGenerate (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V)) (M : ℕ) (v : V) :
    ℕ → Prog Q (ℕ × List (Finset V))
  | 0 => .ret (0, [])
  | i + 1 => (sGenerate R qh pools M v i).bind fun acc =>
      (G.sIter p R qh pools M v).bind fun o =>
        .ret (o.elim acc fun D => (acc.1 + 1, D :: acc.2))

/-- `Φ̂`. -/
def phiS (R : Finset V) (qh : V → ℝ) : ℝ :=
  ∑ u, if u ∈ R then qh u * G.gammaS p R u else 0

/-- The rounds of Algorithm S. -/
def sRounds (t : V) (M : ℕ) :
    ℕ → Finset V → (V → ℝ) → (V → List (Finset V)) → Prog Q ℝ
  | 0, _, qh, _ => .ret (qh t)
  | f + 1, R, qh, pools =>
    if t ∈ R then .ret (qh t)
    else
      (((arcOrder E).filter fun e => G.source e ∈ R ∧ G.target e ∉ R).argmax
          fun e => qh (G.source e) * p e).elim (.ret 0) fun e =>
        if qh (G.source e) * p e ≤ 0 then .ret 0
        else
          (G.sGenerate p R qh pools M (G.target e) M).bind fun res =>
            sRounds t M f (insert (G.target e) R)
              (Function.update qh (G.target e) (G.phiS p R qh * res.1 / M))
              (Function.update pools (G.target e) res.2)

/-- Algorithm S with `M` samples per round. -/
def algS (s t : V) (M : ℕ) : Prog Q ℝ :=
  G.sRounds p t M (Fintype.card V) {s} (fun u => if u = s then 1 else 0)
    (fun u => if u = s then [{s}] else [])

end Digraph

/-! ## Step 1: finitely many alternatives -/

namespace Prog

variable {Q α β : Type}

theorem ChoiceBound.mono {m : Prog Q α} {a b : ℕ} (h : ChoiceBound m a) (hab : a ≤ b) :
    ChoiceBound m b := by
  induction h generalizing b with
  | ret a n => exact .ret a b
  | query x k n _ ih => exact .query x k b fun r => ih r hab
  | @choose ι _ p k n _ ih =>
    obtain ⟨b', rfl⟩ : ∃ b', b = Fintype.card ι + b' := ⟨b - Fintype.card ι, by omega⟩
    exact .choose p k b' fun i => ih i (by omega)
  | work c m n _ ih => exact .work c m b (ih hab)

theorem ChoiceBound.bind {m : Prog Q α} {g : α → Prog Q β} {a b : ℕ}
    (hm : ChoiceBound m a) (hg : ∀ x, ChoiceBound (g x) b) : ChoiceBound (m.bind g) (a + b) := by
  induction hm with
  | ret x n => exact (hg x).mono (by omega)
  | query x k n _ ih => exact .query x _ _ ih
  | choose p k n _ ih =>
    rw [Nat.add_assoc]
    exact .choose p _ _ ih
  | work c m n _ ih => exact .work c _ _ ih

end Prog

namespace Digraph

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [ArcEnumeration E] [DecidableEq E] {Q : Type}
variable (G : Digraph V E) (p : E → ℝ)

omit [Fintype V] [Fintype E] in
theorem sScan_choiceBound (R : Finset V) (pre : E → Option Bool) (z : V) (flag : Bool)
    (l : List E) (D : Finset V) (st : List (V × Bool)) :
    Prog.ChoiceBound (G.sScan (Q := Q) p R pre z flag l D st) (2 * l.length) := by
  induction l generalizing D st with
  | nil => exact .ret _ _
  | cons e l ih =>
    unfold sScan
    split_ifs with h
    · have hfirst : Prog.ChoiceBound
          ((pre e).elim (Prog.choose (coin (p e)) Prog.ret) (Prog.ret (Q := Q))) 2 := by
        cases pre e with
        | none =>
          have := Prog.ChoiceBound.choose (Q := Q) (coin (p e)) Prog.ret 0 fun b => .ret b 0
          simpa using this
        | some b => exact .ret _ _
      have hb := hfirst.bind (b := 2 * l.length) (g := fun o : Bool =>
          if o then
            G.sScan (Q := Q) p R pre z flag l (insert (G.target e) D)
              ((G.target e, flag && decide (G.target e ∉ R)) :: st)
          else G.sScan p R pre z flag l D st) fun o => by
        split_ifs
        · exact ih _ _
        · exact ih _ _
      exact hb.mono (by simp only [List.length_cons]; omega)
    · exact (ih D st).mono (by simp only [List.length_cons]; omega)

theorem sDfs_choiceBound (R : Finset V) (pre : E → Option Bool) (v : V) (f : ℕ)
    (D : Finset V) (st : List (V × Bool)) :
    Prog.ChoiceBound (G.sDfs (Q := Q) p R pre v f D st) (f * (2 * Fintype.card E)) := by
  induction f generalizing D st with
  | zero => exact .ret _ _
  | succ f ih =>
    cases st with
    | nil => exact .ret _ _
    | cons zf st =>
      obtain ⟨z, flag⟩ := zf
      unfold sDfs
      split_ifs
      · exact .ret _ _
      · exact .ret _ _
      · have hs := G.sScan_choiceBound (Q := Q) p R pre z flag (arcOrder E) D st
        rw [arcOrder_length] at hs
        exact (hs.bind fun r => ih r.1 r.2).mono (le_of_eq (by ring))

/-- Bound on the alternatives of one iteration of Generate. -/
def iterChoices (n m M : ℕ) : ℕ := (n + 1) + ((M + 1) + ((m + 1) + (n + 1) * (2 * m)))

theorem sIter_choiceBound (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V))
    (M : ℕ) (v : V) :
    Prog.ChoiceBound (G.sIter (Q := Q) p R qh pools M v)
      (iterChoices (Fintype.card V) (Fintype.card E) M) := by
  unfold sIter iterChoices
  have h1 := Prog.ChoiceBound.choose (Q := Q)
    (normLaw (fun o : Option V =>
      o.elim 0 fun u => if u ∈ R then qh u * G.gammaS p R u else 0) none)
    (fun o => o.elim (.ret none) fun u =>
      .choose (normLaw (fun i : Fin (M + 1) =>
          if (i : ℕ) < (pools u).length then (1 : ℝ) else 0) 0) fun i =>
        .choose (normLaw (fun j : Option E => j.elim 0 (G.firstOpenWeight p R u)) none) fun j =>
          j.elim (.ret none) fun j =>
            G.sDfs p R (G.preState R u j) v (Fintype.card V + 1)
              ((pools u).getD i ∅) [(u, true)])
    ((M + 1) + ((Fintype.card E + 1) + (Fintype.card V + 1) * (2 * Fintype.card E))) ?_
  · simpa [Fintype.card_option] using h1
  · intro o
    cases o with
    | none => exact .ret _ _
    | some u =>
      have h2 := Prog.ChoiceBound.choose (Q := Q)
        (normLaw (fun i : Fin (M + 1) =>
          if (i : ℕ) < (pools u).length then (1 : ℝ) else 0) 0)
        (fun i => .choose (normLaw (fun j : Option E =>
            j.elim 0 (G.firstOpenWeight p R u)) none) fun j =>
          j.elim (.ret none) fun j =>
            G.sDfs p R (G.preState R u j) v (Fintype.card V + 1)
              ((pools u).getD i ∅) [(u, true)])
        ((Fintype.card E + 1) + (Fintype.card V + 1) * (2 * Fintype.card E)) ?_
      · simpa [Fintype.card_fin] using h2
      · intro i
        have h3 := Prog.ChoiceBound.choose (Q := Q)
          (normLaw (fun j : Option E => j.elim 0 (G.firstOpenWeight p R u)) none)
          (fun j => j.elim (.ret none) fun j =>
            G.sDfs p R (G.preState R u j) v (Fintype.card V + 1)
              ((pools u).getD i ∅) [(u, true)])
          ((Fintype.card V + 1) * (2 * Fintype.card E)) ?_
        · simpa [Fintype.card_option] using h3
        · intro j
          cases j with
          | none => exact .ret _ _
          | some j => exact G.sDfs_choiceBound p _ _ _ _ _ _

theorem sGenerate_choiceBound (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V))
    (M : ℕ) (v : V) (i : ℕ) :
    Prog.ChoiceBound (G.sGenerate (Q := Q) p R qh pools M v i)
      (i * iterChoices (Fintype.card V) (Fintype.card E) M) := by
  induction i with
  | zero => exact .ret _ _
  | succ i ih =>
    have h := ih.bind (g := fun acc => (G.sIter (Q := Q) p R qh pools M v).bind fun o =>
        Prog.ret (o.elim acc fun D => (acc.1 + 1, D :: acc.2)))
      (b := iterChoices (Fintype.card V) (Fintype.card E) M + 0)
      fun acc => (G.sIter_choiceBound p R qh pools M v).bind fun o => .ret _ _
    exact h.mono (by rw [Nat.succ_mul]; omega)

theorem sRounds_choiceBound (t : V) (M f : ℕ) (R : Finset V) (qh : V → ℝ)
    (pools : V → List (Finset V)) :
    Prog.ChoiceBound (G.sRounds (Q := Q) p t M f R qh pools)
      (f * (M * iterChoices (Fintype.card V) (Fintype.card E) M)) := by
  induction f generalizing R qh pools with
  | zero => exact .ret _ _
  | succ f ih =>
    unfold sRounds
    split_ifs
    · exact .ret _ _
    · generalize (((arcOrder E).filter fun e => G.source e ∈ R ∧ G.target e ∉ R).argmax
        fun e => qh (G.source e) * p e) = o
      cases o with
      | none => exact .ret _ _
      | some e =>
        change Prog.ChoiceBound (if qh (G.source e) * p e ≤ 0 then Prog.ret 0 else _) _
        split_ifs
        · exact .ret _ _
        · exact ((G.sGenerate_choiceBound p R qh pools M (G.target e) M).bind
            fun res => ih _ _ _).mono (by rw [Nat.succ_mul]; omega)

/-- Total number of alternatives of Algorithm S along any execution. -/
def algSChoices (n m M : ℕ) : ℕ := n * (M * iterChoices n m M)

/-- **Step 1.** Algorithm S is a finite tree of discrete choices: along every
execution the numbers of alternatives sum to at most `algSChoices n m M`. -/
theorem algS_choiceBound (s t : V) (M : ℕ) :
    Prog.ChoiceBound (G.algS (Q := Q) p s t M)
      (algSChoices (Fintype.card V) (Fintype.card E) M) :=
  G.sRounds_choiceBound p t M _ _ _ _

end Digraph

/-! ## Step 3: a common denominator for every estimate -/

namespace Prog

variable {Q α : Type}

theorem Sat.trivial (m : Prog Q α) :
    Sat (fun _ => True) (fun _ => True) (fun _ => True) m := by
  induction m with
  | ret a => exact .ret a True.intro
  | query x k ih => exact .query x k True.intro fun r _ => ih r
  | choose p k ih => exact .choose p k ih
  | work c m ih => exact .work c m ih

theorem Sat.imp {A : ℝ → Prop} {Qp : Q → Prop} {R R' : α → Prop} {m : Prog Q α}
    (h : Sat A Qp R m) (hR : ∀ a, R a → R' a) : Sat A Qp R' m := by
  induction h with
  | ret a ha => exact .ret a (hR a ha)
  | query x k hx _ ih => exact .query x k hx ih
  | choose p k _ ih => exact .choose p k ih
  | work c m _ ih => exact .work c m ih

theorem Sat.discretise {A : ℝ → Prop} {Qp : Q → Prop} {R : α → Prop} {m : Prog Q α}
    (b : ℕ) (h : Sat A Qp R m) : Sat A Qp R (m.discretise b) := by
  induction h with
  | ret a ha => exact .ret a ha
  | query x k hx _ ih => exact .query x _ hx ih
  | choose p k _ ih => exact Sat.draw ih
  | work c m _ ih => exact .work c _ ih

end Prog

namespace Digraph

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [ArcEnumeration E] [DecidableEq E] {Q : Type}
variable (G : Digraph V E) (p : E → ℝ)

section Sizes

variable (a b : E → ℕ) (hb : ∀ e, 0 < b e) (ha : ∀ e, a e ≤ b e)
  (hp : ∀ e, p e = (a e : ℝ) / (b e : ℝ))

include hb ha hp in
/-- A first-open probability is a multiple of `1 / B`, `B` the product of all
input denominators. -/
theorem prod_frac (S : Finset E) (e : E) (he : e ∉ S) :
    ∃ c : ℕ, c ≤ ∏ e, b e ∧
      p e * ∏ e' ∈ S, (1 - p e') = (c : ℝ) / ((∏ e, b e : ℕ) : ℝ) := by
  have hbR : ∀ e, (b e : ℝ) ≠ 0 := fun e => by exact_mod_cast (hb e).ne'
  have hB : (∏ e, b e) = b e * (∏ e' ∈ S, b e') * ∏ e' ∈ (insert e S)ᶜ, b e' := by
    rw [← Finset.prod_mul_prod_compl (insert e S) b, Finset.prod_insert he]
  have h1 : ∏ e' ∈ S, (1 - p e') =
      (∏ e' ∈ S, ((b e' - a e' : ℕ) : ℝ)) / ∏ e' ∈ S, (b e' : ℝ) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro e' _
    rw [hp e', Nat.cast_sub (ha e')]
    have := hbR e'
    field_simp
  have hS : (∏ e' ∈ S, (b e' : ℝ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun e' _ => hbR e'
  have hT : (∏ e' ∈ (insert e S)ᶜ, (b e' : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun e' _ => hbR e'
  refine ⟨a e * (∏ e' ∈ S, (b e' - a e')) * ∏ e' ∈ (insert e S)ᶜ, b e', ?_, ?_⟩
  · rw [hB]
    exact Nat.mul_le_mul (Nat.mul_le_mul (ha e)
      (Finset.prod_le_prod fun e' _ => Nat.sub_le _ _)) le_rfl
  · rw [hB, hp e, h1]
    push_cast
    have := hbR e
    field_simp

include hb ha hp in
theorem firstOpenWeight_frac (R : Finset V) (u : V) (e : E) :
    ∃ c : ℕ, c ≤ ∏ e, b e ∧
      G.firstOpenWeight p R u e = (c : ℝ) / ((∏ e, b e : ℕ) : ℝ) := by
  unfold firstOpenWeight
  split_ifs
  · apply prod_frac p a b hb ha hp
    intro hmem
    exact lt_irrefl _ (Finset.mem_filter.mp hmem).2.2
  · exact ⟨0, Nat.zero_le _, by simp⟩

include hb ha hp in
theorem gammaS_frac (R : Finset V) (u : V) :
    ∃ g : ℕ, g ≤ Fintype.card E * ∏ e, b e ∧
      G.gammaS p R u = (g : ℝ) / ((∏ e, b e : ℕ) : ℝ) := by
  choose c hc hcw using G.firstOpenWeight_frac p a b hb ha hp R u
  refine ⟨∑ e, c e, ?_, ?_⟩
  · have := Finset.sum_le_card_nsmul Finset.univ c (∏ e, b e) fun e _ => hc e
    simpa using this
  · unfold gammaS
    simp_rw [hcw]
    rw [← Finset.sum_div]
    push_cast
    rfl

/-- Growth factor of numerators per round. -/
def sizeBase (n m M B : ℕ) : ℕ := (n * m + 1) * (M * B)

theorem sGenerate_count (R : Finset V) (qh : V → ℝ) (pools : V → List (Finset V))
    (M : ℕ) (v : V) (i : ℕ) :
    Prog.Sat (fun _ => True) (fun _ => True) (fun res : ℕ × List (Finset V) => res.1 ≤ i)
      (G.sGenerate (Q := Q) p R qh pools M v i) := by
  induction i with
  | zero => exact .ret _ (le_refl 0)
  | succ i ih =>
    refine ih.bind fun acc hacc => ?_
    refine (Prog.Sat.trivial (G.sIter (Q := Q) p R qh pools M v)).bind fun o _ => .ret _ ?_
    cases o with
    | none => exact Nat.le_succ_of_le hacc
    | some D => exact Nat.succ_le_succ hacc

include hb ha hp in
/-- Common-denominator invariant: after `r` rounds every estimate is a
multiple of `1 / (M * B)^r` with numerator at most `sizeBase^r`. -/
theorem sRounds_sat (t : V) {M : ℕ} (hM : 0 < M) (f r : ℕ) (R : Finset V) (qh : V → ℝ)
    (pools : V → List (Finset V))
    (hinv : ∀ u, ∃ c : ℕ,
      c ≤ sizeBase (Fintype.card V) (Fintype.card E) M (∏ e, b e) ^ r ∧
      qh u = (c : ℝ) / ((M * ∏ e, b e : ℕ) : ℝ) ^ r) :
    Prog.Sat (fun _ => True) (fun _ => True)
      (fun z : ℝ => ∃ r' c : ℕ, r' ≤ r + f ∧
        c ≤ sizeBase (Fintype.card V) (Fintype.card E) M (∏ e, b e) ^ r' ∧
        z = (c : ℝ) / ((M * ∏ e, b e : ℕ) : ℝ) ^ r')
      (G.sRounds (Q := Q) p t M f R qh pools) := by
  set B := ∏ e, b e with hBdef
  set C := sizeBase (Fintype.card V) (Fintype.card E) M B with hCdef
  have hBpos : 0 < B := Finset.prod_pos fun e _ => hb e
  have hMB : 0 < M * B := Nat.mul_pos hM hBpos
  have hMBC : M * B ≤ C := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have hnmC : Fintype.card V * Fintype.card E * (M * B) ≤ C :=
    Nat.mul_le_mul_right _ (Nat.le_succ _)
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hBR : (B : ℝ) ≠ 0 := by exact_mod_cast hBpos.ne'
  induction f generalizing r R qh pools with
  | zero =>
    obtain ⟨c, hc, hq⟩ := hinv t
    exact .ret _ ⟨r, c, le_refl _, hc, hq⟩
  | succ f ih =>
    unfold sRounds
    split_ifs
    · obtain ⟨c, hc, hq⟩ := hinv t
      exact .ret _ ⟨r, c, by omega, hc, hq⟩
    · generalize (((arcOrder E).filter fun e => G.source e ∈ R ∧ G.target e ∉ R).argmax
        fun e => qh (G.source e) * p e) = o
      have hzero : ∃ r' c : ℕ, r' ≤ r + (f + 1) ∧ c ≤ C ^ r' ∧
          (0 : ℝ) = (c : ℝ) / ((M * B : ℕ) : ℝ) ^ r' := ⟨0, 0, by omega, by simp, by simp⟩
      cases o with
      | none => exact .ret _ hzero
      | some e =>
        change Prog.Sat _ _ _ (if qh (G.source e) * p e ≤ 0 then Prog.ret 0 else _)
        split_ifs
        · exact .ret _ hzero
        · refine (G.sGenerate_count (Q := Q) p R qh pools M (G.target e) M).bind
            fun res hres => ?_
          have hstep := ih (r + 1) (insert (G.target e) R)
            (Function.update qh (G.target e) (G.phiS p R qh * res.1 / M))
            (Function.update pools (G.target e) res.2) ?_
          · rw [show r + (f + 1) = r + 1 + f by omega]
            exact hstep
          · choose c hc hq using hinv
            choose g hg hγ using G.gammaS_frac p a b hb ha hp R
            intro u'
            by_cases hu : u' = G.target e
            · subst hu
              rw [Function.update_self]
              refine ⟨(∑ u, if u ∈ R then c u * g u else 0) * res.1, ?_, ?_⟩
              · have hsum : (∑ u, if u ∈ R then c u * g u else 0) ≤
                    Fintype.card V * (C ^ r * (Fintype.card E * B)) := by
                  have := Finset.sum_le_card_nsmul Finset.univ
                    (fun u => if u ∈ R then c u * g u else 0) (C ^ r * (Fintype.card E * B))
                    fun u _ => by
                      split_ifs
                      · exact Nat.mul_le_mul (hc u) (hg u)
                      · exact Nat.zero_le _
                  simpa using this
                calc (∑ u, if u ∈ R then c u * g u else 0) * res.1
                    ≤ Fintype.card V * (C ^ r * (Fintype.card E * B)) * M :=
                      Nat.mul_le_mul hsum hres
                  _ = C ^ r * (Fintype.card V * Fintype.card E * (M * B)) := by ring
                  _ ≤ C ^ r * C := Nat.mul_le_mul_left _ hnmC
                  _ = C ^ (r + 1) := (pow_succ C r).symm
              · have hphi : G.phiS p R qh =
                    ((∑ u, if u ∈ R then c u * g u else 0 : ℕ) : ℝ) /
                      (((M * B : ℕ) : ℝ) ^ r * B) := by
                  unfold phiS
                  push_cast
                  rw [Finset.sum_div]
                  apply Finset.sum_congr rfl
                  intro u _
                  split_ifs
                  · rw [hq u, hγ u]
                    push_cast
                    rw [div_mul_div_comm]
                    simp [hBdef]
                  · simp
                rw [hphi, pow_succ]
                push_cast
                field_simp
            · rw [Function.update_of_ne hu]
              refine ⟨c u' * (M * B), ?_, ?_⟩
              · calc c u' * (M * B) ≤ C ^ r * C := Nat.mul_le_mul (hc u') hMBC
                  _ = C ^ (r + 1) := (pow_succ C r).symm
              · rw [hq u', pow_succ]
                push_cast
                field_simp

include hb ha hp in
/-- **Step 3.** With rational input probabilities `a e / b e`, every possible
output of Algorithm S is a fraction with numerator and denominator at most
`((n*m + 1) * M * B)^n`, where `B` is the product of the denominators. -/
theorem algS_sat (s t : V) {M : ℕ} (hM : 0 < M) :
    Prog.Sat (fun _ => True) (fun _ => True)
      (Height (sizeBase (Fintype.card V) (Fintype.card E) M (∏ e, b e) ^ Fintype.card V))
      (G.algS (Q := Q) p s t M) := by
  have hBpos : 0 < ∏ e, b e := Finset.prod_pos fun e _ => hb e
  have hMB : 0 < M * ∏ e, b e := Nat.mul_pos hM hBpos
  have hMBC : M * ∏ e, b e ≤ sizeBase (Fintype.card V) (Fintype.card E) M (∏ e, b e) :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have h := G.sRounds_sat (Q := Q) p a b hb ha hp t hM (Fintype.card V) 0 {s}
    (fun u => if u = s then 1 else 0) (fun u => if u = s then [{s}] else []) (by
      intro u
      by_cases hu : u = s
      · exact ⟨1, by simp, by simp [hu]⟩
      · exact ⟨0, by simp, by simp [hu]⟩)
  refine h.imp ?_
  rintro z ⟨r, c, hr, hc, rfl⟩
  rw [Nat.zero_add] at hr
  have hCpos : 0 < sizeBase (Fintype.card V) (Fintype.card E) M (∏ e, b e) :=
    lt_of_lt_of_le hMB hMBC
  refine ⟨c, (M * ∏ e, b e) ^ r, pow_pos hMB r, by push_cast; rfl, ?_, ?_⟩
  · simpa using hc.trans (Nat.pow_le_pow_right hCpos hr)
  · exact (Nat.pow_le_pow_left hMBC r).trans (Nat.pow_le_pow_right hCpos hr)

end Sizes

/-- **Discretised Algorithm S.** Assume the exact algorithm misses a set of
acceptable outputs with probability at most 1/8 (Theorem 9 of the paper, for
this transcription) and `b` is large enough that the total number of
alternatives over `2^b` is at most 1/8. Then the algorithm run on `b`-bit
draws

* misses it with probability at most 1/4;
* uses only uniform `b`-bit draws, at most `algSChoices n m M` of them;
* returns a fraction of the size bounded in `algS_sat`. -/
theorem algS_discretised (O : Oracle Q) (a b : E → ℕ) (hb : ∀ e, 0 < b e)
    (ha : ∀ e, a e ≤ b e) (hp : ∀ e, p e = (a e : ℝ) / (b e : ℝ)) (s t : V) {M : ℕ}
    (hM : 0 < M) (bits : ℕ) (P : ℝ → Prop)
    (hbits : (algSChoices (Fintype.card V) (Fintype.card E) M : ℝ) / (2 : ℝ) ^ bits ≤ 1 / 8)
    (hexact : (G.algS p s t M).exp O (fun z => if P z then 0 else 1) ≤ 1 / 8) :
    ((G.algS p s t M).discretise bits).exp O (fun z => if P z then 0 else 1) ≤ 1 / 4 ∧
    Prog.BitBound bits ((G.algS (Q := Q) p s t M).discretise bits)
      (algSChoices (Fintype.card V) (Fintype.card E) M) ∧
    Prog.Sat (fun _ => True) (fun _ => True)
      (Height (sizeBase (Fintype.card V) (Fintype.card E) M (∏ e, b e) ^ Fintype.card V))
      ((G.algS (Q := Q) p s t M).discretise bits) := by
  have hcb := G.algS_choiceBound (Q := Q) p s t M
  refine ⟨?_, Prog.discretise_bitBound bits hcb,
    (G.algS_sat (Q := Q) p a b hb ha hp s t hM).discretise bits⟩
  have hd := Prog.exp_discretise_le O bits (f := fun z : ℝ => if P z then 0 else 1)
    (fun z => by split_ifs <;> norm_num) (fun z => by split_ifs <;> norm_num) hcb
  have := (abs_le.mp hd).2
  linarith

end Digraph
end
end DirectedCycleFPRAS
