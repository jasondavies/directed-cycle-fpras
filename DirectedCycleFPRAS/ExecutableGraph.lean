module

public import DirectedCycleFPRAS.VertexWitness

@[expose] public section

/-! Executable finite graph searches. The implementation expands a discovered
set at most `card V` times; the correctness proof identifies it with the
relational predicates used in the probability development. -/
set_option linter.unusedSectionVars false
namespace DirectedCycleFPRAS
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E)

/-- One simultaneous expansion along enabled edges. -/
def reachStep (enabled : E → Bool) (D : Finset V) : Finset V :=
  D ∪ (Finset.univ.filter (fun e => enabled e && decide (G.source e ∈ D))).image G.target

theorem mem_reachStep (enabled : E → Bool) (D : Finset V) (v : V) :
    v ∈ G.reachStep enabled D ↔ v ∈ D ∨
      ∃ e, enabled e = true ∧ G.source e ∈ D ∧ G.target e = v := by
  simp [reachStep, and_assoc]

theorem subset_reachStep (enabled : E → Bool) (D : Finset V) : D ⊆ G.reachStep enabled D :=
  Finset.subset_union_left

/-- Fuel bounds the number of complete edge scans; equality detects closure. -/
def reachClose (enabled : E → Bool) : ℕ → Finset V → Finset V
  | 0, D => D
  | n+1, D =>
    let next := G.reachStep enabled D
    if next = D then D else reachClose enabled n next

theorem subset_reachClose (enabled : E → Bool) (n : ℕ) (D : Finset V) :
    D ⊆ G.reachClose enabled n D := by
  induction n generalizing D with
  | zero => exact Finset.Subset.refl _
  | succ n ih =>
    simp only [reachClose]
    split_ifs
    · exact Finset.Subset.refl _
    · exact (G.subset_reachStep enabled D).trans (ih _)

theorem reachClose_closed (enabled : E → Bool) (n : ℕ) (D : Finset V)
    (h : Fintype.card V ≤ D.card+n) :
    G.reachStep enabled (G.reachClose enabled n D) = G.reachClose enabled n D := by
  induction n generalizing D with
  | zero =>
    have hD : D = Finset.univ := Finset.eq_univ_of_card D (le_antisymm (Finset.card_le_univ D) (by simpa using h))
    subst D
    simp [reachClose, reachStep]
  | succ n ih =>
    simp only [reachClose]
    split_ifs with he
    · exact he
    · apply ih
      have hs : D ⊂ G.reachStep enabled D :=
        Finset.ssubset_iff_subset_ne.mpr ⟨G.subset_reachStep enabled D, Ne.symm he⟩
      have hc := Finset.card_lt_card hs
      omega

theorem reachClose_sound (enabled : E → Bool) (s : V) (n : ℕ) (D : Finset V)
    (hD : ∀ v ∈ D, Relation.ReflTransGen (G.Adj {e | enabled e = true}) s v) :
    ∀ v ∈ G.reachClose enabled n D, Relation.ReflTransGen (G.Adj {e | enabled e = true}) s v := by
  induction n generalizing D with
  | zero => exact hD
  | succ n ih =>
    simp only [reachClose]
    split_ifs
    · exact hD
    · apply ih
      intro v hv
      rcases (G.mem_reachStep enabled D v).mp hv with hv | ⟨e, he, hs, ht⟩
      · exact hD v hv
      · exact (hD _ hs).tail ⟨e, he, rfl, ht⟩

/-- Instrumented search: the second result counts calls to `reachStep`.
Each such call scans the enabled-edge vector once. Set-operation costs are
separate from this counter. -/
def reachCloseCount (enabled : E → Bool) : ℕ → Finset V → Finset V × ℕ
  | 0, D => (D, 0)
  | n+1, D =>
    let next := G.reachStep enabled D
    if next = D then (D, 1) else
      let r := reachCloseCount enabled n next
      (r.1, r.2+1)

theorem reachCloseCount_value (enabled : E → Bool) (n : ℕ) (D : Finset V) :
    (G.reachCloseCount enabled n D).1 = G.reachClose enabled n D := by
  induction n generalizing D with
  | zero => rfl
  | succ n ih => simp only [reachCloseCount, reachClose]; split_ifs <;> simp_all

theorem reachCloseCount_bound (enabled : E → Bool) (n : ℕ) (D : Finset V) :
    (G.reachCloseCount enabled n D).2 ≤ n := by
  induction n generalizing D with
  | zero => exact le_refl _
  | succ n ih =>
    simp only [reachCloseCount]
    split_ifs
    · simp
    · exact Nat.add_le_add_right (ih _) 1

/-- At most `card V * card E` enabled-edge examinations in a reachable-set
search. This counts examinations, not machine time for set operations. -/
theorem reachable_edge_examinations (enabled : E → Bool) (s : V) :
    (G.reachCloseCount enabled (Fintype.card V) {s}).2 * Fintype.card E ≤
      Fintype.card V * Fintype.card E :=
  Nat.mul_le_mul_right _ (G.reachCloseCount_bound enabled _ _)

/-- A polynomial number of edge scans computes the full reachable set. -/
def reachableSet (enabled : E → Bool) (s : V) : Finset V :=
  G.reachClose enabled (Fintype.card V) {s}

theorem mem_reachableSet (enabled : E → Bool) (s t : V) :
    t ∈ G.reachableSet enabled s ↔ Relation.ReflTransGen (G.Adj {e | enabled e = true}) s t := by
  constructor
  · intro ht
    exact G.reachClose_sound enabled s _ _ (by
      intro v hv
      have : v = s := by simpa using hv
      subst v
      exact .refl) t ht
  · intro h
    have hs : s ∈ G.reachableSet enabled s := G.subset_reachClose enabled _ _ (by simp)
    have hc := G.reachClose_closed enabled (Fintype.card V) {s} (by simp)
    induction h with
    | refl => exact hs
    | @tail v w _ hedge ih =>
      obtain ⟨e, he, hsrc, htgt⟩ := hedge
      have hm := (G.mem_reachStep enabled (G.reachableSet enabled s) w).mpr
        (Or.inr ⟨e, he, hsrc ▸ ih, htgt⟩)
      change w ∈ G.reachStep enabled (G.reachClose enabled (Fintype.card V) {s}) at hm
      rw [hc] at hm
      exact hm

/-- A computable replacement for relational reachability. -/
def reaches (enabled : E → Bool) (s t : V) : Bool := decide (t ∈ G.reachableSet enabled s)

@[simp] theorem reaches_eq_true (enabled : E → Bool) (s t : V) :
    G.reaches enabled s t = true ↔ Relation.ReflTransGen (G.Adj {e | enabled e = true}) s t := by
  simp [reaches, G.mem_reachableSet]

/-- Membership on a nonempty directed cycle, using one outgoing edge and a return path. -/
def onCycle (enabled : E → Bool) (v : V) : Bool :=
  decide (∃ e, enabled e = true ∧ G.source e = v ∧ G.reaches enabled (G.target e) v = true)

@[simp] theorem onCycle_eq_true (enabled : E → Bool) (v : V) :
    G.onCycle enabled v = true ↔ G.VertexWitness {e | enabled e = true} v := by
  simp only [onCycle, decide_eq_true_eq, reaches_eq_true]
  constructor
  · rintro ⟨e, he, hs, hr⟩
    exact Relation.TransGen.head' ⟨e, he, hs, rfl⟩ hr
  · intro h
    obtain ⟨w, ⟨e, he, hs, ht⟩, hr⟩ := Relation.TransGen.head'_iff.mp h
    exact ⟨e, he, hs, ht ▸ hr⟩

/-- Exact zero detection on the positive-probability support. -/
def hasCycle (enabled : E → Bool) : Bool := decide (∃ v, G.onCycle enabled v = true)

@[simp] theorem hasCycle_eq_true (enabled : E → Bool) :
    G.hasCycle enabled = true ↔ G.Cyclic {e | enabled e = true} := by
  simp [hasCycle, Cyclic, VertexWitness]

end Digraph
end DirectedCycleFPRAS
