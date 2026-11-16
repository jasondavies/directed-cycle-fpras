module

public import DirectedCycleFPRAS.VertexWitness
public import DirectedCycleFPRAS.PositiveOracle

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
open Classical
noncomputable section
set_option linter.unusedSectionVars false
namespace AcyclicityReduction
variable {V : Type} (H : V → V → Prop)

abbrev Edge := Sum V {uv : V × V // H uv.1 uv.2}

def graph : Digraph (V × Bool) (Edge H) where
  source e := match e with
    | .inl v => (v, false)
    | .inr uv => (uv.val.1, true)
  target e := match e with
    | .inl v => (v, true)
    | .inr uv => (uv.val.2, false)

def configuration (selected : V → Bool) : Edge H → Bool
  | .inl v => selected v
  | .inr _ => true

def Independent (selected : V → Bool) : Prop :=
  ∀ u v, H u v → ¬ (selected u = true ∧ selected v = true)

/-- Under an independent selection, every retained arc strictly increases a
four-level potential, so the constructed directed graph is acyclic. -/
theorem independent_acyclic (selected : V → Bool) (h : Independent H selected) :
    ¬ (graph H).Cyclic (Digraph.retained (configuration H selected)) := by
  let rank : V × Bool → ℤ := fun x =>
    if selected x.1 then (if x.2 then 1 else 0) else (if x.2 then -1 else 2)
  have step : ∀ a b, (graph H).Adj (Digraph.retained (configuration H selected)) a b → rank a < rank b := by
    rintro a b ⟨e, he, rfl, rfl⟩
    cases e with
    | inl v =>
      change selected v = true at he
      simp [graph, rank, he]
    | inr uv =>
      have hn := h uv.val.1 uv.val.2 uv.property
      cases hu : selected uv.val.1 <;> cases hv : selected uv.val.2 <;>
        simp_all [graph, rank]
  rintro ⟨v, hv⟩
  have ht := hv.lift rank step
  have collapse : ∀ {a b : ℤ}, Relation.TransGen (fun x y : ℤ => x < y) a b → a < b := by
    intro a b hab
    induction hab with
    | single h => exact h
    | tail _ h ih => exact lt_trans ih h
  exact (lt_irrefl (rank v)) (collapse ht)

/-- An adjacent selected pair creates a directed four-cycle. -/
theorem adjacent_cycle (hsym : ∀ ⦃u v⦄, H u v → H v u) (selected : V → Bool)
    {u v : V} (huv : H u v) (hu : selected u = true) (hv : selected v = true) :
    (graph H).Cyclic (Digraph.retained (configuration H selected)) := by
  have gate (x : V) (hx : selected x = true) :
      (graph H).Adj (Digraph.retained (configuration H selected)) (x, false) (x, true) :=
    ⟨.inl x, hx, rfl, rfl⟩
  have connector (x y : V) (hxy : H x y) :
      (graph H).Adj (Digraph.retained (configuration H selected)) (x, true) (y, false) :=
    ⟨.inr ⟨(x,y), hxy⟩, rfl, rfl, rfl⟩
  exact ⟨(u,false), (((Relation.TransGen.single (gate u hu)).tail
    (connector u v huv)).tail (gate v hv)).tail (connector v u (hsym huv))⟩

/-- The exact graph-theoretic reduction underlying complement hardness. -/
theorem acyclic_iff_independent (hsym : ∀ ⦃u v⦄, H u v → H v u) (selected : V → Bool) :
    ¬ (graph H).Cyclic (Digraph.retained (configuration H selected)) ↔ Independent H selected := by
  constructor
  · intro hn u v huv hpair
    exact hn (adjacent_cycle H hsym selected huv hpair.1 hpair.2)
  · exact independent_acyclic H selected

variable [Fintype V]

/-- Each subset has mass `2^(-|V|)` under independent fair gate choices. -/
theorem fair_gate_mass (selected : V → Bool) :
    edgeWeight (fun _ : V => (1/2 : ℝ)) selected = 1/(2 : ℝ)^(Fintype.card V) := by
  unfold edgeWeight
  have he : ∀ v, (if selected v then (1/2 : ℝ) else 1-1/2) = 1/2 := by intro v; split_ifs <;> norm_num
  simp_rw [he]
  simp

/-- The probability of acyclicity in the fair-gate construction is the number
of independent sets divided by `2^|V|`. External counting hardness applies to
this exact equality. -/
theorem acyclicity_probability (hsym : ∀ ⦃u v⦄, H u v → H v u) :
    eventMass (fun _ : V => (1/2 : ℝ))
      (fun selected => ¬ (graph H).Cyclic (Digraph.retained (configuration H selected))) =
    (Fintype.card {selected : V → Bool // Independent H selected} : ℝ)/(2 : ℝ)^Fintype.card V := by
  simp only [eventMass, acyclic_iff_independent H hsym, fair_gate_mass]
  simp [Fintype.card_subtype, ← Finset.sum_filter, div_eq_mul_inv]

/-- Random vertex gates and deterministic adjacency connectors. -/
def retention : Edge H → ℝ
  | .inl _ => 1/2
  | .inr _ => 1

theorem retention_values (e : Edge H) : retention H e = 1/2 ∨ retention H e = 1 := by
  cases e <;> simp [retention]

/-- The gate experiment is the independent edge-retention model of the paper. -/
theorem edge_retention_probability (hsym : ∀ ⦃u v⦄, H u v → H v u) :
    eventMass (retention H) (fun ω => ¬ (graph H).Cyclic (Digraph.retained ω)) =
      (Fintype.card {selected : V → Bool // Independent H selected} : ℝ)/(2 : ℝ)^Fintype.card V := by
  have hj : Function.Injective (Sum.inl : V → Edge H) := Sum.inl_injective
  have hforced : ∀ e : Edge H, (¬ ∃ v, Sum.inl v = e) → retention H e = 0 ∨ retention H e = 1 := by
    intro e he
    cases e with
    | inl v => exact False.elim (he ⟨v,rfl⟩)
    | inr uv => exact Or.inr rfl
  rw [eventMass_restrict hj hforced]
  have hext (a : V → Bool) : extend Sum.inl (retention H) a = configuration H a := by
    funext e
    cases e with
    | inl v => exact extend_apply hj _ a v
    | inr uv =>
      rw [extend_of_not _ a (by simp)]
      simp [retention, configuration]
  simp_rw [hext]
  exact acyclicity_probability H hsym

end AcyclicityReduction
end
end DirectedCycleFPRAS
