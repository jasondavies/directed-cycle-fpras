module

public import DirectedCycleFPRAS.RationalOracle
public import DirectedCycleFPRAS.RationalVertexOracle
public import DirectedCycleFPRAS.RationalCycleResources

@[expose] public section
namespace DirectedCycleFPRAS
open scoped BigOperators
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E) (U : Finset V)

/-- All reliability calls are actual rational Algorithm S programs, amplified
by a rational median. Compilation introduces fair bits only after inlining. -/
def rationalCycleCallback {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (inner : ℕ) (i : U) (p : E → ℚ) : RatProg ℚ :=
  (G.rationalVertexQuery vertices edges order i.val p).medianOf inner

/-- A polynomial bound for all choices inside one amplified reliability call. -/
def rationalCycleCallbackChoices (n m inner : ℕ) : ℕ :=
  inner*algSChoices (n+1) m (rationalVertexSamples n m)

open Classical
noncomputable section
set_option linter.unusedSectionVars false

def rationalCycleOracle {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (inner : ℕ) : Oracle (VertexQuery (E := E) U) :=
  liftRationalOracle (G.rationalCycleCallback U vertices edges order inner)
    (fun i q => G.vertexExact U (i,q))

theorem rationalCycleCallback_refines {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (inner : ℕ) (i : U) (p : E → ℚ) :
    RatProg.Refines (G.rationalCycleOracle U vertices edges order inner)
      (G.rationalCycleCallback U vertices edges order inner i p)
      (.query (i,fun e => (p e : ℝ)) Prog.ret) Rat.cast :=
  liftRationalOracle_refines _ _ i p

theorem rationalVertexQuery_good_failure {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (hnodup : order.Nodup) (hcomplete : ∀ e, e∈order) (i : U) (p : E → ℚ) :
    (G.rationalVertexQuery vertices edges order i.val p).nominal.exp noOracle
      (fun r => if G.VertexGood U (rejectionAccuracy m) (i,fun e => (p e : ℝ)) (r : ℝ)
        then 0 else 1) ≤ 1/4 := by
  by_cases hp : Prob01 (fun e => (p e : ℝ))
  · by_cases hz : 0<eventMass (fun e => (p e : ℝ)) (G.vertexEvents U i)
    · have hr : eventMass (fun e => (p e : ℝ)) (G.vertexEvents U i) =
          (G.splitVertex i.val).reliability (fun e => (p e : ℝ)) (some i.val) none := by
        exact G.vertex_weight_reliability (fun e => (p e : ℝ)) i.val
      have h := G.rationalVertexQuery_accuracy vertices edges order hnodup hcomplete i.val p hp (hr ▸ hz)
      have hqr := hr ▸ hz
      simpa [VertexGood,hp,hqr,hr] using h.trans (show (1/8 : ℝ) ≤ 1/4 by norm_num)
    · simp [VertexGood,hz,Prog.exp_const]
  · simp [VertexGood,hp,Prog.exp_const]

theorem rationalCycleOracle_failure {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (hnodup : order.Nodup) (hcomplete : ∀ e, e∈order) (inner : ℕ)
    (x : VertexQuery (E := E) U) :
    (∑ s, if G.VertexGood U (rejectionAccuracy m) x
      ((G.rationalCycleOracle U vertices edges order inner).answer x s) then 0 else
      ((G.rationalCycleOracle U vertices edges order inner).law x).value s) ≤ (7/8 : ℝ)^inner := by
  apply liftRationalOracle_failure _ _ (fun i q r => G.VertexGood U (rejectionAccuracy m) (i,q) r)
    (by positivity)
  · intro i q
    exact G.vertexExact_good U (rejectionAccuracy_bounds m).1.le (i,q)
  · intro i q
    exact RatProg.medianOf_failure _ inner _ (G.vertexGood_interval U _ _)
      (G.rationalVertexQuery_good_failure U vertices edges order hnodup hcomplete i q)

/-- Nominal counting accuracy after inlining actual amplified Algorithm S calls.
The witness and arc orders are explicit executable data. -/
theorem rationalVertexCount_failure {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (arcOrder : List E) (hnodup : arcOrder.Nodup) (hcomplete : ∀ e, e∈arcOrder)
    (witnessOrder : Fin k ≃ U) (cover : List U) (hcover : ∀ i, i∈cover)
    (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ))) (d : U) (D inner : ℕ)
    (hZ : 0<(edgeLaw (fun e => (p e : ℝ)) (fun e => (hp e).1) (fun e => (hp e).2)).toMass.unionMass
      (G.vertexEvents U)) {eps : ℝ} (heps : 0<eps)
    (hD : 64*(U.card : ℝ)/eps^2 ≤ D) :
    let Z := (edgeLaw (fun e => (p e : ℝ)) (fun e => (hp e).1) (fun e => (hp e).2)).toMass.unionMass
      (G.vertexEvents U)
    (G.rationalVertexCount U witnessOrder p
      (G.rationalCycleCallback U vertices edges arcOrder inner) cover arcOrder d D).nominal.exp noOracle
      (fun z => if eps*Z ≤ |(z : ℝ)-Z| then 1 else 0) ≤
        1/16+(cover.length+2*arcOrder.length*D : ℕ)*(7/8 : ℝ)^inner := by
  dsimp only
  let O := G.rationalCycleOracle U vertices edges arcOrder inner
  let good := G.VertexGood U (rejectionAccuracy m)
  let fix := G.vertexExact U
  have hlen : arcOrder.length=m := by
    have hm : Fintype.card E=m := by simpa using (Fintype.card_congr edges).symm
    have hl : arcOrder.toFinset=Finset.univ := by ext e; simp [hcomplete e]
    rw [← List.toFinset_card_of_nodup hnodup,hl,Finset.card_univ,hm]
  have ho := G.rationalCycleOracle_failure U vertices edges arcOrder hnodup hcomplete inner
  rw [G.rationalVertexCount_refines U witnessOrder O p hp _
    (G.rationalCycleCallback_refines U vertices edges arcOrder inner) cover arcOrder d D
    (fun z => if eps*(edgeLaw (fun e => (p e : ℝ)) (fun e => (hp e).1)
      (fun e => (hp e).2)).toMass.unionMass (G.vertexEvents U) ≤
      |z-(edgeLaw (fun e => (p e : ℝ)) (fun e => (hp e).1)
      (fun e => (hp e).2)).toMass.unionMass (G.vertexEvents U)| then 1 else 0)]
  apply (Prog.exp_le_repair O good fix (by positivity) ho
    (fun _ => by split_ifs <;> norm_num) (fun _ => by split_ifs <;> norm_num)
    (witnessCount_queryBound (G.vertexEvents U) (fun i q => (i,q)) (G.vertexFeasible U)
      _ hp cover arcOrder d D)).trans
  apply add_le_add _ (le_refl _)
  apply witnessCount_ideal (O.repair good fix) (G.vertexEvents U) (fun i q => (i,q))
    (G.vertexFeasible U) Prob01 (fun _ h => h) (fun _ e b h => prob01_pin h e b)
    (G.vertexFeasible_iff U) _ hp cover hcover arcOrder hcomplete d _ hZ heps
    (by simpa using hD)
  intro i q hq hz seed
  have ha := O.repair_good good fix (G.vertexExact_good U (rejectionAccuracy_bounds m).1.le) (i,q) seed
  rw [hlen]
  exact ha hq hz

/-- Nominal conditional-sampling error, including failures of the actual
amplified rational reliability callback. -/
theorem rationalVertexSample_error {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (arcOrder : List E) (hnodup : arcOrder.Nodup) (hcomplete : ∀ e, e∈arcOrder)
    (witnessOrder : Fin k ≃ U) (cover : List U) (hcover : ∀ i, i∈cover)
    (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ))) (d : U) (fallback : E → Bool)
    (r inner : ℕ)
    (hZ : 0<(edgeLaw (fun e => (p e : ℝ)) (fun e => (hp e).1) (fun e => (hp e).2)).toMass.unionMass
      (G.vertexEvents U)) (f : (E → Bool) → ℝ) (hf0 : ∀ x, 0≤f x) (hf1 : ∀ x, f x≤1) :
    |(G.rationalVertexSample U witnessOrder p
      (G.rationalCycleCallback U vertices edges arcOrder inner) cover arcOrder d fallback (4*U.card*r)).nominal.exp noOracle f-
      (unionLaw (edgeLaw (fun e => (p e : ℝ)) (fun e => (hp e).1) (fun e => (hp e).2)).toMass
        (G.vertexEvents U) hZ).expectation f| ≤
      (1/2 : ℝ)^r+(cover.length+2*arcOrder.length*(4*U.card*r) : ℕ)*(7/8 : ℝ)^inner := by
  let O := G.rationalCycleOracle U vertices edges arcOrder inner
  let good := G.VertexGood U (rejectionAccuracy m)
  let fix := G.vertexExact U
  have hlen : arcOrder.length=m := by
    have hm : Fintype.card E=m := by simpa using (Fintype.card_congr edges).symm
    have hl : arcOrder.toFinset=Finset.univ := by ext e; simp [hcomplete e]
    rw [← List.toFinset_card_of_nodup hnodup,hl,Finset.card_univ,hm]
  have ho := G.rationalCycleOracle_failure U vertices edges arcOrder hnodup hcomplete inner
  have hc := Prog.exp_repair_abs O good fix (by positivity) ho
    (witnessSample (G.vertexEvents U) (fun i q => (i,q)) (G.vertexFeasible U)
      (fun e => (p e : ℝ)) hp cover arcOrder d fallback (4*U.card*r))
    (witnessSample_queryBound (G.vertexEvents U) (fun i q => (i,q)) (G.vertexFeasible U)
      _ hp cover arcOrder d fallback (4*U.card*r)) f hf0 hf1
  have ha := witnessSample_ideal (O.repair good fix) (G.vertexEvents U) (fun i q => (i,q))
    (G.vertexFeasible U) Prob01 (fun _ h => h) (fun _ e b h => prob01_pin h e b)
    (G.vertexFeasible_iff U) _ hp cover hcover arcOrder hcomplete d
    (fun i q hq hz seed => by
      have h := O.repair_good good fix (G.vertexExact_good U (rejectionAccuracy_bounds m).1.le) (i,q) seed
      rw [hlen]
      exact h hq hz) hZ fallback r f hf0 hf1
  simp only [Fintype.card_coe] at ha
  have hr := G.rationalVertexSample_refines U witnessOrder O p hp _
    (G.rationalCycleCallback_refines U vertices edges arcOrder inner) cover arcOrder d fallback (4*U.card*r) f
  simp only [id_eq] at hr
  rw [hr]
  exact (abs_sub_le _ _ _).trans ((add_le_add hc ha).trans_eq (add_comm _ _))

theorem rationalCycleCallback_choiceBound {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (arcOrder : List E) (hlen : arcOrder.length=m) (inner : ℕ) (i : U) (p : E → ℚ) :
    RatProg.ChoiceBound (G.rationalCycleCallback U vertices edges arcOrder inner i p)
      (rationalCycleCallbackChoices n m inner) := by
  unfold rationalCycleCallback rationalCycleCallbackChoices rationalVertexQuery
  apply RatProg.ChoiceBound.medianOf
  exact (G.rationalSplit i.val).rationalAlgS_choiceBound p _ edges arcOrder _ (some i.val) none _ hlen

/-- Compiled counting accuracy, including every inlined reliability call and
outer median. The final additive term is the single global bit-rounding budget. -/
theorem rationalVertexCount_compiled_failure {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (arcOrder : List E) (hnodup : arcOrder.Nodup) (hcomplete : ∀ e, e∈arcOrder)
    (witnessOrder : Fin k ≃ U) (cover : List U) (hcover : ∀ i, i∈cover)
    (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ))) (d : U) (D inner outer b : ℕ)
    (hZ : 0<(edgeLaw (fun e => (p e : ℝ)) (fun e => (hp e).1) (fun e => (hp e).2)).toMass.unionMass
      (G.vertexEvents U)) {eps : ℝ} (heps : 0<eps)
    (hD : 64*(U.card : ℝ)/eps^2 ≤ D)
    (hinner : (cover.length+2*arcOrder.length*D : ℕ)*(7/8 : ℝ)^inner ≤ 1/16) :
    let Z := (edgeLaw (fun e => (p e : ℝ)) (fun e => (hp e).1) (fun e => (hp e).2)).toMass.unionMass
      (G.vertexEvents U)
    let C := rationalCycleCallbackChoices n m inner
    (((G.rationalVertexCount U witnessOrder p
      (G.rationalCycleCallback U vertices edges arcOrder inner) cover arcOrder d D).medianOf outer).compile b).toProg.exp noOracle
      (fun z => if eps*Z ≤ |(z : ℝ)-Z| then 1 else 0) ≤ (7/8 : ℝ)^outer+
        (outer*(cover.length*C+D*(k+2+arcOrder.length*(2*C+2))) : ℕ)/(2 : ℝ)^b := by
  dsimp only
  let Z := (edgeLaw (fun e => (p e : ℝ)) (fun e => (hp e).1) (fun e => (hp e).2)).toMass.unionMass (G.vertexEvents U)
  let base := G.rationalVertexCount U witnessOrder p
    (G.rationalCycleCallback U vertices edges arcOrder inner) cover arcOrder d D
  have hb := G.rationalVertexCount_failure U vertices edges arcOrder hnodup hcomplete
    witnessOrder cover hcover p hp d D inner hZ heps hD
  have he (z : ℚ) : (if |(z : ℝ)-Z|<eps*Z then (0 : ℝ) else 1) =
      (if eps*Z≤|(z : ℝ)-Z| then 1 else 0) := by
    by_cases h : |(z : ℝ)-Z|<eps*Z
    · simp [h,not_le.mpr h]
    · simp [h,le_of_not_gt h]
  have hm := RatProg.medianOf_failure base outer (fun z => |z-Z|<eps*Z)
    (by intro a b c ha hc hab hbc; rw [abs_lt] at *; constructor <;> linarith)
    (by simp_rw [he]; dsimp [base,Z]; linarith)
  simp_rw [he] at hm
  have hlen : arcOrder.length=m := by
    have hm : Fintype.card E=m := by simpa using (Fintype.card_congr edges).symm
    have hl : arcOrder.toFinset=Finset.univ := by ext e; simp [hcomplete e]
    rw [← List.toFinset_card_of_nodup hnodup,hl,Finset.card_univ,hm]
  have hc := G.rationalVertexCount_compile_error U witnessOrder p
    (G.rationalCycleCallback U vertices edges arcOrder inner)
    (G.rationalCycleCallback_choiceBound U vertices edges arcOrder hlen inner)
    cover arcOrder d D outer b (fun z => if eps*Z≤|(z : ℝ)-Z| then 1 else 0)
    (fun _ => by split_ifs <;> norm_num) (fun _ => by split_ifs <;> norm_num)
  have hh := (abs_le.mp hc).2
  change _ ≤ _
  dsimp [base,Z] at hm hh
  linarith

/-- Total-variation test bound for the complete compiled conditional sampler. -/
theorem rationalVertexSample_compiled_error {n m k : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (arcOrder : List E) (hnodup : arcOrder.Nodup) (hcomplete : ∀ e, e∈arcOrder)
    (witnessOrder : Fin k ≃ U) (cover : List U) (hcover : ∀ i, i∈cover)
    (p : E → ℚ) (hp : Prob01 (fun e => (p e : ℝ))) (d : U) (fallback : E → Bool)
    (r inner b : ℕ)
    (hZ : 0<(edgeLaw (fun e => (p e : ℝ)) (fun e => (hp e).1) (fun e => (hp e).2)).toMass.unionMass
      (G.vertexEvents U)) (f : (E → Bool) → ℝ) (hf0 : ∀ x, 0≤f x) (hf1 : ∀ x, f x≤1) :
    let C := rationalCycleCallbackChoices n m inner
    |((G.rationalVertexSample U witnessOrder p
      (G.rationalCycleCallback U vertices edges arcOrder inner) cover arcOrder d fallback (4*U.card*r)).compile b).toProg.exp noOracle f-
      (unionLaw (edgeLaw (fun e => (p e : ℝ)) (fun e => (hp e).1) (fun e => (hp e).2)).toMass
        (G.vertexEvents U) hZ).expectation f| ≤
      (1/2 : ℝ)^r+(cover.length+2*arcOrder.length*(4*U.card*r) : ℕ)*(7/8 : ℝ)^inner+
        (cover.length*C+(4*U.card*r)*(k+2+arcOrder.length*(2*C+2)) : ℕ)/(2 : ℝ)^b := by
  dsimp only
  have hn := G.rationalVertexSample_error U vertices edges arcOrder hnodup hcomplete witnessOrder cover hcover
    p hp d fallback r inner hZ f hf0 hf1
  have hlen : arcOrder.length=m := by
    have hm : Fintype.card E=m := by simpa using (Fintype.card_congr edges).symm
    have hl : arcOrder.toFinset=Finset.univ := by ext e; simp [hcomplete e]
    rw [← List.toFinset_card_of_nodup hnodup,hl,Finset.card_univ,hm]
  have hc := G.rationalVertexSample_compile_error U witnessOrder p
    (G.rationalCycleCallback U vertices edges arcOrder inner)
    (G.rationalCycleCallback_choiceBound U vertices edges arcOrder hlen inner)
    cover arcOrder d fallback (4*U.card*r) b f hf0 hf1
  exact (abs_sub_le _ _ _).trans ((add_le_add hc hn).trans_eq (add_comm _ _))

end
end Digraph
end DirectedCycleFPRAS
