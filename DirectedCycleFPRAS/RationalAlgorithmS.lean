module

public import DirectedCycleFPRAS.RationalProgramBounds
public import DirectedCycleFPRAS.AlgorithmSOrdered

@[expose] public section

/-! Algorithm S with executable rational arithmetic and explicit finite
choice orders. The nominal-law refinement identifies the exact probability
semantics with the ordered real program; finite-bit compilation uses RatProg. -/
set_option linter.unusedSectionVars false
namespace DirectedCycleFPRAS
open scoped BigOperators
namespace Digraph
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : Digraph V E) (p : E → ℚ)

def rFirst (rank : E → ℕ) (R : Finset V) (u : V) (e : E) : ℚ :=
  if G.source e = u ∧ G.target e ∉ R then
    p e * ∏ e' ∈ Finset.univ.filter
      (fun e' => G.source e' = u ∧ G.target e' ∉ R ∧ rank e' < rank e), (1-p e')
  else 0

def rGamma (rank : E → ℕ) (R : Finset V) (u : V) : ℚ :=
  ∑ e, G.rFirst p rank R u e

def rPre (rank : E → ℕ) (R : Finset V) (u : V) (j e : E) : Option Bool :=
  if G.source e = u ∧ G.target e ∉ R then
    (if e=j then some true else if rank e<rank j then some false else none)
  else none

def rScan (R : Finset V) (pre : E → Option Bool) (z : V) (flag : Bool) :
    List E → Finset V → List (V × Bool) → RatProg (Finset V × List (V × Bool))
  | [], D, st => .ret (D,st)
  | e::l, D, st =>
    if G.source e=z ∧ G.target e∉D then
      ((pre e).elim (RatProg.weightedEquiv finTwoEquiv
        (fun b => if b then p e else 1-p e) false RatProg.ret) RatProg.ret).bind fun o =>
        if o then rScan R pre z flag l (insert (G.target e) D)
          ((G.target e,flag && decide (G.target e∉R))::st)
        else rScan R pre z flag l D st
    else rScan R pre z flag l D st

def rDfs (order : List E) (R : Finset V) (pre : E → Option Bool) (v : V) :
    ℕ → Finset V → List (V × Bool) → RatProg (Option (Finset V))
  | 0, _, _ => .ret none
  | _+1, _, [] => .ret none
  | f+1, D, (z,flag)::st =>
    if z=v then .ret (if flag then some D else none)
    else (G.rScan p R pre z flag order D st).bind fun r => rDfs order R pre v f r.1 r.2

def rIter {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (rank : E → ℕ) (dfsFuel : ℕ)
    (R : Finset V) (qh : V → ℚ) (pools : V → List (Finset V)) (M : ℕ) (v : V) :
    RatProg (Option (Finset V)) :=
  RatProg.weightedEquiv ((finSuccEquiv n).trans vertices.optionCongr)
    (fun o : Option V => o.elim 0 fun u => if u∈R then qh u*G.rGamma p rank R u else 0)
    none fun o => o.elim (.ret none) fun u =>
      RatProg.weighted (fun i : Fin (M+1) => if i.val<(pools u).length then 1 else 0) 0 fun i =>
        RatProg.weightedEquiv ((finSuccEquiv m).trans edges.optionCongr)
          (fun j : Option E => j.elim 0 (G.rFirst p rank R u)) none fun j =>
            j.elim (.ret none) fun j =>
              G.rDfs p order R (G.rPre rank R u j) v dfsFuel ((pools u).getD i ∅) [(u,true)]

def rGenerate {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (rank : E → ℕ) (dfsFuel : ℕ)
    (R : Finset V) (qh : V → ℚ) (pools : V → List (Finset V)) (M : ℕ) (v : V) :
    ℕ → RatProg (ℕ × List (Finset V))
  | 0 => .ret (0,[])
  | i+1 => (rGenerate vertices edges order rank dfsFuel R qh pools M v i).bind fun acc =>
      (G.rIter p vertices edges order rank dfsFuel R qh pools M v).bind fun o =>
        .ret (o.elim acc fun D => (acc.1+1,D::acc.2))

def rPhi (rank : E → ℕ) (R : Finset V) (qh : V → ℚ) : ℚ :=
  ∑ u, if u∈R then qh u*G.rGamma p rank R u else 0

def rRounds {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (rank : E → ℕ) (dfsFuel : ℕ) (t : V) (M : ℕ) :
    ℕ → Finset V → (V → ℚ) → (V → List (Finset V)) → RatProg ℚ
  | 0, _, qh, _ => .ret (qh t)
  | f+1, R, qh, pools =>
    if t∈R then .ret (qh t) else
      ((order.filter fun e => G.source e∈R ∧ G.target e∉R).argmax
        fun e => qh (G.source e)*p e).elim (.ret 0) fun e =>
          if qh (G.source e)*p e≤0 then .ret 0 else
            (G.rGenerate p vertices edges order rank dfsFuel R qh pools M (G.target e) M).bind fun res =>
              rRounds vertices edges order rank dfsFuel t M f (insert (G.target e) R)
                (Function.update qh (G.target e) (G.rPhi p rank R qh*res.1/M))
                (Function.update pools (G.target e) res.2)

/-- Executable Algorithm S; enumeration order is part of the input. -/
def rationalAlgS {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (rank : E → ℕ) (s t : V) (M : ℕ) : RatProg ℚ :=
  G.rRounds p vertices edges order rank (Fintype.card V+1) t M (Fintype.card V)
    {s} (fun u => if u=s then 1 else 0) (fun u => if u=s then [{s}] else [])

open Classical
noncomputable section

theorem rFirst_cast (rank : E → ℕ) (R : Finset V) (u : V) (e : E) :
    (G.rFirst p rank R u e : ℝ) = G.oFirst (fun j => (p j : ℝ)) rank R u e := by
  unfold rFirst oFirst cutAt
  split_ifs <;> simp [Rat.cast_prod,and_assoc]

theorem rGamma_cast (rank : E → ℕ) (R : Finset V) (u : V) :
    (G.rGamma p rank R u : ℝ) = G.oGamma (fun j => (p j : ℝ)) rank R u := by
  simp [rGamma,oGamma,Rat.cast_sum,G.rFirst_cast p]

theorem rPre_eq (rank : E → ℕ) (R : Finset V) (u : V) (j : E) :
    G.rPre rank R u j = G.oPre rank R u j := by
  funext e
  unfold rPre oPre cutAt
  split_ifs <;> rfl

theorem rPhi_cast (rank : E → ℕ) (R : Finset V) (qh : V → ℚ) :
    (G.rPhi p rank R qh : ℝ) = G.oPhi (fun j => (p j : ℝ)) rank R (fun u => (qh u : ℝ)) := by
  simp [rPhi,oPhi,Rat.cast_sum,G.rGamma_cast p]

theorem argmax_rat_cast {α : Type} (f : α → ℚ) (l : List α) :
    l.argmax (fun a => (f a : ℝ)) = l.argmax f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.argmax_cons,List.argmax_cons,ih]
    cases l.argmax f <;> simp

/-- Exact nominal law of the rational edge scan. -/
theorem rScan_law (R : Finset V) (pre : E → Option Bool) (z : V) (flag : Bool)
    (l : List E) (D : Finset V) (st : List (V × Bool)) (f : (Finset V × List (V × Bool)) → ℝ) :
    (G.rScan p R pre z flag l D st).nominal.exp noOracle f =
      (G.sScan (fun e => (p e : ℝ)) R pre z flag l D st).exp noOracle f := by
  induction l generalizing D st with
  | nil => rfl
  | cons e l ih =>
    simp only [rScan,sScan]
    split_ifs
    · simp only [RatProg.nominal_bind,Prog.exp_bind]
      cases he : pre e with
      | none =>
        simp only [Option.elim_none,RatProg.weightedEquiv_exp,Prog.exp,coin]
        have hw : (fun b : Bool => ((if b then p e else 1-p e : ℚ) : ℝ)) =
            (fun b => if b then (p e : ℝ) else 1-(p e : ℝ)) := by funext b; cases b <;> simp
        rw [hw]
        apply Finset.sum_congr rfl
        intro b _
        congr 1
        cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,ih,RatProg.nominal,Prog.exp]
      | some b =>
        cases b <;> simp only [Option.elim_some,RatProg.nominal,Prog.exp,
          Bool.false_eq_true,ite_false,ite_true,ih]
    · exact ih D st

/-- Exact nominal law of the rational DFS. -/
theorem rDfs_law (order : List E) (R : Finset V) (pre : E → Option Bool) (v : V)
    (fuel : ℕ) (D : Finset V) (st : List (V × Bool)) (f : Option (Finset V) → ℝ) :
    (G.rDfs p order R pre v fuel D st).nominal.exp noOracle f =
      (G.oDfs (fun e => (p e : ℝ)) order R pre v fuel D st).exp noOracle f := by
  induction fuel generalizing D st with
  | zero => rfl
  | succ fuel ih =>
    cases st with
    | nil => rfl
    | cons zf st =>
      rcases zf with ⟨z,flag⟩
      simp only [rDfs,oDfs]
      split_ifs
      · rfl
      · rfl
      · simp only [RatProg.nominal_bind,Prog.exp_bind,ih]
        exact G.rScan_law p R pre z flag order D st _

/-- Exact nominal law of one rational snapshot proposal. -/
theorem rIter_law {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (rank : E → ℕ) (dfsFuel : ℕ) (R : Finset V)
    (qh : V → ℚ) (pools : V → List (Finset V)) (M : ℕ) (v : V)
    (f : Option (Finset V) → ℝ) :
    (G.rIter p vertices edges order rank dfsFuel R qh pools M v).nominal.exp noOracle f =
      (G.oIter (fun e => (p e : ℝ)) order rank dfsFuel R (fun u => (qh u : ℝ)) pools M v).exp noOracle f := by
  unfold rIter oIter
  rw [RatProg.weightedEquiv_exp]
  simp only [Prog.exp]
  have hw : (fun o : Option V => ((o.elim 0 fun u => if u∈R then qh u*G.rGamma p rank R u else 0 : ℚ) : ℝ)) =
      (fun o => o.elim 0 fun u => if u∈R then (qh u : ℝ)*G.oGamma (fun e => (p e : ℝ)) rank R u else 0) := by
    funext o; cases o with
    | none => simp
    | some u => simp only [Option.elim_some]; split_ifs <;> simp [G.rGamma_cast p]
  rw [hw]
  apply Finset.sum_congr rfl
  intro o _
  congr 1
  cases o with
  | none => rfl
  | some u =>
    simp only [Option.elim_some,RatProg.weighted_exp]
    have hpool : (fun i : Fin (M+1) => ((if i.val<(pools u).length then 1 else 0 : ℚ) : ℝ)) =
        (fun i => if i.val<(pools u).length then (1 : ℝ) else 0) := by funext i; split_ifs <;> simp
    rw [hpool]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [RatProg.weightedEquiv_exp]
    have he : (fun j : Option E => ((j.elim 0 (G.rFirst p rank R u) : ℚ) : ℝ)) =
        (fun j => j.elim 0 (G.oFirst (fun e => (p e : ℝ)) rank R u)) := by
      funext j; cases j <;> simp [G.rFirst_cast p]
    rw [he]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    cases j with
    | none => rfl
    | some j => simpa only [Option.elim_some,G.rPre_eq] using
        G.rDfs_law p order R (G.rPre rank R u j) v dfsFuel ((pools u).getD i ∅) [(u,true)] f

/-- Exact nominal law of the empirical snapshot pool. -/
theorem rGenerate_law {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (rank : E → ℕ) (dfsFuel : ℕ) (R : Finset V)
    (qh : V → ℚ) (pools : V → List (Finset V)) (M : ℕ) (v : V)
    (count : ℕ) (f : (ℕ × List (Finset V)) → ℝ) :
    (G.rGenerate p vertices edges order rank dfsFuel R qh pools M v count).nominal.exp noOracle f =
      (G.oGenerate (fun e => (p e : ℝ)) order rank dfsFuel R (fun u => (qh u : ℝ)) pools M v count).exp noOracle f := by
  induction count generalizing f with
  | zero => rfl
  | succ count ih =>
    simp only [rGenerate,oGenerate,RatProg.nominal_bind,Prog.exp_bind]
    simp_rw [G.rIter_law p]
    exact ih _

/-- Exact nominal law of the rational rounds, including unsuccessful exits. -/
theorem rRounds_law {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (rank : E → ℕ) (dfsFuel : ℕ) (t : V) (M fuel : ℕ)
    (R : Finset V) (qh : V → ℚ) (pools : V → List (Finset V)) (f : ℝ → ℝ) :
    (G.rRounds p vertices edges order rank dfsFuel t M fuel R qh pools).nominal.exp noOracle
      (fun q => f (q : ℝ)) =
      (G.oRounds (fun e => (p e : ℝ)) order rank dfsFuel t M fuel R
        (fun u => (qh u : ℝ)) pools).exp noOracle f := by
  induction fuel generalizing R qh pools with
  | zero => rfl
  | succ fuel ih =>
    simp only [rRounds,oRounds]
    by_cases ht : t∈R
    · simp only [ht,ite_true,RatProg.nominal,Prog.exp]
    · simp only [ht,ite_false]
      have he : ((order.filter fun e => G.source e∈R ∧ G.target e∉R).argmax
          fun e => (qh (G.source e) : ℝ)*(p e : ℝ)) =
          ((order.filter fun e => G.source e∈R ∧ G.target e∉R).argmax
          fun e => qh (G.source e)*p e) := by
        simpa only [Rat.cast_mul] using argmax_rat_cast
          (fun e => qh (G.source e)*p e) (order.filter fun e => G.source e∈R ∧ G.target e∉R)
      rw [he]
      cases hs : (order.filter fun e => G.source e∈R ∧ G.target e∉R).argmax
          (fun e => qh (G.source e)*p e) with
      | none => simp [RatProg.nominal,Prog.exp]
      | some e =>
        simp only [Option.elim_some]
        by_cases hz : qh (G.source e)*p e≤0
        · have hz' : (qh (G.source e) : ℝ)*(p e : ℝ)≤0 := by exact_mod_cast hz
          simp only [hz,hz',ite_true,RatProg.nominal,Prog.exp,Rat.cast_zero]
        · have hz' : ¬(qh (G.source e) : ℝ)*(p e : ℝ)≤0 := by exact_mod_cast hz
          simp only [hz,hz',ite_false,RatProg.nominal_bind,Prog.exp_bind,ih]
          rw [G.rGenerate_law]
          congr 1
          funext res
          have hu : (fun u => ((Function.update qh (G.target e)
              (G.rPhi p rank R qh*res.1/M)) u : ℝ)) =
              Function.update (fun u => (qh u : ℝ)) (G.target e)
                (G.oPhi (fun e => (p e : ℝ)) rank R (fun u => (qh u : ℝ))*res.1/M) := by
            funext u
            by_cases h : u=G.target e
            · subst u
              simp [G.rPhi_cast p]
            · simp [Function.update_of_ne h]
          rw [hu]

/-- The executable rational transcription has exactly the ordered Algorithm S
law before finite-bit rounding. -/
theorem rationalAlgS_law {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (rank : E → ℕ) (s t : V) (M : ℕ) (f : ℝ → ℝ) :
    (G.rationalAlgS p vertices edges order rank s t M).nominal.exp noOracle (fun q => f (q : ℝ)) =
      (G.orderedAlgS (fun e => (p e : ℝ)) order rank (Fintype.card V+1)
        (Fintype.card V) s t M).exp noOracle f := by
  unfold rationalAlgS orderedAlgS
  rw [G.rRounds_law]
  have hinit : (fun u => ((if u=s then 1 else 0 : ℚ) : ℝ)) = (fun u => if u=s then (1 : ℝ) else 0) := by
    funext u; split_ifs <;> simp
  rw [hinit]

/-- Alternative-count bound for the executable rational scan. -/
theorem rScan_choiceBound (R : Finset V) (pre : E → Option Bool) (z : V) (flag : Bool)
    (l : List E) (D : Finset V) (st : List (V × Bool)) :
    RatProg.ChoiceBound (G.rScan p R pre z flag l D st) (2*l.length) := by
  induction l generalizing D st with
  | nil => exact .ret _ _
  | cons e l ih =>
    unfold rScan
    split_ifs
    · have hc : RatProg.ChoiceBound
          ((pre e).elim (RatProg.weightedEquiv finTwoEquiv
            (fun b => if b then p e else 1-p e) false RatProg.ret) RatProg.ret) 2 := by
        cases pre e with
        | none =>
          simp only [Option.elim_none]
          exact RatProg.ChoiceBound.weightedEquiv finTwoEquiv
            (fun b => if b then p e else 1-p e) false RatProg.ret (N := 0) (fun b => .ret b 0)
        | some b => exact .ret b 2
      have hb := hc.bind (b := 2*l.length) (g := fun o : Bool =>
        if o then G.rScan p R pre z flag l (insert (G.target e) D)
          ((G.target e,flag && decide (G.target e∉R))::st)
        else G.rScan p R pre z flag l D st) (fun b => by cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> exact ih _ _)
      exact hb.mono (by simp only [List.length_cons]; omega)
    · exact (ih D st).mono (by simp only [List.length_cons]; omega)

theorem rDfs_choiceBound (order : List E) (R : Finset V) (pre : E → Option Bool) (v : V)
    (fuel : ℕ) (D : Finset V) (st : List (V × Bool)) :
    RatProg.ChoiceBound (G.rDfs p order R pre v fuel D st) (fuel*(2*order.length)) := by
  induction fuel generalizing D st with
  | zero => exact .ret _ _
  | succ fuel ih =>
    cases st with
    | nil => exact .ret _ _
    | cons zf st =>
      rcases zf with ⟨z,flag⟩
      unfold rDfs
      split_ifs
      · exact .ret _ _
      · exact .ret _ _
      · exact ((G.rScan_choiceBound p R pre z flag order D st).bind fun r => ih r.1 r.2).mono
          (le_of_eq (by ring))

def rationalIterChoices (n m dfsFuel orderLength M : ℕ) : ℕ :=
  (n+1)+((M+1)+((m+1)+dfsFuel*(2*orderLength)))

theorem rIter_choiceBound {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (rank : E → ℕ) (dfsFuel : ℕ) (R : Finset V)
    (qh : V → ℚ) (pools : V → List (Finset V)) (M : ℕ) (v : V) :
    RatProg.ChoiceBound (G.rIter p vertices edges order rank dfsFuel R qh pools M v)
      (rationalIterChoices n m dfsFuel order.length M) := by
  unfold rIter rationalIterChoices
  apply RatProg.ChoiceBound.weightedEquiv
  intro o
  cases o with
  | none => exact .ret _ _
  | some u =>
    apply RatProg.ChoiceBound.weighted
    intro i
    apply RatProg.ChoiceBound.weightedEquiv
    intro j
    cases j with
    | none => exact .ret _ _
    | some j => exact G.rDfs_choiceBound p order R _ v dfsFuel _ _

theorem rGenerate_choiceBound {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (rank : E → ℕ) (dfsFuel : ℕ) (R : Finset V)
    (qh : V → ℚ) (pools : V → List (Finset V)) (M : ℕ) (v : V) (count : ℕ) :
    RatProg.ChoiceBound (G.rGenerate p vertices edges order rank dfsFuel R qh pools M v count)
      (count*rationalIterChoices n m dfsFuel order.length M) := by
  induction count with
  | zero => exact .ret _ _
  | succ count ih =>
    unfold rGenerate
    have h := ih.bind (fun acc => (G.rIter_choiceBound p vertices edges order rank dfsFuel R qh pools M v).bind
      (b := 0) (fun o => RatProg.ChoiceBound.ret (o.elim acc fun D => (acc.1+1,D::acc.2)) 0))
    exact h.mono (by rw [Nat.succ_mul]; omega)

theorem rRounds_choiceBound {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (rank : E → ℕ) (dfsFuel : ℕ) (t : V) (M fuel : ℕ)
    (R : Finset V) (qh : V → ℚ) (pools : V → List (Finset V)) :
    RatProg.ChoiceBound (G.rRounds p vertices edges order rank dfsFuel t M fuel R qh pools)
      (fuel*(M*rationalIterChoices n m dfsFuel order.length M)) := by
  induction fuel generalizing R qh pools with
  | zero => exact .ret _ _
  | succ fuel ih =>
    unfold rRounds
    split_ifs
    · exact .ret _ _
    · generalize ((order.filter fun e => G.source e∈R ∧ G.target e∉R).argmax
          fun e => qh (G.source e)*p e) = o
      cases o with
      | none => exact .ret _ _
      | some e =>
        simp only [Option.elim_some]
        split_ifs
        · exact .ret _ _
        · exact ((G.rGenerate_choiceBound p vertices edges order rank dfsFuel R qh pools M (G.target e) M).bind
            (fun r => ih _ _ _)).mono (le_of_eq (by ring))

theorem rationalAlgS_choiceBound {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (rank : E → ℕ) (s t : V) (M : ℕ) (hlen : order.length=m) :
    RatProg.ChoiceBound (G.rationalAlgS p vertices edges order rank s t M) (algSChoices n m M) := by
  have hn : Fintype.card V=n := by simpa using (Fintype.card_congr vertices).symm
  simpa only [rationalAlgS,hlen,hn,rationalIterChoices,algSChoices,iterChoices] using
    G.rRounds_choiceBound p vertices edges order rank (Fintype.card V+1) t M (Fintype.card V)
      {s} (fun u => if u=s then 1 else 0) (fun u => if u=s then [{s}] else [])

/-- Compiling the actual rational Algorithm S has a bounded rounding error. -/
theorem rationalAlgS_compile_error {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (rank : E → ℕ) (s t : V) (M b : ℕ) (hlen : order.length=m)
    (f : ℝ → ℝ) (hf0 : ∀ x, 0≤f x) (hf1 : ∀ x, f x≤1) :
    |((G.rationalAlgS p vertices edges order rank s t M).compile b).toProg.exp noOracle
      (fun q => f (q : ℝ)) -
      (G.orderedAlgS (fun e => (p e : ℝ)) order rank (Fintype.card V+1)
        (Fintype.card V) s t M).exp noOracle f| ≤ (algSChoices n m M : ℝ)/(2 : ℝ)^b := by
  rw [← G.rationalAlgS_law p vertices edges order rank s t M f]
  exact RatProg.compile_error b (G.rationalAlgS_choiceBound p vertices edges order rank s t M hlen)
    _ (fun q => hf0 q) (fun q => hf1 q)

theorem rationalAlgS_bits {n m : ℕ} (vertices : Fin n ≃ V) (edges : Fin m ≃ E)
    (order : List E) (rank : E → ℕ) (s t : V) (M b : ℕ) (hlen : order.length=m) :
    BitProg.Bits ((G.rationalAlgS p vertices edges order rank s t M).compile b)
      (b*algSChoices n m M) :=
  (G.rationalAlgS_choiceBound p vertices edges order rank s t M hlen).compile b

end
end Digraph
end DirectedCycleFPRAS
