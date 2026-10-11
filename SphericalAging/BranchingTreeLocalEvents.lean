module

public import SphericalAging.BranchingNodeLaw

public section

/-! A genuine finite-tree union bound under the product branching law.
Shared ancestry is handled by the proved child state/subtree marginal law;
no independence among local node events is assumed. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.BranchingTreeLocalEvents
open Set MeasureTheory IndependentBranchingSuccess BranchingNodeLaw
open scoped BigOperators
variable {S G : Type} [MeasurableSpace S] [MeasurableSpace G] {K : ℕ}

@[expose] def AllGood (update : ℕ→S→G→S) (B : ℕ→Set (S×(Fin K→G))) :
    (d : ℕ)→Set (S×TreeSample G K d)
  | 0 => Set.univ
  | d+1 => {z | (z.1,childNoises d z.2)∈B d ∧
      ∀i,childSampler update d i z∈AllGood update B d}

@[expose] def failureBudget (K : ℕ) (b : ℕ→ℝ) : ℕ→ℝ
  | 0 => 0
  | d+1 => b d+(K:ℝ)*failureBudget K b d

theorem AllGood_measurable (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure G) [IsProbabilityMeasure ν] (update : ℕ→S→G→S)
    (hu : ∀d,MeasurePreserving (Function.uncurry (update d)) (μ.prod ν) μ)
    (B : ℕ→Set (S×(Fin K→G))) (hB : ∀d,MeasurableSet (B d)) (d : ℕ) :
    MeasurableSet (AllGood update B d) := by
  induction d with
  | zero => exact MeasurableSet.univ
  | succ d ih =>
    have hl : Measurable (fun z : S×TreeSample G K (d+1) => (z.1,childNoises d z.2)) :=
      ((MeasurePreserving.id μ).prod (childNoises_measurePreserving ν K d)).measurable
    have hf : MeasurableSet {z | ∀i,childSampler update d i z∈AllGood update B d} := by
      have heq : {z | ∀i,childSampler update d i z∈AllGood update B d}=
          ⋂i,{z | childSampler update d i z∈AllGood update B d} := by ext z;simp
      rw [heq]
      exact MeasurableSet.iInter (fun i => ih.preimage
        (childSampler_measurePreserving μ ν update hu d i).measurable)
    exact ((hB d).preimage hl).inter hf

theorem actual_tree_failure_bound (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure G) [IsProbabilityMeasure ν] (update : ℕ→S→G→S)
    (hu : ∀d,MeasurePreserving (Function.uncurry (update d)) (μ.prod ν) μ)
    (B : ℕ→Set (S×(Fin K→G))) (hB : ∀d,MeasurableSet (B d)) (d : ℕ) :
    (μ.prod (treeLaw ν K d)).real (AllGood update B d)ᶜ≤
      failureBudget K (fun j => (μ.prod (Measure.pi (fun _ : Fin K => ν))).real (B j)ᶜ) d := by
  induction d with
  | zero => simp [AllGood,failureBudget]
  | succ d ih =>
    let P := μ.prod (treeLaw ν K (d+1))
    let E := {z : S×TreeSample G K (d+1) | (z.1,childNoises d z.2)∉B d}
    let F := fun i : Fin K => {z : S×TreeSample G K (d+1) | childSampler update d i z∉AllGood update B d}
    have hsub : (AllGood update B (d+1))ᶜ⊆E∪⋃i,F i := by
      intro z hz
      change ¬((z.1,childNoises d z.2)∈B d ∧ ∀i,childSampler update d i z∈AllGood update B d) at hz
      rcases (not_and_or.mp hz) with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa only [mem_iUnion,F,mem_setOf_eq,not_forall] using h)
    have hl := ((MeasurePreserving.id μ).prod (childNoises_measurePreserving ν K d)).hasLaw.measureReal_eq
      (hB d).compl
    have hc i := (childSampler_measurePreserving μ ν update hu d i).hasLaw.measureReal_eq
      (AllGood_measurable μ ν update hu B hB d).compl
    change P.real E=(μ.prod (Measure.pi (fun _ : Fin K => ν))).real (B d)ᶜ at hl
    change ∀i,P.real (F i)=(μ.prod (treeLaw ν K d)).real (AllGood update B d)ᶜ at hc
    change P.real (AllGood update B (d+1))ᶜ≤_
    calc
      _≤P.real E+∑i : Fin K,P.real (F i) :=
        (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
          (add_le_add le_rfl (measureReal_iUnion_fintype_le _)))
      _=(μ.prod (Measure.pi (fun _ : Fin K => ν))).real (B d)ᶜ+
          (K:ℝ)*(μ.prod (treeLaw ν K d)).real (AllGood update B d)ᶜ := by
        rw [hl]
        simp_rw [hc]
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      _≤_ := add_le_add le_rfl (mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg K))

theorem failureBudget_mono (b c : ℕ→ℝ) (h : ∀j,b j≤c j) (d : ℕ) :
    failureBudget K b d≤failureBudget K c d := by
  induction d with
  | zero => exact le_rfl
  | succ d ih => exact add_le_add (h d) (mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg K))

theorem actual_tree_success_bound (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure G) [IsProbabilityMeasure ν] (update : ℕ→S→G→S)
    (hu : ∀d,MeasurePreserving (Function.uncurry (update d)) (μ.prod ν) μ)
    (B : ℕ→Set (S×(Fin K→G))) (hB : ∀d,MeasurableSet (B d)) (d : ℕ) :
    1-failureBudget K (fun j => (μ.prod (Measure.pi (fun _ : Fin K => ν))).real (B j)ᶜ) d≤
      (μ.prod (treeLaw ν K d)).real (AllGood update B d) := by
  have hb := actual_tree_failure_bound μ ν update hu B hB d
  have hsum := measureReal_add_measureReal_compl (μ:=μ.prod (treeLaw ν K d))
    (AllGood_measurable μ ν update hu B hB d)
  rw [probReal_univ] at hsum
  linarith

end SphericalAging.BranchingTreeLocalEvents
