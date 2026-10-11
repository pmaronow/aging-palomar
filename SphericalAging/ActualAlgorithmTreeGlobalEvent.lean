module

public import SphericalAging.ActualAlgorithmTreeOverlap

public section

/-! A true simultaneous global overlap event for the literal algorithm
output tree, with an explicit finite union concentration budget. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualAlgorithmTreeGlobalEvent
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open ActualAlgorithmTree ActualAlgorithmTreeOverlap GaussianTreePathState
open IndependentBranchingSuccess GaussianBranchingSuccess PartialVarianceBranchingCoefficients
open AlgorithmicOverlapConcentration AlgorithmicCorrelationContinuity
open RegularTreeGlobalToLocal RegularTreeGlobalPathSpecification
open scoped InnerProductSpace NNReal BigOperators
variable {N p K : ℕ}

@[expose] abbrev Paths (K d : ℕ) := Fin d→Fin K
@[expose] abbrev CrossIndex (K d : ℕ) := Paths K d×Paths K d×Fin d

@[expose] def selfBad (A : TensorSpace N p→Vector N) (V : ℕ→ℝ) (d : ℕ) (ε : ℝ)
    (a : Paths K d) : Set (TensorSpace N p×TreeSample (TensorSpace N p) K d) :=
  {z | ε≤|‖terminalOutput A (update (parentCoefficient V) (freshCoefficient V)) d a z‖^2/(N:ℝ)-correlation A 1|}

@[expose] def crossBad (A : TensorSpace N p→Vector N) (V : ℕ→ℝ) (d : ℕ) (ε : ℝ)
    (t : CrossIndex K d) : Set (TensorSpace N p×TreeSample (TensorSpace N p) K d) :=
  if t.1 t.2.2≠t.2.1 t.2.2 ∧ (∀i : Fin d,i<t.2.2→t.1 i=t.2.1 i) then
    {z | ε≤|pairOverlap A
      (terminalState (update (parentCoefficient V) (freshCoefficient V)) d t.1 z,
        terminalState (update (parentCoefficient V) (freshCoefficient V)) d t.2.1 z)-correlation A (V (d-t.2.2.val))|}
  else ∅

@[expose] def goodEvent (A : TensorSpace N p→Vector N) (V : ℕ→ℝ) (d : ℕ) (ε : ℝ) :
    Set (TensorSpace N p×TreeSample (TensorSpace N p) K d) :=
  ((⋃a : Paths K d,selfBad A V d ε a)∪(⋃t : CrossIndex K d,crossBad A V d ε t))ᶜ

@[expose] def unionBudget (K d : ℕ) (b : ℝ) : ℝ :=
  ((Fintype.card (Paths K d):ℕ)+(Fintype.card (CrossIndex K d):ℕ):ℝ)*b

theorem selfBad_measurable (A : TensorSpace N p→Vector N) (hA : Measurable A)
    (V : ℕ→ℝ) (d : ℕ) (ε : ℝ) (a : Paths K d) :
    MeasurableSet (selfBad A V d ε a) := by
  have hm := terminalOutput_measurable A hA (update (parentCoefficient V) (freshCoefficient V))
    (update_measurable _ _) d a
  exact measurableSet_le measurable_const (continuous_abs.measurable.comp (((hm.norm.pow_const 2).div_const (N:ℝ)).sub_const _))

theorem crossBad_measurable (A : TensorSpace N p→Vector N) (hA : Continuous A)
    (V : ℕ→ℝ) (d : ℕ) (ε : ℝ) (t : CrossIndex K d) :
    MeasurableSet (crossBad A V d ε t) := by
  classical
  unfold crossBad
  split_ifs
  · have hm : Measurable (fun z : TensorSpace N p×TreeSample (TensorSpace N p) K d => pairOverlap A
        (terminalState (update (parentCoefficient V) (freshCoefficient V)) d t.1 z,
          terminalState (update (parentCoefficient V) (freshCoefficient V)) d t.2.1 z)) :=
      (pairOverlap_continuous A hA).measurable.comp
        ((terminalState_measurable _ (update_measurable _ _) d t.1).prodMk
          (terminalState_measurable _ (update_measurable _ _) d t.2.1))
    exact measurableSet_le measurable_const (continuous_abs.measurable.comp (hm.sub_const _))
  · exact MeasurableSet.empty

theorem goodEvent_measurable (A : TensorSpace N p→Vector N) (hA : Continuous A)
    (V : ℕ→ℝ) (d : ℕ) (ε : ℝ) : MeasurableSet (goodEvent (K:=K) A V d ε) :=
  ((MeasurableSet.iUnion (selfBad_measurable A hA.measurable V d ε)).union
    (MeasurableSet.iUnion (crossBad_measurable A hA V d ε))).compl

theorem actual_global_overlap_event (hN : 0<N) (V : ℕ→ℝ)
    (hV : ∀j,0≤V j) (hVm : ∀j,V (j+1)≤V j) (hV0 : V 0=1) (hV1 : ∀j,V j≤1)
    {L : ℝ≥0} (A : TensorSpace N p→Vector N) (hA : LipschitzWith L A)
    (hball : ∀s,‖A s‖≤Real.sqrt N) (d : ℕ) (q : ℕ→ℝ)
    (hqd : q d=correlation A 1) (hq : ∀j : Fin d,q j.val=correlation A (V (d-j.val)))
    (ε : ℝ) (hε : 0≤ε) :
    MeasurableSet (goodEvent (K:=K) A V d ε) ∧
    1-unionBudget K d (2*Real.exp (-ε^2/(2*(overlapConstant N L:ℝ))))≤
      ((stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K d)).real
        (goodEvent (K:=K) A V d ε) ∧
    ∀z∈goodEvent (K:=K) A V d ε,
      GlobalOverlapTree q ε d (outputTree A (update (parentCoefficient V) (freshCoefficient V)) d z.1 z.2) := by
  classical
  let μ := (stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K d)
  let b := 2*Real.exp (-ε^2/(2*(overlapConstant N L:ℝ)))
  have hself (a : Paths K d) : μ.real (selfBad A V d ε a)≤b :=
    actual_terminal_self_overlap_tail hN V hV hVm A hA hball d a ε hε
  have hcross (t : CrossIndex K d) : μ.real (crossBad A V d ε t)≤b := by
    unfold crossBad
    split_ifs with ht
    · exact actual_terminal_cross_overlap_tail hN V hV hVm hV0 hV1 A hA hball d t.1 t.2.1 t.2.2 ht.1 ht.2 ε hε
    · simp only [measureReal_empty]
      positivity
  have hbad : μ.real (goodEvent (K:=K) A V d ε)ᶜ≤unionBudget K d b := by
    simp only [goodEvent,compl_compl]
    apply (measureReal_union_le _ _).trans
    have hs := (measureReal_iUnion_fintype_le (μ:=μ) (selfBad A V d ε)).trans
      (Finset.sum_le_sum (fun a _ => hself a))
    have hc := (measureReal_iUnion_fintype_le (μ:=μ) (crossBad A V d ε)).trans
      (Finset.sum_le_sum (fun t _ => hcross t))
    simpa [unionBudget,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,add_mul,Nat.cast_add] using add_le_add hs hc
  have hm := goodEvent_measurable (K:=K) A hA.continuous V d ε
  refine ⟨hm,?_,?_⟩
  · have hh := measureReal_add_measureReal_compl (μ:=μ) hm
    simp only [probReal_univ] at hh
    change 1-unionBudget K d b≤μ.real (goodEvent (K:=K) A V d ε)
    linarith
  · intro z hz
    apply globalOverlapTree_of_paths
    · intro a
      rw [leafAt_outputTree]
      rw [terminalOutput_eq_state]
      exact hball _
    · intro a
      have hn : z∉selfBad A V d ε a := fun hh => hz (Or.inl (mem_iUnion.mpr ⟨a,hh⟩))
      have hs : |‖terminalOutput A (update (parentCoefficient V) (freshCoefficient V)) d a z‖^2/(N:ℝ)-correlation A 1|≤ε :=
        (lt_of_not_ge hn).le
      rw [leafAt_outputTree,hqd,CentroidOverlapEstimates.overlap,real_inner_self_eq_norm_sq]
      exact hs
    · intro a b j hab hbefore
      have hn : z∉crossBad A V d ε (a,b,j) := fun hh => hz (Or.inr (mem_iUnion.mpr ⟨(a,b,j),hh⟩))
      have ht : a j≠b j ∧ (∀i : Fin d,i<j→a i=b i) := ⟨hab,hbefore⟩
      simp only [crossBad,if_pos ht] at hn
      have hs : |pairOverlap A
          (terminalState (update (parentCoefficient V) (freshCoefficient V)) d a z,
            terminalState (update (parentCoefficient V) (freshCoefficient V)) d b z)-correlation A (V (d-j.val))|≤ε :=
        (lt_of_not_ge hn).le
      rw [leafAt_outputTree,leafAt_outputTree,hq j]
      simpa only [CentroidOverlapEstimates.overlap,pairOverlap,terminalOutput_eq_state,Function.comp_def] using hs

end SphericalAging.ActualAlgorithmTreeGlobalEvent
