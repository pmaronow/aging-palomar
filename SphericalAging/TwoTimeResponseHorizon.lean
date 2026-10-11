module

public import SphericalAging.TwoTimeResponseParameter

public section

/-! Genuine horizon independence of the physical two-time response.
Restricting its actual strong equation and applying pathwise uniqueness
identifies terminal matrices constructed with different response windows. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.TwoTimeResponseHorizon
open HardSphereDynamics LocalSDE TwoTimePhysicalResponse TwoTimeResponseMatrix
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma physical_response_on_smaller {β : ℝ} {J : FiniteModel.Disorder N p}
    {X : ℝ≥0 → Ω → State N} {D : BrownianDriver N P F} {s S T : ℝ≥0}
    {v : State N} {Y : ℝ≥0 → Ω → State N} (hST : S≤T)
    (hY : IsStrongResponseOn β J X D s v Y T) : IsStrongResponseOn β J X D s v Y S := by
  rcases hY with ⟨hYa,hYc,A,U,hA,hU,hEq⟩
  let G := ShiftedBrownian.filtration F s
  let A' := fun i => FourPapersCommon.FilteredBrownian.predictableTimeRestrict G S (A i)
  let U' := fun i j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict G S (U i j)
  refine ⟨hYa,hYc,A',U',?_,?_,?_⟩
  · intro i
    filter_upwards [hA i,FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn G S (A i)] with q hq hc
    change (A' i : TimeProcessL2 P) q=_
    rw [hc]
    unfold FourPapersCommon.FilteredBrownian.predictableTimeFrame
    by_cases hs : q.1∈Ioc (0 : ℝ≥0) S
    · have ht : q.1∈Ioc (0 : ℝ≥0) T := ⟨hs.1,hs.2.trans hST⟩
      rw [indicator_of_mem (show q∈Ioc (0 : ℝ≥0) S ×ˢ (univ : Set Ω) from ⟨hs,mem_univ _⟩),hq]
      simp only [FourPapersCommon.continuousAdaptedTimeCut,hs,ht,ite_true]
    · rw [indicator_of_notMem (show q∉Ioc (0 : ℝ≥0) S ×ˢ (univ : Set Ω) from fun h => hs h.1)]
      simp only [FourPapersCommon.continuousAdaptedTimeCut,hs,ite_false]
  · intro i j
    filter_upwards [hU i j,FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn G S (U i j)] with q hq hc
    change (U' i j : TimeProcessL2 P) q=_
    rw [hc]
    unfold FourPapersCommon.FilteredBrownian.predictableTimeFrame
    by_cases hs : q.1∈Ioc (0 : ℝ≥0) S
    · have ht : q.1∈Ioc (0 : ℝ≥0) T := ⟨hs.1,hs.2.trans hST⟩
      rw [indicator_of_mem (show q∈Ioc (0 : ℝ≥0) S ×ˢ (univ : Set Ω) from ⟨hs,mem_univ _⟩),hq]
      simp only [FourPapersCommon.continuousAdaptedTimeCut,hs,ht,ite_true]
    · rw [indicator_of_notMem (show q∉Ioc (0 : ℝ≥0) S ×ˢ (univ : Set Ω) from fun h => hs h.1)]
      simp only [FourPapersCommon.continuousAdaptedTimeCut,hs,ite_false]
  · intro t ht i
    have he : (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict (ShiftedBrownian.filtration F s) t (U' i j))=
        fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict (ShiftedBrownian.filtration F s) t (U i j) := by
      funext j
      exact FourPapersCommon.FilteredBrownian.predictableTimeRestrict_restrict G ht _
    rw [he]
    exact hEq t (ht.trans hST) i

theorem terminalResponse_horizon_independent (hN : N≠0) (D : BrownianDriver N P F)
    (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P,Continuous (fun t => X t ω)) (β : ℝ) (J : FiniteModel.Disorder N p)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    {Kb Ks : ℝ≥0} (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
    (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
    (s S T : ℝ≥0) (hST : S≤T) (hSphere : ∀ᵐ ω ∂P,OnSphere (X s ω))
    (hSpherePath : ∀ᵐ ω ∂P,∀ u,u≤s+T → OnSphere (X u ω))
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
    (t : ℝ≥0) (ht : t≤S) :
    terminalResponse hN D X hXa hXc β J R hR hb hs s T hSphere t=
      terminalResponse hN D X hXa hXc β J R hR hb hs s S hSphere t := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  obtain ⟨Y,hY,hterminal⟩ := exists_physical_response hN D X hXa hXc β J R hR hb hs s T hSphere hNR hSpherePath v
  have hsmall := physical_response_on_smaller hST hY
  have hsmallSphere : ∀ᵐ ω ∂P,∀ u,u≤s+S → OnSphere (X u ω) :=
    hSpherePath.mono (fun _ h u hu => h u (hu.trans (add_le_add le_rfl hST)))
  exact (hterminal t).trans (terminalResponse_eq_of_physical hN D X hXa hXc β J R hR hb hs s S
    hSphere hNR hsmallSphere hnull v hsmall t ht).symm

theorem physicalMatrix_horizon_independent (hN : N≠0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (s S T : ℝ≥0) (hST : S≤T) (t : ℝ≥0) (ht : t≤S)
    (q : FiniteModel.Disorder N p × State N) (hx : OnSphere q.2) :
    TwoTimeResponseParameter.physicalMatrix hN D₀ β R hR hNR s T t q hx=
      TwoTimeResponseParameter.physicalMatrix hN D₀ β R hR hNR s S t q hx := by
  let hsol := TwoTimeResponseParameter.globalProcess_physicalSolution hN D₀ β R hR hNR q.1 q.2 hx (s+T)
  let hall := ActualSphereTransition.globalProcess_onSphere hN D₀ β R hR hNR q.1 q.2 hx
  exact terminalResponse_horizon_independent hN (NullAugmentation.driver D₀)
    (HamiltonianJointProcess.globalProcess (NullAugmentation.driver D₀) β R hR q)
    hsol.choose hsol.choose_spec.choose β q.1 R hR hNR
    (HamiltonianPicardDependence.drift_family_lipschitz β R hR (‖q.1‖₊+1) ⟨q.1,by simp⟩)
    (HamiltonianPicardDependence.noise_family_lipschitz N R hR)
    s S T hST (hall.mono (fun _ h => h s)) (hall.mono (fun _ h u _ => h u))
    (fun _ hA hzero => NullAugmentation.augment_null_known_zero F hA hzero) t ht

end SphericalAging.TwoTimeResponseHorizon
