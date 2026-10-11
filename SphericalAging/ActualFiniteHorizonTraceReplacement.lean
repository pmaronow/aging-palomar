module

public import SphericalAging.AnnealedResponseTimeMatrix
public import SphericalAging.FiniteHorizonTraceReplacement

public section

/-! Finite-horizon integration of the actual annealed two-time response
trace. The physical matrix and all joint measurability and moment bounds
are derived. Only the overlap concentration error is an input. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualFiniteHorizonTraceReplacement
open HardSphereDynamics FiniteModel FiniteCorrelationIto EnergyCovarianceContraction
open TwoTimeResponseParameter TwoTimeResponseTimeParameter ResponseMatrixEnergyContraction
open AnnealedTwoTimeResponseMoments AnnealedResponseMatrixContraction AnnealedResponseTimeMatrix
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def waitingMeasure (H : ℝ≥0) : Measure (WaitingTime H) :=
  (nonnegativeLebesgueMeasure.restrict (Ioc (0 : ℝ≥0) H)).comap Subtype.val

lemma waitingMeasure_univ (H : ℝ≥0) : waitingMeasure H univ=ENNReal.ofReal (H : ℝ) := by
  rw [waitingMeasure,comap_subtype_coe_apply measurableSet_Icc,Subtype.coe_image_univ,
    Measure.restrict_apply measurableSet_Icc,inter_eq_right.mpr Ioc_subset_Icc_self,nonnegativeLebesgueMeasure_Ioc]
  simp only [NNReal.coe_zero,sub_zero]

instance waitingMeasure_finite (H : ℝ≥0) : IsFiniteMeasure (waitingMeasure H) where
  measure_univ_lt_top := by rw [waitingMeasure_univ];exact ENNReal.ofReal_lt_top

lemma waitingMeasure_real_univ (H : ℝ≥0) : (waitingMeasure H).real univ=(H : ℝ) := by
  rw [Measure.real_def,waitingMeasure_univ,ENNReal.toReal_ofReal H.coe_nonneg]

@[expose] def overlapField (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (H : ℝ≥0) (q : WaitingTime H × ((Disorder N p × State N) × Ω)) : ℝ :=
  overlap (trajectory D β R hR H q.2) (trajectory D β R hR q.1 q.2)

lemma waitingTrajectory_stronglyMeasurable (D : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (H : ℝ≥0) :
    StronglyMeasurable (fun q : WaitingTime H × ((Disorder N p × State N) × Ω) =>
      trajectory D β R hR q.1 q.2) := by
  exact (ActualSphereTransition.jointProcess_measurable D β R hR).comp_measurable
    ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_subtype_coe.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)))

lemma overlapField_stronglyMeasurable (D : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (H : ℝ≥0) :
    StronglyMeasurable (overlapField (p := p) D β R hR H) := by
  have h := ((trajectory_stronglyMeasurable (p := p) D β R hR H).comp_snd.inner
    (waitingTrajectory_stronglyMeasurable D β R hR H)).mul_const (N : ℝ)⁻¹
  convert h using 1
  funext q
  simp only [overlapField,overlap,div_eq_mul_inv]

private lemma integrated_abs_of_secondMoment {A : Type*} [MeasurableSpace A]
    {ν : Measure A} [IsFiniteMeasure ν] {c : A × Ω → ℝ} {B : ℝ}
    (hc : StronglyMeasurable c) (hm : ∀ s,MemLp (fun ω => c (s,ω)) 2 P)
    (hB : ∀ s,(∫ ω,(c (s,ω))^2 ∂P)≤B) :
    Integrable (fun q => |c q|) (ν.prod P) ∧
      (∫ q,|c q| ∂ν.prod P)≤ν.real univ*Real.sqrt B := by
  have hs (s : A) : Integrable (fun ω => |c (s,ω)|) P ∧ (∫ ω,|c (s,ω)| ∂P)≤Real.sqrt B := by
    refine ⟨?_,(integral_abs_le_sqrt_secondMoment (hm s)).trans (Real.sqrt_le_sqrt (hB s))⟩
    simpa only [Real.norm_eq_abs] using ((hm s).integrable (by norm_num)).norm
  have hf : StronglyMeasurable (fun q => |c q|) := by simpa only [Real.norm_eq_abs] using hc.norm
  have hF : Integrable (fun s => ∫ ω,|c (s,ω)| ∂P) ν :=
    (integrable_const (Real.sqrt B)).mono' hf.integral_prod_right'.aestronglyMeasurable
      (.of_forall (fun s => by
        rw [Real.norm_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))]
        exact (hs s).2))
  have hi : Integrable (fun q => |c q|) (ν.prod P) := by
    apply (integrable_prod_iff hf.aestronglyMeasurable).mpr
    refine ⟨.of_forall (fun s => (hs s).1),?_⟩
    simpa only [Real.norm_eq_abs,abs_abs] using hF
  refine ⟨hi,?_⟩
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ _ : A,Real.sqrt B ∂ν := integral_mono_ae hF (integrable_const _) (.of_forall (fun s => (hs s).2))
    _ = _ := by rw [integral_const];rfl

/-- Actual finite-horizon rank-one energy correction. Its integrated
mean absolute size vanishes as N tends to infinity using only the
derived physical column moments. -/
theorem exists_actual_integrated_energy_error (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0) :
    ∃ U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N),StronglyMeasurable U ∧
      (∀ s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω))) =ᵐ[P]
        sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx)) ∧
      Integrable (fun q => |energyCorrection (p := p)
        (trajectory (NullAugmentation.driver D₀) β R hR H q.2)
        (trajectory (NullAugmentation.driver D₀) β R hR q.1 q.2) (U q)|)
          ((waitingMeasure H).prod ((parameterLaw N p).prod P)) ∧
      (∫ q,|energyCorrection (p := p)
        (trajectory (NullAugmentation.driver D₀) β R hR H q.2)
        (trajectory (NullAugmentation.driver D₀) β R hR q.1 q.2) (U q)|
          ∂(waitingMeasure H).prod ((parameterLaw N p).prod P))≤
        (H : ℝ)*Real.sqrt (((p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ))*(1+annealedFourthConstant p β H)) := by
  obtain ⟨U,hU,hUs,hUM⟩ := exists_actual_fixedTerminal_matrix hN hp D₀ β R hR hNR H
  have hX : StronglyMeasurable (fun q : WaitingTime H × ((Disorder N p × State N) × Ω) =>
      trajectory (NullAugmentation.driver D₀) β R hR H q.2) :=
    (trajectory_stronglyMeasurable (NullAugmentation.driver D₀) β R hR H).comp_snd
  have hY := waitingTrajectory_stronglyMeasurable (p := p) (NullAugmentation.driver D₀) β R hR H
  have hUX : StronglyMeasurable (fun q => U q (trajectory (NullAugmentation.driver D₀) β R hR H q.2)) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hU.prodMk hX)
  have hc : StronglyMeasurable (fun q => energyCorrection (p := p)
      (trajectory (NullAugmentation.driver D₀) β R hR H q.2)
      (trajectory (NullAugmentation.driver D₀) β R hR q.1 q.2) (U q)) := by
    have hh := (((overlapField_stronglyMeasurable (NullAugmentation.driver D₀) β R hR H).pow (p-2)).mul
      (hY.inner hUX)).const_mul ((p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2)
    convert hh using 1
    funext q
    simp only [energyCorrection,Pi.mul_apply,Pi.pow_apply,overlapField]
    ring
  have hh := integrated_abs_of_secondMoment (P := (parameterLaw N p).prod P) (ν := waitingMeasure H) hc
    (fun s => (hUM s).2.2.1) (fun s => (hUM s).2.2.2)
  refine ⟨U,hU,hUs,hh.1,?_⟩
  simpa only [waitingMeasure_real_univ] using hh.2

/-- The actual signed trace replacement is integrable over the full
finite horizon and annealed law. All response field regularity and L⁴
estimates are conclusions of the genuine physical SDE construction. -/
theorem exists_actual_integrated_trace_replacement (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0) (n : ℕ)
    (b : WaitingTime H → ℝ) (hb : StronglyMeasurable b) (hbb : ∀ s,|b s|≤1)
    (ε : ℝ) (hε : 0≤ε)
    (hvariance : ∀ s,(∫ q,(overlapField (NullAugmentation.driver D₀) β R hR H (s,q)-b s)^2
      ∂(parameterLaw N p).prod P)≤ε^2) :
    ∃ U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N),StronglyMeasurable U ∧
      (∀ s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω))) =ᵐ[P]
        sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx)) ∧
      Integrable (fun q => |((overlapField (NullAugmentation.driver D₀) β R hR H q)^n-(b q.1)^n)*
        normalizedTrace (U q)|) ((waitingMeasure H).prod ((parameterLaw N p).prod P)) ∧
      (∫ q,|((overlapField (NullAugmentation.driver D₀) β R hR H q)^n-(b q.1)^n)*normalizedTrace (U q)|
        ∂(waitingMeasure H).prod ((parameterLaw N p).prod P))≤
          (H : ℝ)*((n : ℝ)*ε*Real.sqrt (1+annealedFourthConstant p β H)) := by
  obtain ⟨U,hU,hUs,hUM⟩ := exists_actual_fixedTerminal_matrix hN hp D₀ β R hR hNR H
  have htrace : StronglyMeasurable (fun q => normalizedTrace (U q)) := by
    have hc : Continuous (normalizedTrace : (State N →L[ℝ] State N) → ℝ) := by
      unfold normalizedTrace HamiltonianDerivativeCovariance.operatorTrace
      simp_rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin N) ℝ)]
      change Continuous (fun U : State N →L[ℝ] State N =>
        (∑ i : Fin N,inner ℝ (EuclideanSpace.basisFun (Fin N) ℝ i) (U (EuclideanSpace.basisFun (Fin N) ℝ i)))/(N : ℝ))
      fun_prop
    exact hc.comp_stronglyMeasurable hU
  have hab : ∀ s,∀ᵐ q ∂(parameterLaw N p).prod P,
      |overlapField (NullAugmentation.driver D₀) β R hR H (s,q)|≤1 := by
    intro s
    filter_upwards [trajectory_onSphere hN D₀ β R hR hNR H,trajectory_onSphere hN D₀ β R hR hNR s] with q hx hy
    exact overlap_abs_le_one hN hx hy
  have hh := FiniteHorizonTraceReplacement.integrated_weighted_trace_replacement (ν := waitingMeasure H) n hε
    (overlapField_stronglyMeasurable (NullAugmentation.driver D₀) β R hR H) htrace hb hab hbb
    (fun s => (hUM s).1) (fun s => (hUM s).2.1) hvariance
  refine ⟨U,hU,hUs,hh.1,?_⟩
  simpa only [waitingMeasure_real_univ] using hh.2

end SphericalAging.ActualFiniteHorizonTraceReplacement
