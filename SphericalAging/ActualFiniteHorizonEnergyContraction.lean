module

public import SphericalAging.ActualFiniteHorizonTraceReplacement

public section

/-! Exact integrated ordered covariance contraction for the genuine
annealed physical two-time response matrix. All fields and integrability
are derived from the actual SDE; its rank-one correction has a dimension
vanishing integrated mean bound from column moments. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualFiniteHorizonEnergyContraction
open HardSphereDynamics FiniteModel FiniteCorrelationIto EnergyCovarianceContraction
open TwoTimeResponseParameter TwoTimeResponseTimeParameter ResponseMatrixEnergyContraction
open AnnealedTwoTimeResponseMoments AnnealedResponseMatrixContraction AnnealedResponseTimeMatrix
open ActualFiniteHorizonTraceReplacement
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

private lemma integrated_abs_two {A : Type*} [MeasurableSpace A]
    {ν : Measure A} [IsFiniteMeasure ν] {c : A × Ω → ℝ} {B : ℝ}
    (hc : StronglyMeasurable c) (hm : ∀ s,MemLp (fun ω => c (s,ω)) 2 P)
    (hB : ∀ s,(∫ ω,(c (s,ω))^2 ∂P)≤B) :
    Integrable c (ν.prod P) ∧ (∫ q,|c q| ∂ν.prod P)≤ν.real univ*Real.sqrt B := by
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
  refine ⟨(integrable_norm_iff hc.aestronglyMeasurable).mp (by simpa only [Real.norm_eq_abs] using hi),?_⟩
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ _ : A,Real.sqrt B ∂ν := integral_mono_ae hF (integrable_const _) (.of_forall (fun s => (hs s).2))
    _ = _ := by rw [integral_const];rfl

@[expose] def orderedContraction (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (H : ℝ≥0) (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (q : WaitingTime H × ((Disorder N p × State N) × Ω)) : ℝ :=
  (∑ I : TensorIndex N p,inner ℝ
    (gradient (GaussianIntegrationByParts.hamiltonianCoefficient I) (trajectory D β R hR H q.2))
    (U q (gradient (GaussianIntegrationByParts.hamiltonianCoefficient I) (trajectory D β R hR q.1 q.2))))/(N : ℝ)

@[expose] def errorField (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (H : ℝ≥0) (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (q : WaitingTime H × ((Disorder N p × State N) × Ω)) : ℝ :=
  energyCorrection (p := p) (trajectory D β R hR H q.2) (trajectory D β R hR q.1 q.2) (U q)

theorem exists_actual_integrated_contraction (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0) :
    ∃ U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N),StronglyMeasurable U ∧
      (∀ s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω))) =ᵐ[P]
        sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx)) ∧
      let ν := (waitingMeasure H).prod ((parameterLaw N p).prod P)
      let a := overlapField (NullAugmentation.driver D₀) β R hR H
      let c := orderedContraction (NullAugmentation.driver D₀) β R hR H U
      let e := errorField (NullAugmentation.driver D₀) β R hR H U
      Integrable c ν ∧ Integrable (fun q => (a q)^(p-1)*normalizedTrace (U q)) ν ∧ Integrable e ν ∧
      (∫ q,c q ∂ν)=(p : ℝ)*(∫ q,(a q)^(p-1)*normalizedTrace (U q) ∂ν)+(∫ q,e q ∂ν) ∧
      |(∫ q,c q ∂ν)-(p : ℝ)*(∫ q,(a q)^(p-1)*normalizedTrace (U q) ∂ν)|≤
        (H : ℝ)*Real.sqrt (((p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ))*(1+annealedFourthConstant p β H)) := by
  obtain ⟨U,hU,hUs,hUM⟩ := exists_actual_fixedTerminal_matrix hN hp D₀ β R hR hNR H
  let μ := (parameterLaw N p).prod P
  let ν := (waitingMeasure H).prod μ
  let a := overlapField (p := p) (NullAugmentation.driver D₀) β R hR H
  let r := fun q => normalizedTrace (U q)
  let e := errorField (NullAugmentation.driver D₀) β R hR H U
  have ha : StronglyMeasurable a := overlapField_stronglyMeasurable (NullAugmentation.driver D₀) β R hR H
  have hr : StronglyMeasurable r := by
    have hc : Continuous (normalizedTrace : (State N →L[ℝ] State N) → ℝ) := by
      unfold normalizedTrace HamiltonianDerivativeCovariance.operatorTrace
      simp_rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin N) ℝ)]
      change Continuous (fun U : State N →L[ℝ] State N =>
        (∑ i : Fin N,inner ℝ (EuclideanSpace.basisFun (Fin N) ℝ i) (U (EuclideanSpace.basisFun (Fin N) ℝ i)))/(N : ℝ))
      fun_prop
    exact hc.comp_stronglyMeasurable hU
  have htr₂ s := ResponseTraceReplacement.fourthMoment_to_secondMoment (hUM s).1 (hUM s).2.1
  have hri := integrated_abs_two (P := μ) (ν := waitingMeasure H) hr (fun s => (htr₂ s).1) (fun s => (htr₂ s).2)
  have hab : ∀ᵐ q ∂ν,|a q|≤1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le ha.norm.measurable measurable_const)).mpr
    exact .of_forall (fun s => by
      filter_upwards [trajectory_onSphere hN D₀ β R hR hNR H,trajectory_onSphere hN D₀ β R hR hNR s] with q hx hy
      exact overlap_abs_le_one hN hx hy)
  have hwi : Integrable (fun q => (a q)^(p-1)*r q) ν :=
    hri.1.norm.mono' ((ha.pow (p-1)).mul hr).aestronglyMeasurable (hab.mono (fun q hq => by
      rw [Real.norm_eq_abs,abs_mul,abs_pow]
      exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hq)))
  have hX : StronglyMeasurable (fun q : WaitingTime H × ((Disorder N p × State N) × Ω) =>
      trajectory (NullAugmentation.driver D₀) β R hR H q.2) :=
    (trajectory_stronglyMeasurable (NullAugmentation.driver D₀) β R hR H).comp_snd
  have hY := waitingTrajectory_stronglyMeasurable (p := p) (NullAugmentation.driver D₀) β R hR H
  have hUX : StronglyMeasurable (fun q => U q (trajectory (NullAugmentation.driver D₀) β R hR H q.2)) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hU.prodMk hX)
  have he : StronglyMeasurable e := by
    have hh := ((ha.pow (p-2)).mul (hY.inner hUX)).const_mul ((p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2)
    convert hh using 1
    funext q
    simp only [e,errorField,energyCorrection,Pi.mul_apply,Pi.pow_apply,a,overlapField]
    ring
  have hei := integrated_abs_two (P := μ) (ν := waitingMeasure H) he
    (fun s => (hUM s).2.2.1) (fun s => (hUM s).2.2.2)
  have hsplit : orderedContraction (NullAugmentation.driver D₀) β R hR H U=
      fun q => (p : ℝ)*(a q)^(p-1)*r q+e q := by
    funext q
    exact normalized_contraction_eq hN hp _ _ _
  have hci : Integrable (orderedContraction (NullAugmentation.driver D₀) β R hR H U) ν := by
    rw [hsplit]
    convert (hwi.const_mul (p : ℝ)).add hei.1 using 1
    funext q
    simp only [Pi.add_apply]
    ring
  have hid : (∫ q,orderedContraction (NullAugmentation.driver D₀) β R hR H U q ∂ν)=
      (p : ℝ)*(∫ q,(a q)^(p-1)*r q ∂ν)+(∫ q,e q ∂ν) := by
    rw [hsplit]
    have heq : (fun q => (p : ℝ)*(a q)^(p-1)*r q+e q)=fun q => (p : ℝ)*((a q)^(p-1)*r q)+e q := by
      funext q
      ring
    rw [heq,integral_add (hwi.const_mul (p : ℝ)) hei.1,integral_const_mul]
  refine ⟨U,hU,hUs,hci,hwi,hei.1,hid,?_⟩
  rw [hid,add_sub_cancel_left]
  exact abs_integral_le_integral_abs.trans (by simpa only [waitingMeasure_real_univ] using hei.2)

end SphericalAging.ActualFiniteHorizonEnergyContraction
