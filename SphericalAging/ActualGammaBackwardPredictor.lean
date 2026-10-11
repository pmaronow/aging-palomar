module

public import SphericalAging.BrownianFutureConditionalIntegral
public import SphericalAging.ActualGammaFutureAnnealed
public import SphericalAging.HamiltonianTerminalSpatialC2

public section

/-! The genuine backward conditional predictor of the two-time Brownian
pairing. The observation at the earlier time and the state are retained
jointly; only the actual future increment path is independent. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualGammaBackwardPredictor
open FiniteModel HardSphereDynamics ActualSphereTransition AnnealedSDECore
open ActualGammaFutureInnovation ActualGammaFutureAnnealed ActualBackgroundGammaLaw
open ActualDisorderGammaVariance ActualSphereGammaVariance BrownianVectorMoments
open ActualSphereLinearTransition BrownianFuturePath BrownianFutureFiltered
open BrownianFutureConditionalIntegral
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem gammaMean_initial_contDiff_two (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : Disorder N p) (T t s : ℝ≥0) (hT : 0<T) :
    ContDiff ℝ 2 (fun x : State N => gammaMean β R hR x T t s J) := by
  have hh := (innerSL ℝ (brownianClass (N:=N) s)).contDiff.comp
    (HamiltonianTerminalSpatialC2.stateClass_contDiff_two (VectorBrownian.driver N) β J R hR T t hT)
  simpa only [gammaMean,ActualSphereOverlapDerivative.terminal_classes_eq,Function.comp_def,innerSL_apply_apply] using hh.div_const (Real.sqrt 2*(N : ℝ))

lemma brownianVector_future (r u : ℝ≥0) (ω : VectorBrownian.Space N) :
    brownianVector u (future r ω)=brownianVector (r+u) ω-brownianVector r ω := by
  ext i
  rfl

@[expose] def predictor (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p)
    (T t s r : ℝ≥0) (x b : State N) : ℝ :=
  ⟪b,mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-r) x⟫_ℝ/
    (Real.sqrt 2*(N : ℝ))+gammaMean β R hR x T (t-r) (s-r) J

/-- Genuine conditional expectation of the original two-time pairing at
every time before its Brownian observation, with no conditional-law input. -/
theorem gamma_eq_condExp_predictor (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    {Z0 : VectorBrownian.Space N → State N}
    (X : ℝ≥0 → VectorBrownian.Space N → State N)
    (hX : ∀ T,IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X T)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ u,OnSphere (X u ω))
    (T t s r : ℝ≥0) (ht : t≤T) (hst : s≤t) (hrs : r≤s) :
    (VectorBrownian.law N)[(fun ω => ⟪brownianVector s ω,X t ω⟫_ℝ/(Real.sqrt 2*(N : ℝ))) |
      NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N) r]
      =ᵐ[VectorBrownian.law N] fun ω => predictor β R hR J T t s r (X r ω) (brownianVector r ω) := by
  let P := VectorBrownian.law N
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let F := NullAugmentation.augment (VectorBrownian.filtration N) P
  let Z : VectorBrownian.Space N → State N×State N := fun ω => (X r ω,brownianVector r ω)
  have hZa : Measurable[F r] Z := ((hX 0).2.1 r).measurable.prodMk (brownianVector_waiting_measurable r)
  have hZm : Measurable Z := hZa.mono (F.le r) le_rfl
  let μ := P.map Z
  letI : IsProbabilityMeasure μ :=
    (hasLaw_map hZm.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  have hZmap : MeasurePreserving Z P μ := ⟨hZm,rfl⟩
  have hμs : ∀ᵐ z ∂μ,OnSphere z.1 :=
    (ae_map_iff hZm.aemeasurable (ActualSphereKernelSupport.measurableSet_onSphere.preimage measurable_fst)).mpr
      (hSphere.mono (fun _ h => h r))
  have hBi : Integrable (fun z : State N×State N => ‖z.2‖) μ :=
    (hZmap.integrable_comp (by fun_prop : AEStronglyMeasurable (fun z : State N×State N => ‖z.2‖) μ)).mp
      (((brownianVector_memLp (N:=N) r (q:=2) (by norm_num)).norm).integrable (by norm_num))
  let Y : (State N×State N)×VectorBrownian.Space N → State N := fun q => jointProcess D β R hR (J,q.1.1) (t-r) q.2
  let G : (State N×State N)×VectorBrownian.Space N → ℝ := fun q =>
    ⟪q.1.2+brownianVector (s-r) q.2,Y q⟫_ℝ/(Real.sqrt 2*(N : ℝ))
  have hY : StronglyMeasurable Y := (jointProcess_measurable D β R hR).comp_measurable
    ((measurable_const.prodMk (measurable_fst.comp measurable_fst)).prodMk (measurable_const.prodMk measurable_snd))
  have hBsm : StronglyMeasurable (brownianVector (N:=N) (s-r)) := by
    exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)).symm.continuous.measurable.comp
      (measurable_pi_iff.mpr (fun i => VectorBrownian.coordinate_measurable i (s-r)))).stronglyMeasurable
  have hG : StronglyMeasurable G :=
    (continuous_id.div_const (Real.sqrt 2*(N : ℝ))).comp_stronglyMeasurable
      (((measurable_snd.comp measurable_fst).stronglyMeasurable.add
        (hBsm.comp_measurable measurable_snd)).inner (𝕜:=ℝ) hY)
  have hsp : ∀ᵐ q ∂μ.prod P,OnSphere (Y q) := by
    have hm : MeasurableSet {q : (State N×State N)×VectorBrownian.Space N | OnSphere (Y q)} :=
      ActualSphereKernelSupport.measurableSet_onSphere.preimage hY.measurable
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    filter_upwards [hμs] with z hz
    exact (jointProcess_onSphere (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR J z.1 hz).mono
      (fun _ h => h (t-r))
  let C : ℝ := Real.sqrt N/(Real.sqrt 2*(N : ℝ))
  have hDom : Integrable (fun q : (State N×State N)×VectorBrownian.Space N =>
      C*(‖q.1.2‖+‖brownianVector (s-r) q.2‖)) (μ.prod P) :=
    ((hBi.comp_fst P).add
      (((brownianVector_memLp (N:=N) (s-r) (q:=2) (by norm_num)).norm.integrable (by norm_num)).comp_snd μ)).const_mul C
  have hGi : Integrable G (μ.prod P) := by
    apply hDom.mono' hG.aestronglyMeasurable
    filter_upwards [hsp] with q hq
    have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
    have hd : 0<Real.sqrt 2*(N : ℝ) := by positivity
    have hy : ‖Y q‖=Real.sqrt N := by
      calc
        _=Real.sqrt (‖Y q‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _=_ := congrArg Real.sqrt ((onSphere_iff_norm_sq _).mp hq)
    change ‖⟪q.1.2+brownianVector (s-r) q.2,Y q⟫_ℝ/(Real.sqrt 2*(N : ℝ))‖≤_
    rw [norm_div,Real.norm_of_nonneg hd.le]
    calc
      _≤((‖q.1.2‖+‖brownianVector (s-r) q.2‖)*Real.sqrt N)/(Real.sqrt 2*(N : ℝ)) := by
        apply div_le_div_of_nonneg_right _ hd.le
        exact (norm_inner_le_norm (𝕜:=ℝ) _ _).trans (by rw [hy];gcongr;exact norm_add_le _ _)
      _=_ := by dsimp only [C];ring
  have hrst : r≤t := hrs.trans hst
  have hfuture := ActualSphereMarkovRestart.actual_future_eq_joint (Nat.ne_of_gt hN) β R hR hNR J X hX hSphere r (t-r)
  rw [add_tsub_cancel_of_le hrst] at hfuture
  have he : (fun ω => ⟪brownianVector s ω,X t ω⟫_ℝ/(Real.sqrt 2*(N : ℝ)))=ᵐ[P]
      fun ω => G (Z ω,future r ω) := by
    filter_upwards [hfuture] with ω hω
    dsimp only [G,Z,Y]
    rw [brownianVector_future,add_tsub_cancel_of_le hrs,hω]
    simp only [add_sub_cancel]
    rfl
  have hc := waiting_future_condExp r Z hZa G hG hGi
  refine (condExp_congr_ae he).trans (hc.trans (.of_forall (fun ω => ?_)))
  dsimp only [Z,predictor]
  change (∫ η,⟪brownianVector r ω+brownianVector (s-r) η,jointProcess D β R hR (J,X r ω) (t-r) η⟫_ℝ/
      (Real.sqrt 2*(N : ℝ)) ∂P)=_
  rw [integral_div]
  simp_rw [inner_add_left]
  have hYi := (jointProcess_memLp_two D β R hR J (t-r) (X r ω)).integrable (by norm_num)
  have hB2 := brownianVector_memLp (N:=N) (s-r) (q:=2) (by norm_num)
  have hY2 := jointProcess_memLp_two D β R hR J (t-r) (X r ω)
  have hnorm : Integrable (fun η => ‖brownianVector (s-r) η‖*‖jointProcess D β R hR (J,X r ω) (t-r) η‖) P :=
    (show MemLp _ 1 P from hB2.norm.mul hY2.norm).integrable le_rfl
  have hfi : Integrable (fun η => ⟪brownianVector (s-r) η,jointProcess D β R hR (J,X r ω) (t-r) η⟫_ℝ) P :=
    hnorm.mono' (hB2.aestronglyMeasurable.inner (𝕜:=ℝ) hY2.aestronglyMeasurable)
      (.of_forall (fun η => norm_inner_le_norm (𝕜:=ℝ) _ _))
  have hli : Integrable (fun η => ⟪brownianVector r ω,jointProcess D β R hR (J,X r ω) (t-r) η⟫_ℝ) P := hYi.const_inner (brownianVector r ω)
  rw [integral_add hli hfi]
  rw [add_div]
  congr 1
  · exact congrArg (fun z : ℝ => z/(Real.sqrt 2*(N : ℝ)))
      ((innerSL ℝ (brownianVector r ω)).integral_comp_comm hYi)
  · have hh := backgroundMean_eq_joint_mean β R hR T (t-r) (s-r) (tsub_le_self.trans ht) (J,X r ω)
    change gammaMean β R hR (X r ω) T (t-r) (s-r) J=_ at hh
    rw [←integral_div]
    exact (integral_congr_ae (.of_forall (fun η => by dsimp only [jointGamma];rw [real_inner_comm]))).trans hh.symm

end SphericalAging.ActualGammaBackwardPredictor
