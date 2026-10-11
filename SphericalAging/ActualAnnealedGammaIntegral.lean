module

public import SphericalAging.ActualQuenchedGammaIntegral
public import SphericalAging.ActualAnnealedCorrelationIntegral
public import SphericalAging.ActualBrownianPrimitiveTimeModulus

public section

/-! The actual full Gaussian × sphere × Wiener expectation satisfies its
Brownian-pairing integral row. Time and parameter Fubini are proved from
Gaussian landscape integrability and the genuine unbounded Brownian law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualAnnealedGammaIntegral
open HardSphereDynamics FiniteModel ActualSphereTransition FiniteCorrelationIto
  ActualQuenchedCorrelationIntegral ActualQuenchedPastVectorMean ActualQuenchedGammaIntegral
  ActualAnnealedCorrelationIntegral BrownianVectorMoments AnnealedTwoTimeResponseMoments
  AnnealedResponseMatrixContraction
  ForkEnergyComparison GaussianLandscape
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def annealedGammaPair (β R : ℝ≥0) (hR : 0<(R : ℝ)) (t s : ℝ≥0) : ℝ :=
  ∫ q : ModelSample N p,inner ℝ
    (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR t q)
    (brownianVector s q.2)/(Real.sqrt 2*N) ∂AnnealedModelLaw.law N p

@[expose] def gammaDriftField (β R : ℝ≥0) (hR : 0<(R : ℝ)) (s : ℝ≥0)
    (q : ℝ×ModelSample N p) : ℝ :=
  inner ℝ (hamiltonianDrift β q.2.1.1
    (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1.toNNReal q.2))
    (brownianVector s q.2.2)/(Real.sqrt 2*N)

lemma gammaDriftField_stronglyMeasurable (β R : ℝ≥0) (hR : 0<(R : ℝ)) (s : ℝ≥0) :
    StronglyMeasurable (gammaDriftField (N := N) (p := p) β R hR s) := by
  have hX : StronglyMeasurable (fun q : ℝ×ModelSample N p =>
      trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1.toNNReal q.2) :=
    (jointProcess_measurable (NullAugmentation.driver (VectorBrownian.driver N)) β R hR).comp_measurable
      ((measurable_fst.comp measurable_snd).prodMk
        (((continuous_real_toNNReal.measurable).comp measurable_fst).prodMk
          (measurable_snd.comp measurable_snd)))
  have hJ : StronglyMeasurable (fun q : ℝ×ModelSample N p => q.2.1.1) :=
    (measurable_fst.comp (measurable_fst.comp measurable_snd)).stronglyMeasurable
  have hdc : Continuous (fun z : Disorder N p×State N => hamiltonianDrift β z.1 z.2) := by
    unfold hamiltonianDrift drift hamiltonianGradient
    exact ((SphereInitialFisherCovariance.projected_gradient_joint_continuous N p).const_smul (β : ℝ)).sub
      (continuous_snd.const_smul (kappa N))
  have hB : StronglyMeasurable (brownianVector (N := N) s) :=
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)).symm.continuous.measurable.comp
      (VectorBrownian.process_measurable N s)).stronglyMeasurable
  convert ((hdc.comp_stronglyMeasurable (hJ.prodMk hX)).inner (𝕜 := ℝ)
    hB.comp_snd.comp_snd).mul_const (Real.sqrt 2*N)⁻¹ using 1
  funext q
  simp only [gammaDriftField,div_eq_mul_inv]

lemma gammaDriftField_integrable (hN : 0<N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (s t : ℝ≥0) :
    Integrable (gammaDriftField (N := N) (p := p) β R hR s)
      ((volume.restrict (Ioc (s : ℝ) (t : ℝ))).prod (AnnealedModelLaw.law N p)) := by
  let ν := volume.restrict (Ioc (s : ℝ) (t : ℝ))
  let μ := AnnealedModelLaw.parameterLaw N p
  have hQ : Integrable (fun q : Disorder N p×State N => landscapeNorm N p q.1) μ :=
    ((landscape_memLp_two hN hp).integrable (by norm_num)).comp_fst (SphereInitialLaw.sphereLaw N)
  have hA : Integrable (fun q : Disorder N p×State N =>
      (1+(β : ℝ)*(p : ℝ)*landscapeNorm N p q.1)*Real.sqrt N/(Real.sqrt 2*N)) μ :=
    (((integrable_const (1 : ℝ)).add (hQ.const_mul ((β : ℝ)*(p : ℝ)))).mul_const (Real.sqrt N)).div_const _
  have hBn : Integrable (fun ω => ‖brownianVector (N := N) s ω‖) (VectorBrownian.law N) :=
    (brownianVector_memLp s (q := 2) (by norm_num)).norm.integrable (by norm_num)
  have hEnv := (hA.mul_prod hBn).comp_snd ν
  have hX : StronglyMeasurable (fun q : ℝ×ModelSample N p =>
      trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1.toNNReal q.2) :=
    (jointProcess_measurable (NullAugmentation.driver (VectorBrownian.driver N)) β R hR).comp_measurable
      ((measurable_fst.comp measurable_snd).prodMk
        (((continuous_real_toNNReal.measurable).comp measurable_fst).prodMk
          (measurable_snd.comp measurable_snd)))
  have hsp : ∀ᵐ q ∂ν.prod (AnnealedModelLaw.law N p),OnSphere
      (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1.toNNReal q.2) := by
    apply (Measure.ae_prod_iff_ae_ae (ActualSphereKernelSupport.measurableSet_onSphere.preimage hX.measurable)).mpr
    exact .of_forall (fun u => trajectory_onSphere (p := p) hN (VectorBrownian.driver N) β R hR hNR u.toNNReal)
  apply hEnv.mono' (gammaDriftField_stronglyMeasurable β R hR s).aestronglyMeasurable
  filter_upwards [hsp] with q hq
  have hd : 0<Real.sqrt 2*(N : ℝ) := by positivity
  rw [gammaDriftField,Real.norm_eq_abs,abs_div,abs_of_pos hd]
  calc
    _≤(‖hamiltonianDrift β q.2.1.1 (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1.toNNReal q.2)‖*
      ‖brownianVector s q.2.2‖)/(Real.sqrt 2*N) :=
      div_le_div_of_nonneg_right (norm_inner_le_norm (𝕜 := ℝ) _ _) hd.le
    _≤((1+(β : ℝ)*(p : ℝ)*landscapeNorm N p q.2.1.1)*Real.sqrt N*‖brownianVector s q.2.2‖)/(Real.sqrt 2*N) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (PhysicalStateIncrementMoments.drift_norm_onSphere hN β _ _ hq) (norm_nonneg _)) hd.le
    _=_ := by ring

lemma annealedGammaPair_integrable (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (t s : ℝ≥0) :
    Integrable (fun q : ModelSample N p => inner ℝ
      (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR t q)
      (brownianVector s q.2)/(Real.sqrt 2*N)) (AnnealedModelLaw.law N p) := by
  have hh := (ActualBrownianPrimitiveTimeModulus.actualGamma_memLp_two (p := p)
    (by omega : 1≤N) β R hR hNR t s).ae_eq
      (ActualBackgroundGammaLaw.actualGamma_ae_joint β R hR t s)
  exact hh.integrable (by norm_num)

 theorem actual_annealed_gamma_integral (hN : 0<N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (s t : ℝ≥0) (hst : s≤t) :
    annealedGammaPair (N := N) (p := p) β R hR t s=annealedGammaPair (N := N) (p := p) β R hR s s+
      ∫ u in (s : ℝ)..(t : ℝ),∫ q : ModelSample N p,gammaDriftField β R hR s (u,q)
        ∂AnnealedModelLaw.law N p := by
  let ν := volume.restrict (Ioc (s : ℝ) (t : ℝ))
  let μ := AnnealedModelLaw.parameterLaw N p
  let P := VectorBrownian.law N
  have hi := gammaDriftField_integrable hN hp β R hR hNR s t
  have hswap := integral_integral_swap (f := fun u q => gammaDriftField (N := N) (p := p) β R hR s (u,q)) hi
  have htime : Integrable (fun q : ModelSample N p =>
      ∫ u in (s : ℝ)..(t : ℝ),gammaDriftField β R hR s (u,q)) (μ.prod P) := by
    simpa only [intervalIntegral.integral_of_le (show (s : ℝ)≤t from hst),AnnealedModelLaw.law,μ,P] using hi.integral_prod_right
  unfold annealedGammaPair AnnealedModelLaw.law
  rw [integral_prod _ (annealedGammaPair_integrable (p := p) hN β R hR hNR t s),
    integral_prod _ (annealedGammaPair_integrable (p := p) hN β R hR hNR s s)]
  have hqe : (fun q : Disorder N p×State N => ∫ ω,inner ℝ
      (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR t (q,ω))
      (brownianVector s ω)/(Real.sqrt 2*N) ∂P)=ᵐ[μ]
      (fun q => (∫ ω,inner ℝ
        (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s (q,ω))
        (brownianVector s ω)/(Real.sqrt 2*N) ∂P)+
        ∫ ω,(∫ u in (s : ℝ)..(t : ℝ),gammaDriftField β R hR s (u,(q,ω))) ∂P) := by
    filter_upwards [parameterLaw_onSphere (p := p) hN] with q hq
    have he := actual_quenched_gamma_integral hN β R hR hNR q.1 q.2 hq s t hst
    have hBn : Integrable (fun ω => ‖brownianVector (N := N) s ω‖) P :=
      (brownianVector_memLp s (q := 2) (by norm_num)).norm.integrable (by norm_num)
    have hrow : Integrable (pastDrift (NullAugmentation.driver (VectorBrownian.driver N))
        β R hR q.1 q.2 (brownianVector s)) (ν.prod P) := by
      apply ((hBn.const_mul ((1+(β : ℝ)*(p : ℝ)*landscapeNorm N p q.1)*Real.sqrt N/(Real.sqrt 2*N))).comp_snd ν).mono'
        (pastDrift_stronglyMeasurable _ _ _ _ _ _ _
          (ActualGammaFutureInnovation.brownianVector_waiting_measurable s |>.mono
            ((NullAugmentation.augment (VectorBrownian.filtration N) P).le s) le_rfl |>.stronglyMeasurable)).aestronglyMeasurable
      filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := ν) (ν := P)).ae
        (jointProcess_onSphere (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR q.1 q.2 hq)] with z hz
      have hd : 0<Real.sqrt 2*(N : ℝ) := by positivity
      rw [pastDrift,Real.norm_eq_abs,abs_div,abs_of_pos hd]
      calc
        _≤(‖hamiltonianDrift β q.1 (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (q.1,q.2) z.1.toNNReal z.2)‖*
            ‖brownianVector s z.2‖)/(Real.sqrt 2*N) :=
          div_le_div_of_nonneg_right (norm_inner_le_norm (𝕜 := ℝ) _ _) hd.le
        _≤((1+(β : ℝ)*(p : ℝ)*landscapeNorm N p q.1)*Real.sqrt N*‖brownianVector s z.2‖)/(Real.sqrt 2*N) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
            (PhysicalStateIncrementMoments.drift_norm_onSphere hN β _ _ (hz _)) (norm_nonneg _)) hd.le
        _=_ := by ring
    change gammaPair β R hR q.1 q.2 t s=_
    rw [he]
    congr 1
    simp only [intervalIntegral.integral_of_le (show (s : ℝ)≤t from hst)]
    exact integral_integral_swap (f := fun u ω => pastDrift
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1 q.2 (brownianVector s) (u,ω)) hrow
  rw [integral_congr_ae hqe,integral_add
    (annealedGammaPair_integrable (p := p) hN β R hR hNR s s).integral_prod_left htime.integral_prod_left]
  congr 1
  rw [←integral_prod _ htime]
  simpa only [intervalIntegral.integral_of_le (show (s : ℝ)≤t from hst),AnnealedModelLaw.law,μ,P] using hswap.symm

end SphericalAging.ActualAnnealedGammaIntegral
