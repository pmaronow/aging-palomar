module

public import SphericalAging.ActualQuenchedCorrelationIntegral
public import SphericalAging.ActualCKCorrelationForceResidual
public import SphericalAging.ForkEnergyComparison
public import SphericalAging.SphereInitialFisherCovariance

public section

/-! True full-law correlation integral equation. The parameter and time
integrals are justified by actual sphere support and Gaussian landscape
moments, before any CK closure is asserted. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualAnnealedCorrelationIntegral
open HardSphereDynamics FiniteModel ActualSphereTransition FiniteCorrelationIto
  AnnealedResponseMatrixContraction ActualQuenchedCorrelationIntegral
  AnnealedTwoTimeResponseMoments ForkEnergyComparison GaussianLandscape
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] abbrev ModelSample (N p : ℕ) := (Disorder N p × State N) × VectorBrownian.Space N

@[expose] def correlationPair (β R : ℝ≥0) (hR : 0<(R : ℝ)) (s t : ℝ≥0) : ℝ :=
  ∫ q : ModelSample N p, overlap
    (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR t q)
    (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s q)
    ∂AnnealedModelLaw.law N p

@[expose] def driftField (β R : ℝ≥0) (hR : 0<(R : ℝ)) (s : ℝ≥0)
    (q : ℝ × ModelSample N p) : ℝ :=
  inner ℝ (hamiltonianDrift β q.2.1.1
    (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1.toNNReal q.2))
    (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s q.2)/(N : ℝ)

lemma driftField_stronglyMeasurable (β R : ℝ≥0) (hR : 0<(R : ℝ)) (s : ℝ≥0) :
    StronglyMeasurable (driftField (N := N) (p := p) β R hR s) := by
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
  have hD := hdc.comp_stronglyMeasurable (hJ.prodMk hX)
  convert (hD.inner (𝕜 := ℝ) (trajectory_stronglyMeasurable
    (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s).comp_snd).mul_const (N : ℝ)⁻¹ using 1
  funext q
  simp only [driftField,div_eq_mul_inv]

lemma driftField_integrable (hN : 0<N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (s t : ℝ≥0) :
    Integrable (driftField (N := N) (p := p) β R hR s)
      ((volume.restrict (Ioc (s : ℝ) (t : ℝ))).prod (AnnealedModelLaw.law N p)) := by
  let ν := volume.restrict (Ioc (s : ℝ) (t : ℝ))
  let μ := AnnealedModelLaw.law N p
  have hQ : Integrable (fun q : ModelSample N p => landscapeNorm N p q.1.1) μ :=
    ((landscape_memLp_two hN hp).integrable (by norm_num)).comp_fst
      (SphereInitialLaw.sphereLaw N) |>.comp_fst (VectorBrownian.law N)
  have hEnv : Integrable (fun q : ℝ×ModelSample N p =>
      1+(β : ℝ)*(p : ℝ)*landscapeNorm N p q.2.1.1) (ν.prod μ) := by
    convert ((integrable_const (1 : ℝ)).add (hQ.const_mul ((β : ℝ)*(p : ℝ)))).comp_snd ν using 1
  have hsphere : ∀ᵐ q ∂ν.prod μ,
      OnSphere (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1.toNNReal q.2) ∧
      OnSphere (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s q.2) := by
    apply (Measure.ae_prod_iff_ae_ae ?_).mpr
    · exact .of_forall (fun u => (trajectory_onSphere (p := p) hN (VectorBrownian.driver N)
        β R hR hNR u.toNNReal).and
          (trajectory_onSphere (p := p) hN (VectorBrownian.driver N) β R hR hNR s))
    · have hm := driftField_stronglyMeasurable (N := N) (p := p) β R hR s
      have hX : StronglyMeasurable (fun q : ℝ×ModelSample N p =>
          trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1.toNNReal q.2) :=
        (jointProcess_measurable (NullAugmentation.driver (VectorBrownian.driver N)) β R hR).comp_measurable
          ((measurable_fst.comp measurable_snd).prodMk
            (((continuous_real_toNNReal.measurable).comp measurable_fst).prodMk
              (measurable_snd.comp measurable_snd)))
      have hY := (trajectory_stronglyMeasurable (p := p)
        (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s).comp_snd (α := ℝ)
      exact (hX.inner hX).measurableSet_eq_fun stronglyMeasurable_const |>.inter
        ((hY.inner hY).measurableSet_eq_fun stronglyMeasurable_const)
  apply hEnv.mono' (driftField_stronglyMeasurable β R hR s).aestronglyMeasurable
  filter_upwards [hsphere] with q hq
  rw [Real.norm_eq_abs]
  exact normalized_drift_pairing_abs_le hN β q.2.1.1 hq.1 hq.2

lemma correlationPair_integrable (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (s t : ℝ≥0) :
    Integrable (fun q : ModelSample N p => overlap
      (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR t q)
      (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s q))
      (AnnealedModelLaw.law N p) := by
  have hm := ((trajectory_stronglyMeasurable (p := p)
    (NullAugmentation.driver (VectorBrownian.driver N)) β R hR t).inner
      (trajectory_stronglyMeasurable (p := p)
        (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s)).mul_const (N : ℝ)⁻¹
  apply Integrable.of_bound (by convert hm.aestronglyMeasurable using 1 <;> simp [overlap,div_eq_mul_inv]) 1
  filter_upwards [trajectory_onSphere (p := p) hN (VectorBrownian.driver N) β R hR hNR t,
    trajectory_onSphere (p := p) hN (VectorBrownian.driver N) β R hR hNR s] with q ht hs
  exact overlap_abs_le_one hN ht hs

 theorem actual_annealed_correlation_integral (hN : 0<N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (s t : ℝ≥0) (hst : s≤t) :
    correlationPair (N := N) (p := p) β R hR s t=
      1+∫ u in (s : ℝ)..(t : ℝ),∫ q : ModelSample N p,driftField β R hR s (u,q)
        ∂AnnealedModelLaw.law N p := by
  let ν := volume.restrict (Ioc (s : ℝ) (t : ℝ))
  let μ := AnnealedModelLaw.parameterLaw N p
  let P := VectorBrownian.law N
  have hi := driftField_integrable hN hp β R hR hNR s t
  have hswap := integral_integral_swap (f := fun u q => driftField (N := N) (p := p) β R hR s (u,q)) hi
  have htime : Integrable (fun q : ModelSample N p => ∫ u in (s : ℝ)..(t : ℝ),driftField β R hR s (u,q)) (μ.prod P) := by
    simpa only [intervalIntegral.integral_of_le (show (s : ℝ)≤t from hst),AnnealedModelLaw.law,μ,P] using hi.integral_prod_right
  unfold correlationPair AnnealedModelLaw.law
  rw [integral_prod _ (correlationPair_integrable (p := p) hN β R hR hNR s t)]
  have hqe : (fun q : Disorder N p×State N => ∫ ω,overlap
      (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR t (q,ω))
      (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s (q,ω)) ∂P)=ᵐ[μ]
      (fun q => 1+∫ ω,(∫ u in (s : ℝ)..(t : ℝ),driftField β R hR s (u,(q,ω))) ∂P) := by
    filter_upwards [parameterLaw_onSphere (p := p) hN] with q hq
    have he := actual_quenched_correlation_integral hN (VectorBrownian.driver N) β R hR hNR q.1 q.2 hq s t hst
    have hrow : Integrable (rowDrift (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1 q.2 s) (ν.prod P) :=
      Integrable.of_bound (rowDrift_stronglyMeasurable _ _ _ _ _ _ _).aestronglyMeasurable
        (1+(β : ℝ)*(p : ℝ)*landscapeNorm N p q.1) (by
          filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := ν) (ν := P)).ae
            (jointProcess_onSphere (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR q.1 q.2 hq)] with z hz
          rw [Real.norm_eq_abs]
          exact normalized_drift_pairing_abs_le hN β q.1 (hz z.1.toNNReal) (hz s))
    change (∫ ω,overlap (jointProcess (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR (q.1,q.2) t ω) (jointProcess (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR (q.1,q.2) s ω) ∂VectorBrownian.law N)=_
    rw [he]
    congr 1
    simp only [intervalIntegral.integral_of_le (show (s : ℝ)≤t from hst)]
    exact integral_integral_swap (f := fun u ω => rowDrift
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1 q.2 s (u,ω)) hrow
  rw [integral_congr_ae hqe,integral_add (integrable_const 1) htime.integral_prod_left]
  simp only [integral_const,probReal_univ,one_smul]
  congr 1
  rw [← integral_prod _ htime]
  simpa only [intervalIntegral.integral_of_le (show (s : ℝ)≤t from hst),AnnealedModelLaw.law,μ,P] using hswap.symm

end SphericalAging.ActualAnnealedCorrelationIntegral
