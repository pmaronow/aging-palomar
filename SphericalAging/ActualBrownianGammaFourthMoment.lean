module

public import SphericalAging.ActualBrownianResponseMemoryIntegrability
public import SphericalAging.ActualBackgroundGammaLaw

public section

/-! Dimension-independent fourth moments of the literal actual Brownian
pairing, at arbitrary pairs of times. This supplies genuine Hölder weights
for replacing correlations inside the Brownian response memory. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualBrownianGammaFourthMoment
open HardSphereDynamics FiniteModel FiniteCorrelationIto BrownianVectorMoments
  ActualBackgroundGammaLaw ActualBrownianPrimitiveTimeModulus
  ActualBrownianResponseMemoryIntegrability AnnealedResponseMatrixContraction
  ActualResponseCoefficientIntegral AnnealedTwoTimeResponseMoments
  BrownianHessianCovarianceContraction TwoTimeResponseParameter TwoTimeResponseTimeParameter
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

lemma jointGamma_stronglyMeasurable (β R : ℝ≥0) (hR : 0<(R : ℝ)) (t s : ℝ≥0) :
    StronglyMeasurable (jointGamma (N := N) (p := p) β R hR t s) := by
  have hB : StronglyMeasurable (brownianVector (N := N) s) :=
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)).symm.continuous.measurable.comp
      (VectorBrownian.process_measurable N s)).stronglyMeasurable
  convert ((trajectory_stronglyMeasurable (p := p)
    (NullAugmentation.driver (VectorBrownian.driver N)) β R hR t).inner (𝕜 := ℝ)
    hB.comp_snd).mul_const (Real.sqrt 2*N)⁻¹ using 1
  funext q
  simp only [jointGamma,trajectory,div_eq_mul_inv]

 theorem jointGamma_memLp (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (t s : ℝ≥0) {q : ℝ≥0∞} (hq : q≠⊤) :
    MemLp (jointGamma (N := N) (p := p) β R hR t s) q (AnnealedModelLaw.law N p) := by
  have hB := (brownianVector_memLp (N := N) s (q := q) hq).comp_snd (AnnealedModelLaw.parameterLaw N p)
  apply hB.of_le_mul (c := Real.sqrt N/(Real.sqrt 2*N))
    (jointGamma_stronglyMeasurable β R hR t s).aestronglyMeasurable
  filter_upwards [trajectory_onSphere (p := p) hN (VectorBrownian.driver N) β R hR hNR t] with z hz
  have hd : 0<Real.sqrt 2*(N : ℝ) := by positivity
  rw [Real.norm_eq_abs,jointGamma,abs_div,abs_of_pos hd]
  calc
    _≤(Real.sqrt N*‖brownianVector s z.2‖)/(Real.sqrt 2*N) := by
      apply div_le_div_of_nonneg_right _ hd.le
      have hh := abs_real_inner_le_norm
        (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR t z) (brownianVector s z.2)
      rw [sphere_norm hz] at hh
      exact hh
    _=_ := by ring

 theorem jointGamma_fourthMoment_le (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (t s : ℝ≥0) :
    (∫ z,|jointGamma (N := N) (p := p) β R hR t s z|^4 ∂AnnealedModelLaw.law N p)≤
      3*(s : ℝ)^2/4 := by
  have hi := (jointGamma_memLp (p := p) hN β R hR hNR t s (q := 4) (by norm_num)).integrable_norm_pow'
  have hB := (ActualBrownianPrimitiveTimeModulus.actualBrownian_memLp (N := N) (p := p) s
    (q := 4) (by norm_num)).integrable_norm_pow'.div_const (4*(N : ℝ)^2)
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  calc
    _≤∫ z,‖brownianVector s z.2‖^4/(4*(N : ℝ)^2) ∂AnnealedModelLaw.law N p := by
      apply integral_mono_ae (by simpa only [Real.norm_eq_abs] using hi) hB
      filter_upwards [trajectory_onSphere (p := p) hN (VectorBrownian.driver N) β R hR hNR t] with z hz
      have hh := sphere_pairing_square_le hN
        (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR t z) (brownianVector s z.2) hz
      have hs := (sq_le_sq₀ (sq_nonneg _) (div_nonneg (sq_nonneg _) (by positivity))).mpr hh
      simpa only [jointGamma,trajectory,actualBrownian,show (4 : ℕ)=2*2 from rfl,pow_mul,sq_abs,div_pow,mul_pow,
        show (2 : ℝ)^2=4 from by norm_num] using hs
    _=(∫ z,‖brownianVector (N := N) s z.2‖^4 ∂AnnealedModelLaw.law N p)/(4*(N : ℝ)^2) := integral_div _ _
    _≤(3*(N : ℝ)^2*(s : ℝ)^2)/(4*(N : ℝ)^2) := div_le_div_of_nonneg_right
      (actualBrownian_fourthMoment_le (N := N) (p := p) s) (by positivity)
    _=_ := by field_simp

 theorem waitingGamma_slice_memLp_four (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H S : ℝ≥0) (r : WaitingTime H) :
    MemLp (fun q => waitingGamma (N := N) (p := p) β R hR H S (r,q)) 4
      (AnnealedModelLaw.law N p) := jointGamma_memLp hN β R hR hNR r S (by norm_num)

 theorem waitingGamma_slice_fourthMoment_le (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H S : ℝ≥0) (r : WaitingTime H) :
    (∫ q,|waitingGamma (N := N) (p := p) β R hR H S (r,q)|^4 ∂AnnealedModelLaw.law N p)≤
      3*(S : ℝ)^2/4 := jointGamma_fourthMoment_le hN β R hR hNR r S

end SphericalAging.ActualBrownianGammaFourthMoment
