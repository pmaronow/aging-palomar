module

public import SphericalAging.PhysicalStateIncrementFourthMoment
public import SphericalAging.ActualBrownianPrimitiveTimeModulus

public section

/-! Actual Gaussian × uniform sphere × Wiener fourth time increments.
The quenched quartic production is averaged using the true uniform third
landscape moment. The resulting modulus is quadratic at the origin. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualStateIncrementFourthMoment
open HardSphereDynamics FiniteModel GaussianLandscape GaussianLandscapeMoments
open ActualStateIncrementMoments PhysicalStateIncrementFourthMoment ActualSphereTransition
open ActualBrownianPrimitiveTimeModulus AnnealedCutoffProcess
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem cube_add_one_le {z : ℝ} (hz : 0≤z) : (1+z)^3≤4*(1+z^3) := by
  have hh : 0≤3*(z-1)^2*(z+1) := mul_nonneg (by positivity) (by linarith)
  nlinarith only [hh]

theorem driftCube_expectation_bound (hN : 1≤N) (hp : 0<p) (β : ℝ≥0) :
    Integrable (fun J : Disorder N p => (1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J)^3) (disorderLaw N p) ∧
    (∫ J : Disorder N p,(1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J)^3 ∂disorderLaw N p)≤
      4*(1+((β : ℝ)*(p : ℝ))^3*momentCeiling p 3) := by
  have hQ := uniform_real_power_moment hN hp (k:=3) (by norm_num)
  have hQi : Integrable (fun J : Disorder N p => (landscapeNorm N p J)^3) (disorderLaw N p) := by
    simpa only [Real.rpow_ofNat] using hQ.1
  have hQb : (∫ J : Disorder N p,(landscapeNorm N p J)^3 ∂disorderLaw N p)≤momentCeiling p 3 := by
    simpa only [Real.rpow_ofNat] using hQ.2
  have hDom := ((integrable_const (1 : ℝ)).add (hQi.const_mul (((β : ℝ)*(p : ℝ))^3))).const_mul (4 : ℝ)
  have hm := (((landscapeNorm_continuous N p).const_mul ((β : ℝ)*(p : ℝ))).const_add 1).aestronglyMeasurable (μ:=disorderLaw N p) |>.pow 3
  have hi : Integrable (fun J : Disorder N p => (1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J)^3) (disorderLaw N p) := by
    apply hDom.mono' hm
    exact .of_forall (fun J => by
      have hz : 0≤(β : ℝ)*(p : ℝ)*landscapeNorm N p J := by have := landscapeNorm_nonnegative N p J;positivity
      change ‖(1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J)^3‖≤4*(1+((β : ℝ)*(p : ℝ))^3*(landscapeNorm N p J)^3)
      simpa only [Real.norm_of_nonneg (pow_nonneg (by linarith : 0≤1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J) 3),mul_pow] using cube_add_one_le hz)
  refine ⟨hi,?_⟩
  calc
    _≤∫ J : Disorder N p,4*(1+((β : ℝ)*(p : ℝ))^3*(landscapeNorm N p J)^3) ∂disorderLaw N p := by
      apply integral_mono hi hDom
      intro J
      have hz : 0≤(β : ℝ)*(p : ℝ)*landscapeNorm N p J := by have := landscapeNorm_nonnegative N p J;positivity
      change (1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J)^3≤4*(1+((β : ℝ)*(p : ℝ))^3*(landscapeNorm N p J)^3)
      simpa only [mul_pow] using cube_add_one_le hz
    _=4*(1+((β : ℝ)*(p : ℝ))^3*(∫ J : Disorder N p,(landscapeNorm N p J)^3 ∂disorderLaw N p)) := by
      rw [integral_const_mul,integral_add (integrable_const _) (hQi.const_mul _),integral_const_mul]
      simp
    _≤_ := mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hQb (by positivity))) (by norm_num)

theorem fourthIncrementCeiling_le_cube (β : ℝ≥0) (J : Disorder N p) (t : ℝ≥0) :
    fourthIncrementCeiling β J t≤20*(2*(t : ℝ)^3+4*(t : ℝ)^2)*
      (1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J)^3 := by
  let A : ℝ := 1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J
  have hA : 1≤A := by
    dsimp [A]
    have hz : 0≤(β : ℝ)*(p : ℝ)*landscapeNorm N p J := by have := landscapeNorm_nonnegative N p J;positivity
    linarith
  have hA2 : 1≤A^2 := by nlinarith
  have hleft : 8*A+12≤20*A := by linarith
  have hright : 2*(t : ℝ)^3*A^2+4*(t : ℝ)^2≤(2*(t : ℝ)^3+4*(t : ℝ)^2)*A^2 := by
    nlinarith [mul_nonneg (show 0≤4*(t : ℝ)^2 by positivity) (sub_nonneg.mpr hA2)]
  have hh := mul_le_mul hleft hright (by positivity) (by positivity : (0 : ℝ)≤20*A)
  unfold fourthIncrementCeiling
  change (8*A+12)*(2*(t : ℝ)^3*A^2+4*(t : ℝ)^2)≤_
  convert hh using 1 <;> dsimp only [A] <;> ring

@[expose] def incrementFourthCeiling (p : ℕ) (β : ℝ≥0) (t : ℝ≥0) : ℝ :=
  80*(2*(t : ℝ)^3+4*(t : ℝ)^2)*(1+((β : ℝ)*(p : ℝ))^3*momentCeiling p 3)

theorem actual_increment_fourthMoment (hN : 1≤N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (s t : ℝ≥0) :
    (∫ omega,‖actualState (p:=p) β R hR (s+t) omega-actualState β R hR s omega‖^4
      ∂AnnealedModelLaw.law N p)/(N : ℝ)^2≤ incrementFourthCeiling p β t := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let f : Parameter N p×VectorBrownian.Space N→ℝ := fun omega =>
    ‖jointProcess D β R hR omega.1 (s+t) omega.2-jointProcess D β R hR omega.1 s omega.2‖^4
  have he : (fun omega => ‖actualState (p:=p) β R hR (s+t) omega-actualState β R hR s omega‖^4)=ᵐ[
      AnnealedModelLaw.law N p] f := by
    filter_upwards [actualState_ae_joint β R hR (s+t),actualState_ae_joint β R hR s] with omega ha hb
    simp only [f,D,ha,hb]
  have hi : Integrable f (AnnealedModelLaw.law N p) :=
    (actualStateIncrement_memLp_four (p:=p) hN β R hR hNR s t).integrable_norm_pow'.congr he
  have hD := driftCube_expectation_bound (N:=N) hN hp β
  have hDP : Integrable (fun q : Parameter N p => (1+(β : ℝ)*(p : ℝ)*landscapeNorm N p q.1)^3)
      (AnnealedModelLaw.parameterLaw N p) := hD.1.comp_fst (SphereInitialLaw.sphereLaw N)
  have hP := hDP.const_mul ((N : ℝ)^2*(20*(2*(t : ℝ)^3+4*(t : ℝ)^2)))
  have hpoint : ∀ᵐ q ∂AnnealedModelLaw.parameterLaw N p,
      (∫ omega,f (q,omega) ∂VectorBrownian.law N)≤
        (N : ℝ)^2*(20*(2*(t : ℝ)^3+4*(t : ℝ)^2))*(1+(β : ℝ)*(p : ℝ)*landscapeNorm N p q.1)^3 := by
    filter_upwards [AnnealedModelLaw.parameter_initial_onSphere hN p] with q hq
    have hh := jointProcess_increment_fourthMoment (by omega : 0<N) (VectorBrownian.driver N)
      β R hR hNR q.1 q.2 hq s t
    have hn : (0 : ℝ)<(N : ℝ)^2 := by positivity
    have hb := (div_le_iff₀ hn).mp hh.2
    change (∫ omega,f (q,omega) ∂VectorBrownian.law N)≤fourthIncrementCeiling β q.1 t*(N : ℝ)^2 at hb
    exact hb.trans (by
      have hs := mul_le_mul_of_nonneg_right (fourthIncrementCeiling_le_cube β q.1 t) (sq_nonneg (N : ℝ))
      convert hs using 1 <;> ring)
  have hh := integral_mono_ae hi.integral_prod_left hP hpoint
  have hpar : (∫ q : Parameter N p,(1+(β : ℝ)*(p : ℝ)*landscapeNorm N p q.1)^3
      ∂AnnealedModelLaw.parameterLaw N p)=
      ∫ J : Disorder N p,(1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J)^3 ∂disorderLaw N p := by
    rw [AnnealedModelLaw.parameterLaw,integral_prod _ hDP]
    simp
  rw [←integral_prod _ hi,integral_const_mul,hpar] at hh
  rw [integral_congr_ae he]
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<(N : ℝ)^2)).mpr
  refine hh.trans ?_
  have hd := mul_le_mul_of_nonneg_left hD.2
    (show 0≤(N : ℝ)^2*(20*(2*(t : ℝ)^3+4*(t : ℝ)^2)) by positivity)
  convert hd using 1 <;> unfold incrementFourthCeiling <;> ring

end SphericalAging.ActualStateIncrementFourthMoment
