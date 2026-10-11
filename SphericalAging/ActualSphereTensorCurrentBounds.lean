module

public import SphericalAging.ActualSphereTensorProductCurrent
public import SphericalAging.SphereEnergyIncrement

public section

/-! Genuine continuity, probability bounds and sharp Fisher control for
the actual two-semigroup tensor current. Endpoint lag zero is handled by
continuity, while the backward equation is used on the open interval. -/
noncomputable section
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualSphereTensorCurrentBounds
open MeasureTheory Set Filter
open FiniteModel HardSphereDynamics SphereInitialLaw AdaptiveGradientDisclosure
open ActualSphereTensorSemigroup ActualSphereTensorGradient ActualSphereTensorProductCurrent
open SphereFisherHelly SphereRotationGeometry SphereFisherCurrent SphereIntegratedFDT
open SphericalIntegrationByParts SphereEnergyIncrement GaussianLandscape SphereEntropyBudget
open scoped Topology NNReal InnerProductSpace BigOperators
variable {N p k : ℕ}

theorem tensor_fderiv_coordinate {g : State N→TensorSpace N k} (hg : ContDiff ℝ 2 g)
    (x v : State N) (I : TensorIndex N k) :
    (fderiv ℝ g x v) I=fderiv ℝ (fun y => g y I) x v := by
  have hd := (PiLp.proj (𝕜:=ℝ) 2 (fun _ : TensorIndex N k => ℝ) I).hasFDerivAt.comp x
    ((hg.differentiable (by norm_num)) x).hasFDerivAt
  simp only [Function.comp_def,PiLp.proj_apply] at hd
  rw [hd.fderiv]
  rfl

theorem actualTensorPairing_continuous (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (E : FisherDensity N p β) (J : Disorder N p) (T a d : ℝ) :
    Continuous (actualTensorPairing (k:=k) β R hR E J T a d) := by
  unfold actualTensorPairing
  apply continuous_sphere_parameter_integral hN
  exact ((E.smooth J).continuous.comp ((continuous_const.add continuous_fst).prodMk continuous_snd)).mul
    (((realTensorMean_joint_continuous (k:=k) β R hR J).comp
      ((continuous_const.sub continuous_fst).prodMk continuous_snd)).inner
        ((realTensorMean_joint_continuous (k:=k) β R hR J).comp
          ((continuous_const.add continuous_fst).prodMk continuous_snd)))

theorem actualTensorCurrent_continuous (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (E : FisherDensity N p β) (J : Disorder N p) (T a d : ℝ) :
    Continuous (actualTensorCurrent (k:=k) β R hR E J T a d) := by
  classical
  have hρ : ContDiff ℝ 2 (Function.uncurry (E.ρ J)) := (E.smooth J).of_le (by norm_num)
  have hs := (joint_tangentScore_continuous β J hρ (E.positive J)).comp
    ((continuous_const.add continuous_fst).prodMk continuous_snd :
      Continuous (fun w : ℝ×State N => (T+w.1,w.2)))
  have hinner : Continuous (fun w : ℝ×State N =>
      ⟪realTensorMean (k:=k) β R hR J (a-w.1) w.2,
        fderiv ℝ (realTensorMean (k:=k) β R hR J (d+w.1)) w.2
          (tangentScore β J (E.ρ J (T+w.1)) w.2)⟫_ℝ) := by
    have hc := continuous_finsetSum (Finset.univ : Finset (TensorIndex N k)) (fun I _ =>
      ((realTensorMean_coordinate_joint_continuous β R hR J I).comp
        ((continuous_const.sub continuous_fst).prodMk continuous_snd :
          Continuous (fun w : ℝ×State N => (a-w.1,w.2)))).mul
        (((realTensorMean_coordinate_first_joint_continuous β R hR J I).comp
          ((continuous_const.add continuous_fst).prodMk continuous_snd :
            Continuous (fun w : ℝ×State N => (d+w.1,w.2)))).clm_apply hs))
    apply hc.congr
    intro w
    rw [tensor_inner_eq_sum]
    apply Finset.sum_congr rfl
    intro I _
    change realTensorMean (k:=k) β R hR J (a-w.1) w.2 I*
      fderiv ℝ (fun y => realTensorMean (k:=k) β R hR J (d+w.1) y I) w.2
        (tangentScore β J (E.ρ J (T+w.1)) w.2)=
      realTensorMean (k:=k) β R hR J (a-w.1) w.2 I*
        (fderiv ℝ (realTensorMean (k:=k) β R hR J (d+w.1)) w.2
          (tangentScore β J (E.ρ J (T+w.1)) w.2)) I
    congr 1
    exact (tensor_fderiv_coordinate (tensorMean_contDiff_two β R hR J (d+w.1).toNNReal) _ _ I).symm
  unfold actualTensorCurrent
  apply Continuous.const_mul
  apply continuous_sphere_parameter_integral hN
  exact ((E.smooth J).continuous.comp
    ((continuous_const.add continuous_fst).prodMk continuous_snd)).mul hinner

theorem actualTensorPairing_abs_le_one (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (E : FisherDensity N p β) (J : Disorder N p)
    (T a d z : ℝ) (hT : 0≤T+z) :
    |actualTensorPairing (k:=k) β R hR E J T a d z|≤1 := by
  have hρ := (E.smooth J).continuous.comp
    (continuous_const.prodMk continuous_id : Continuous (fun x : State N => (T+z,x)))
  have hf := (tensorMean_contDiff_two (k:=k) β R hR J (a-z).toNNReal).continuous
  have hg := (tensorMean_contDiff_two (k:=k) β R hR J (d+z).toNNReal).continuous
  have hi := continuous_sphere_integrable hN (hρ.mul (hf.inner hg))
  have hp : ∀ᵐ x ∂sphereLaw N,‖E.ρ J (T+z) x*
      ⟪realTensorMean (k:=k) β R hR J (a-z) x,realTensorMean (k:=k) β R hR J (d+z) x⟫_ℝ‖≤E.ρ J (T+z) x := by
    filter_upwards [sphereLaw_support hN] with x hx
    have hxs := (onSphere_iff_norm_sq x).mpr hx
    have hn₁ := tensorMean_norm_le_one (k:=k) hN β R hR hNR J (a-z).toNNReal x hxs
    have hn₂ := tensorMean_norm_le_one (k:=k) hN β R hR hNR J (d+z).toNNReal x hxs
    rw [norm_mul,Real.norm_of_nonneg (E.positive J (T+z) x).le]
    simpa only [mul_one,realTensorMean] using mul_le_mul_of_nonneg_left ((norm_inner_le_norm (𝕜:=ℝ) _ _).trans
      (mul_le_mul hn₁ hn₂ (norm_nonneg _) (by norm_num))) (E.positive J (T+z) x).le
  unfold actualTensorPairing
  change ‖∫x : State N,E.ρ J (T+z) x*
    ⟪realTensorMean (k:=k) β R hR J (a-z) x,realTensorMean (k:=k) β R hR J (d+z) x⟫_ℝ ∂sphereLaw N‖≤1
  exact (norm_integral_le_integral_norm _).trans
    ((integral_mono_ae hi.norm (continuous_sphere_integrable hN hρ) hp).trans_eq (density_mass hN E J hT))

theorem actualTensorCurrent_square_bound (hN : 0<N) (hp : 2≤p) (hk : 1≤k)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (E : FisherDensity N p β) (J : Disorder N p) (T a d z : ℝ)
    (hT : 0≤T+z) (hd : 0≤d+z) :
    (actualTensorCurrent (k:=k) β R hR E J T a d z)^2≤
      (2*(k:ℝ)*Real.exp ((β:ℝ)*(p:ℝ)^2*landscapeNorm N p J*(d+z)))^2*
        (fisherInformation β J (E.ρ J (T+z))/(N:ℝ)) := by
  let f := realTensorMean (k:=k) β R hR J (a-z)
  let g := realTensorMean (k:=k) β R hR J (d+z)
  let score := tangentScore β J (E.ρ J (T+z))
  let c := ((k:ℝ)/Real.sqrt N)*Real.exp ((β:ℝ)*(p:ℝ)^2*landscapeNorm N p J*(d+z))
  have hc : 0≤c := by dsimp only [c];positivity
  have hρ : ContDiff ℝ 2 (E.ρ J (T+z)) := by
    simpa only [Function.comp_def,Function.uncurry,id_eq] using
      ((E.smooth J).of_le (by norm_num) : ContDiff ℝ 2 (Function.uncurry (E.ρ J))).comp
        (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : State N => (T+z,x)))
  have hs : Continuous score := tangentScore_continuous β J hρ (E.positive J (T+z))
  have hf : Continuous f := (tensorMean_contDiff_two β R hR J (a-z).toNNReal).continuous
  have hg : ContDiff ℝ 2 g := tensorMean_contDiff_two β R hR J (d+z).toNNReal
  have hinter : Continuous (fun x => ⟪f x,fderiv ℝ g x (score x)⟫_ℝ) :=
    hf.inner ((hg.continuous_fderiv (by norm_num)).clm_apply hs)
  have hvar := density_integral_square_le hN hρ.continuous hinter (fun x => (E.positive J (T+z) x).le)
    (density_mass hN E J hT)
  have hpw : ∀ᵐ x ∂sphereLaw N,E.ρ J (T+z) x*⟪f x,fderiv ℝ g x (score x)⟫_ℝ^2≤
      c^2*(E.ρ J (T+z) x*‖score x‖^2) := by
    filter_upwards [sphereLaw_support hN] with x hx
    have hxs := (onSphere_iff_norm_sq x).mpr hx
    have hn := tensorMean_norm_le_one (k:=k) hN β R hR hNR J (a-z).toNNReal x hxs
    have hsc : projection x (score x)=score x :=
      projection_idempotent (Nat.ne_of_gt hN) x _ hxs
    have hb := tensorMean_tangent_derivative_norm_le hN hp hk β R hR hNR J x (score x) hxs (d+z).toNNReal
    rw [hsc,Real.coe_toNNReal _ hd] at hb
    change ‖fderiv ℝ g x (score x)‖≤c*‖score x‖ at hb
    have hnorm : ‖⟪f x,fderiv ℝ g x (score x)⟫_ℝ‖≤c*‖score x‖ := by
      calc
        _ ≤ ‖f x‖*‖fderiv ℝ g x (score x)‖ := norm_inner_le_norm (𝕜:=ℝ) _ _
        _ ≤ 1*‖fderiv ℝ g x (score x)‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
        _ ≤ c*‖score x‖ := by simpa only [one_mul] using hb
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mpr hnorm
    rw [Real.norm_eq_abs,sq_abs,mul_pow] at hsq
    nlinarith [mul_le_mul_of_nonneg_left hsq (E.positive J (T+z) x).le]
  have hi₁ := continuous_sphere_integrable hN (hρ.continuous.mul (hinter.pow 2))
  have hi₂ := (continuous_sphere_integrable hN (hρ.continuous.mul (hs.norm.pow 2))).const_mul (c^2)
  have hh := hvar.trans (integral_mono_ae hi₁ hi₂ hpw)
  rw [integral_const_mul] at hh
  change (∫x : State N,E.ρ J (T+z) x*⟪f x,fderiv ℝ g x (score x)⟫_ℝ ∂sphereLaw N)^2≤
    c^2*fisherInformation β J (E.ρ J (T+z)) at hh
  unfold actualTensorCurrent
  have hnormc : 4*c^2*fisherInformation β J (E.ρ J (T+z))=
      (2*(k:ℝ)*Real.exp ((β:ℝ)*(p:ℝ)^2*landscapeNorm N p J*(d+z)))^2*
        (fisherInformation β J (E.ρ J (T+z))/(N:ℝ)) := by
    dsimp only [c]
    rw [mul_pow,div_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
    ring
  rw [←hnormc]
  change (-2*(∫x : State N,E.ρ J (T+z) x*⟪f x,fderiv ℝ g x (score x)⟫_ℝ ∂sphereLaw N))^2≤_
  nlinarith

theorem actualTensorPairing_increment_current (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (E : FisherDensity N p β) (J : Disorder N p)
    (T a d : ℝ) {u v : ℝ} (huv : u≤v) (hT : 0≤T+u) (ha : v≤a) (hd : 0≤d+u) :
    actualTensorPairing (k:=k) β R hR E J T a d v-
      actualTensorPairing (k:=k) β R hR E J T a d u=
        ∫z in u..v,actualTensorCurrent (k:=k) β R hR E J T a d z :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
    (actualTensorPairing_continuous hN β R hR E J T a d).continuousOn
    (fun z hz => actualTensorPairing_hasDerivAt hN β R hR hNR E J T a d z
      (by linarith [hz.1]) (hz.2.trans_le ha) (by linarith [hz.1]))
    ((actualTensorCurrent_continuous hN β R hR E J T a d).intervalIntegrable u v)).symm

end SphericalAging.ActualSphereTensorCurrentBounds
