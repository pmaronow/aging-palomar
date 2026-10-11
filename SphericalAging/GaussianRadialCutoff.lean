module

public import SphericalAging.GaussianRadiusVariance
public import SphericalAging.SphereInitialLaw
public import SphericalAging.HardSphereDynamics
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inv

public section

/-! Smooth radial extension for functions on the actual initial sphere.
The cutoff removes the normalization singularity at the origin; all
constants of the one-dimensional transition are independent of N. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace BigOperators NNReal ENNReal
namespace SphericalAging.GaussianRadialCutoff
open HardSphereDynamics SphereInitialLaw
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

 lemma transition_deriv_zero_lt {u : ℝ} (hu : u<0) : deriv Real.smoothTransition u=0 := by
  apply HasDerivAt.deriv
  apply (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hu] with v hv
  exact Real.smoothTransition.zero_of_nonpos hv.le

 lemma transition_deriv_zero_gt {u : ℝ} (hu : 1<u) : deriv Real.smoothTransition u=0 := by
  apply HasDerivAt.deriv
  apply (hasDerivAt_const u (1 : ℝ)).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hu] with v hv
  exact Real.smoothTransition.one_of_one_le hv.le

 theorem exists_transition_deriv_bound : ∃ B : ℝ≥0,∀ u : ℝ,|deriv Real.smoothTransition u|≤B := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv_one
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨⟨max C 0,le_max_right _ _⟩,fun u => ?_⟩
  by_cases h0 : u<0
  · rw [transition_deriv_zero_lt h0,abs_zero]
    exact le_max_right _ _
  by_cases h1 : 1<u
  · rw [transition_deriv_zero_gt h1,abs_zero]
    exact le_max_right _ _
  have hh : |deriv Real.smoothTransition u|≤C := by simpa only [Real.norm_eq_abs] using hC u ⟨le_of_not_gt h0,le_of_not_gt h1⟩
  exact hh.trans (le_max_left _ _)

@[expose]  def transitionBound : ℝ≥0 := exists_transition_deriv_bound.choose
 lemma transitionBound_spec (u : ℝ) : |deriv Real.smoothTransition u|≤transitionBound :=
  exists_transition_deriv_bound.choose_spec u

@[expose]  def cutoff (N : ℕ) (z : State N) : ℝ := Real.smoothTransition (4*‖z‖^2/(N : ℝ)-1)
@[expose]  def extension (N : ℕ) (f : State N → ℝ) (z : State N) : ℝ := cutoff N z*f (normalize N z)

 lemma cutoff_nonneg (z : State N) : 0≤cutoff N z := Real.smoothTransition.nonneg _
 lemma cutoff_le_one (z : State N) : cutoff N z≤1 := Real.smoothTransition.le_one _
 lemma cutoff_zero (hN : 0<N) (z : State N) (hz : ‖z‖^2≤(N : ℝ)/4) : cutoff N z=0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  apply sub_nonpos.mpr
  apply (div_le_one hn).mpr
  nlinarith
 lemma cutoff_one (hN : 0<N) (z : State N) (hz : (N : ℝ)/2≤‖z‖^2) : cutoff N z=1 := by
  apply Real.smoothTransition.one_of_one_le
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  apply le_sub_iff_add_le.mpr
  apply (le_div_iff₀ hn).mpr
  nlinarith

 lemma norm_hasFDerivAt (z : State N) (hz : z≠0) :
    HasFDerivAt (fun y : State N => ‖y‖) ((1/‖z‖) • innerSL ℝ z) z := by
  have hn : ‖z‖≠0 := norm_ne_zero_iff.mpr hz
  have hs : ‖z‖^2≠0 := pow_ne_zero _ hn
  have hh := (Real.hasDerivAt_sqrt hs).comp_hasFDerivAt z (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  convert hh using 1
  · funext y
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg y)]
  · rw [Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg z),← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
    congr 1
    field_simp <;> norm_num

 lemma normalize_hasFDerivAt (hN : 0<N) (z : State N) (hz : z≠0) :
    HasFDerivAt (normalize N)
      ((Real.sqrt N/‖z‖) • ContinuousLinearMap.id ℝ (State N)-
        (Real.sqrt N/‖z‖^3) • ((innerSL ℝ z).smulRight z)) z := by
  have hn : ‖z‖≠0 := norm_ne_zero_iff.mpr hz
  have hh := (((hasDerivAt_inv hn).comp_hasFDerivAt z (norm_hasFDerivAt z hz)).const_mul (Real.sqrt N)).smul (hasFDerivAt_id z)
  convert hh using 1
  · funext y
    change (Real.sqrt N/‖y‖) • y=(Real.sqrt N*‖y‖⁻¹) • y
    rw [div_eq_mul_inv]
  · ext1 v
    simp only [ContinuousLinearMap.sub_apply,smul_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.add_apply,innerSL_apply_apply,
      smul_eq_mul,smul_smul,ContinuousLinearMap.zero_apply,Function.comp_apply,id_eq]
    ext i
    simp only [PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,smul_eq_mul]
    field_simp
    ring

 lemma normalize_derivative_projected (hN : 0<N) (z v : State N) (hz : z≠0) :
    fderiv ℝ (normalize N) z v=(Real.sqrt N/‖z‖) • projection (normalize N z) v := by
  rw [(normalize_hasFDerivAt hN z hz).fderiv]
  simp only [ContinuousLinearMap.sub_apply,smul_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,projection,SphereInitialLaw.normalize,real_inner_smul_left,
    smul_sub,smul_smul]
  have hn : ‖z‖≠0 := norm_ne_zero_iff.mpr hz
  have hnN : (N : ℝ)≠0 := (Nat.cast_pos.mpr hN).ne'
  have hs := Real.sq_sqrt (Nat.cast_nonneg N)
  congr 1
  congr 1
  field_simp
  rw [hs]
  ring


 lemma cutoff_hasFDerivAt (z : State N) : HasFDerivAt (cutoff N)
      (((8/(N : ℝ))*deriv Real.smoothTransition (4*‖z‖^2/(N : ℝ)-1)) • innerSL ℝ z) z := by
  have hu := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul (4/(N : ℝ))).sub_const 1
  have hh := ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) _).hasDerivAt.comp_hasFDerivAt z hu
  have he : (4/(N : ℝ))*‖z‖^2-1=4*‖z‖^2/(N : ℝ)-1 := by ring
  rw [he] at hh
  convert hh using 1
  · funext y
    change Real.smoothTransition (4*‖y‖^2/(N : ℝ)-1)=Real.smoothTransition ((4/(N : ℝ))*‖y‖^2-1)
    congr 1
    ring
  ext1 v
  simp only [ContinuousLinearMap.comp_apply,smul_apply,innerSL_apply_apply,ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.smulRight_apply,smul_eq_mul,ContinuousLinearMap.one_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.id_apply,← Nat.cast_smul_eq_nsmul ℝ,Nat.cast_ofNat]
  ring

 lemma extension_zero_near (hN : 0<N) (f : State N → ℝ) :
    extension N f=ᶠ[𝓝 (0 : State N)] fun _ => 0 := by
  have hh : ∀ᶠ z : State N in 𝓝 0,‖z‖^2<(N : ℝ)/4 :=
    ((continuous_norm.pow 2).continuousAt.tendsto.eventually_lt_const (show ‖(0 : State N)‖^2<(N : ℝ)/4 by simpa using (show (0 : ℝ)<(N : ℝ)/4 by exact div_pos (Nat.cast_pos.mpr hN) (by norm_num))))
  filter_upwards [hh] with z hz
  rw [extension,cutoff_zero hN z hz.le,zero_mul]

 theorem extension_differentiable (hN : 0<N) {f : State N → ℝ} (hf : Differentiable ℝ f) :
    Differentiable ℝ (extension N f) := by
  intro z
  by_cases hz : z=0
  · subst z
    exact (hasFDerivAt_zero_of_eventually_const (0 : ℝ) (extension_zero_near hN f)).differentiableAt
  · exact (cutoff_hasFDerivAt z).differentiableAt.mul ((hf _).comp z (normalize_hasFDerivAt hN z hz).differentiableAt)

 lemma extension_fderiv_zero (hN : 0<N) (f : State N → ℝ) : fderiv ℝ (extension N f) 0=0 :=
  (hasFDerivAt_zero_of_eventually_const (0 : ℝ) (extension_zero_near hN f)).fderiv


 theorem cutoff_derivative_norm_le (hN : 0<N) (z : State N) :
    ‖fderiv ℝ (cutoff N) z‖≤8*(transitionBound : ℝ)/Real.sqrt N := by
  rw [(cutoff_hasFDerivAt z).fderiv,norm_smul,innerSL_apply_norm]
  let u := 4*‖z‖^2/(N : ℝ)-1
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  have hs : 0<Real.sqrt N := Real.sqrt_pos.mpr hn
  by_cases h0 : u<0
  · rw [transition_deriv_zero_lt h0,mul_zero,norm_zero,zero_mul]
    positivity
  by_cases h1 : 1<u
  · rw [transition_deriv_zero_gt h1,mul_zero,norm_zero,zero_mul]
    positivity
  have hzz : ‖z‖≤Real.sqrt N := by
    have hu : 4*‖z‖^2/(N : ℝ)≤2 := by dsimp [u] at h1;linarith
    have hh := (div_le_iff₀ hn).mp hu
    exact (Real.le_sqrt (norm_nonneg z) (Nat.cast_nonneg N)).mpr (by nlinarith)
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (show 0≤8/(N : ℝ) by positivity)]
  calc
    _ ≤ (8/(N : ℝ))*(transitionBound : ℝ)*‖z‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (transitionBound_spec u) (by positivity)) (norm_nonneg z)
    _ ≤ (8/(N : ℝ))*(transitionBound : ℝ)*Real.sqrt N :=
      mul_le_mul_of_nonneg_left hzz (by positivity)
    _ = _ := by
      have hh := Real.sq_sqrt (Nat.cast_nonneg N)
      field_simp
      nlinarith [hh]

 theorem extension_abs_le (hN : 0<N) {f : State N → ℝ} {M : ℝ} (hM : 0≤M)
    (hf : ∀ x : State N,OnSphere x → |f x|≤M) (z : State N) : |extension N f z|≤M := by
  by_cases hz : z=0
  · subst z
    rw [extension,cutoff_zero hN 0 (by simp;positivity),zero_mul,abs_zero]
    exact hM
  · have hs : OnSphere (normalize N z) := (onSphere_iff_norm_sq _).mpr (normalize_norm_sq z hz)
    rw [extension,abs_mul,abs_of_nonneg (cutoff_nonneg z)]
    exact (mul_le_mul_of_nonneg_left (hf _ hs) (cutoff_nonneg z)).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (cutoff_le_one z) hM)


 theorem extension_derivative_norm_le (hN : 0<N) {f : State N → ℝ}
    (hf : Differentiable ℝ f) {M L : ℝ} (hM : 0≤M) (hL : 0≤L)
    (hb : ∀ x : State N,OnSphere x → |f x|≤M)
    (hd : ∀ x v : State N,OnSphere x → ‖fderiv ℝ f x (projection x v)‖≤L*‖v‖)
    (z : State N) : ‖fderiv ℝ (extension N f) z‖≤8*(transitionBound : ℝ)*M/Real.sqrt N+2*L := by
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  have hs : 0<Real.sqrt N := Real.sqrt_pos.mpr hn
  by_cases hz : z=0
  · subst z
    rw [extension_fderiv_zero hN f,norm_zero]
    positivity
  have hnorm : 0<‖z‖ := norm_pos_iff.mpr hz
  have hSphere : OnSphere (normalize N z) := (onSphere_iff_norm_sq _).mpr (normalize_norm_sq z hz)
  have he (v : State N) : fderiv ℝ (extension N f) z v=
      f (normalize N z)*fderiv ℝ (cutoff N) z v+
        cutoff N z*fderiv ℝ f (normalize N z) (fderiv ℝ (normalize N) z v) := by
    have hh := (cutoff_hasFDerivAt z).mul ((hf _).hasFDerivAt.comp z (normalize_hasFDerivAt hN z hz))
    change fderiv ℝ (cutoff N * f ∘ normalize N) z v=_
    rw [hh.fderiv,(cutoff_hasFDerivAt z).fderiv,(normalize_hasFDerivAt hN z hz).fderiv]
    simp only [ContinuousLinearMap.add_apply,smul_apply,ContinuousLinearMap.comp_apply,smul_eq_mul,Function.comp_apply]
    ring
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hfirst : |f (normalize N z)*fderiv ℝ (cutoff N) z v|≤
      M*(8*(transitionBound : ℝ)/Real.sqrt N)*‖v‖ := by
    rw [abs_mul]
    have hc := (fderiv ℝ (cutoff N) z).le_opNorm v
    rw [Real.norm_eq_abs] at hc
    calc
      _ ≤ M*(‖fderiv ℝ (cutoff N) z‖*‖v‖) :=
        mul_le_mul (hb _ hSphere) hc (abs_nonneg _) hM
      _ ≤ M*((8*(transitionBound : ℝ)/Real.sqrt N)*‖v‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (cutoff_derivative_norm_le hN z) (norm_nonneg v)) hM
      _ = _ := by ring
  have hsecond : |cutoff N z*fderiv ℝ f (normalize N z) (fderiv ℝ (normalize N) z v)|≤2*L*‖v‖ := by
    by_cases hc : cutoff N z=0
    · rw [hc,zero_mul,abs_zero]
      positivity
    have hzz : (N : ℝ)/4<‖z‖^2 := by
      by_contra hh
      exact hc (cutoff_zero hN z (le_of_not_gt hh))
    have hratio : Real.sqrt N/‖z‖≤2 := by
      apply (div_le_iff₀ hnorm).mpr
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      rw [Real.sq_sqrt (Nat.cast_nonneg N)]
      nlinarith [hzz]
    rw [normalize_derivative_projected hN z v hz,abs_mul,abs_of_nonneg (cutoff_nonneg z)]
    have hfd : |fderiv ℝ f (normalize N z) ((Real.sqrt N/‖z‖) • projection (normalize N z) v)|≤
        2*L*‖v‖ := by
      rw [map_smul,smul_eq_mul,abs_mul,abs_of_nonneg (show 0≤Real.sqrt N/‖z‖ by positivity)]
      have hh := hd (normalize N z) v hSphere
      rw [Real.norm_eq_abs] at hh
      calc
        _ ≤ (Real.sqrt N/‖z‖)*(L*‖v‖) := mul_le_mul_of_nonneg_left hh (by positivity)
        _ ≤ 2*(L*‖v‖) := mul_le_mul_of_nonneg_right hratio (mul_nonneg hL (norm_nonneg v))
        _ = _ := by ring
    have hh := mul_le_mul_of_nonneg_left hfd (cutoff_nonneg z)
    exact hh.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (cutoff_le_one z) (show 0≤2*L*‖v‖ by positivity))
  rw [he,Real.norm_eq_abs]
  calc
    _ ≤ |f (normalize N z)*fderiv ℝ (cutoff N) z v|+
        |cutoff N z*fderiv ℝ f (normalize N z) (fderiv ℝ (normalize N) z v)| := abs_add_le _ _
    _ ≤ M*(8*(transitionBound : ℝ)/Real.sqrt N)*‖v‖+2*L*‖v‖ := add_le_add hfirst hsecond
    _ = _ := by ring

end SphericalAging.GaussianRadialCutoff
