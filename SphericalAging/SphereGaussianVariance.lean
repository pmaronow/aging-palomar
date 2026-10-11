module

public import SphericalAging.GaussianRadialCutoff

public section

/-! A genuine variance estimate under the literal normalized-Gaussian
sphere law. The proof uses a smooth radial extension, Gaussian rotation
variance, and a derived small-radius probability bound. It needs no
sphere Poincaré or spectral-gap premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace BigOperators NNReal ENNReal
namespace SphericalAging.SphereGaussianVariance
open HardSphereDynamics SphereInitialLaw GaussianRadialCutoff
set_option maxHeartbeats 1900000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

@[expose]  def sphereVarianceConstant : ℝ := (32*(transitionBound : ℝ)^2+4)*Real.pi^2
 lemma sphereVarianceConstant_nonneg : 0≤sphereVarianceConstant := by unfold sphereVarianceConstant;positivity

 lemma variance_le_center_sq {E : Type*} [MeasurableSpace E] {μ : Measure E}
    [IsProbabilityMeasure μ] {f : E → ℝ} (hf : AEStronglyMeasurable f μ) (c : ℝ) :
    variance f μ≤∫ z,(f z-c)^2 ∂μ := by
  have hh := variance_le_expectation_sq (hf.sub (aestronglyMeasurable_const (b := c)))
  change variance (fun z => f z-c) μ≤∫ z,(f z-c)^2 ∂μ at hh
  rw [variance_sub_const hf c] at hh
  exact hh

 theorem sphere_variance_le_tangent (hN : 0<N) {f : State N → ℝ}
    (hf : Differentiable ℝ f) {M L : ℝ} (hM : 0≤M) (hL : 0≤L)
    (hb : ∀ x : State N,OnSphere x → |f x|≤M)
    (hd : ∀ x v : State N,OnSphere x → ‖fderiv ℝ f x (projection x v)‖≤L*‖v‖) :
    variance f (sphereLaw N)≤2*Real.pi^2*L^2+sphereVarianceConstant*M^2/(N : ℝ) := by
  let γ := stdGaussian (State N)
  let g : State N → ℝ := f ∘ normalize N
  let F := extension N f
  let A := 8*(transitionBound : ℝ)*M/Real.sqrt N+2*L
  let bad : Set (State N) := {z | ‖z‖^2<(N : ℝ)/2}
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  have hs : 0<Real.sqrt N := Real.sqrt_pos.mpr hn
  have hA : 0≤A := by dsimp [A];positivity
  have hbad : MeasurableSet bad := (isOpen_lt (continuous_norm.pow 2) continuous_const).measurableSet
  have hgm : StronglyMeasurable g := hf.continuous.stronglyMeasurable.comp_measurable (normalize_measurable N)
  have hgd : ∀ᵐ z ∂γ,|g z|≤M := by
    filter_upwards [gaussian_ne_zero_ae (Nat.succ_le_iff.mpr hN)] with z hz
    exact hb _ ((onSphere_iff_norm_sq _).mpr (normalize_norm_sq z hz))
  have h2g : MemLp g 2 γ := MemLp.of_bound hgm.aestronglyMeasurable M
    (hgd.mono (fun z hz => by simpa only [Real.norm_eq_abs] using hz))
  have hFd : Differentiable ℝ F := extension_differentiable hN hf
  have hFm : StronglyMeasurable F := hFd.continuous.stronglyMeasurable
  have h2F : MemLp F 2 γ := MemLp.of_bound hFm.aestronglyMeasurable M
    (.of_forall (fun z => by simpa only [Real.norm_eq_abs] using extension_abs_le hN hM hb z))
  have hgradm : StronglyMeasurable (fun z => ‖fderiv ℝ F z‖^2) := (measurable_fderiv ℝ F).stronglyMeasurable.norm.pow 2
  have hgradbound (z : State N) : ‖fderiv ℝ F z‖^2≤A^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (extension_derivative_norm_le hN hf hM hL hb hd z) 2
  have hgradi : Integrable (fun z => ‖fderiv ℝ F z‖^2) γ := by
    apply (integrable_const (A^2)).mono' hgradm.aestronglyMeasurable
    exact .of_forall (fun z => by rw [Real.norm_of_nonneg (sq_nonneg _)];exact hgradbound z)
  have hvarF : variance F γ≤(Real.pi^2/8)*A^2 := by
    refine (DifferentiableGaussianVariance.gaussian_variance_le_gradient hFd h2F hgradi).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hh := integral_mono hgradi (integrable_const (A^2)) hgradbound
    simpa only [integral_const,probReal_univ,one_smul] using hh
  have hδi : Integrable (fun z => (g z-F z)^2) γ := (h2g.sub h2F).integrable_sq
  have hδbound : ∀ᵐ z ∂γ,(g z-F z)^2≤bad.indicator (fun _ => M^2) z := by
    filter_upwards [hgd] with z hz
    by_cases hzb : z∈bad
    · rw [indicator_of_mem hzb]
      have hc0 := cutoff_nonneg z
      have hc1 := cutoff_le_one z
      have hab : |g z-F z|≤M := by
        change |g z-cutoff N z*g z|≤M
        rw [← one_sub_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr hc1)]
        exact (mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr hc1)).trans (by nlinarith)
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).mpr hab
    · have hc : cutoff N z=1 := cutoff_one hN z (le_of_not_gt hzb)
      rw [indicator_of_notMem hzb]
      change (g z-cutoff N z*g z)^2≤0
      rw [hc,one_mul,sub_self,zero_pow (by norm_num : (2 : ℕ)≠0)]
  have hδ : (∫ z,(g z-F z)^2 ∂γ)≤M^2*γ.real bad := by
    have hh := integral_mono_ae hδi ((integrable_const (M^2)).indicator hbad) hδbound
    rw [integral_indicator_const _ hbad] at hh
    simpa only [smul_eq_mul,mul_comm] using hh
  have hprob : γ.real bad≤2*Real.pi^2/(N : ℝ) := by
    have hh := GaussianRadiusVariance.small_radius_probability_le (E := State N) (by simpa using hN)
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using hh
  have hvar : variance g γ≤2*variance F γ+2*(∫ z,(g z-F z)^2 ∂γ) := by
    let c := ∫ z,F z ∂γ
    have hcg : Integrable (fun z => (g z-c)^2) γ := (h2g.sub (memLp_const c)).integrable_sq
    have hcF : Integrable (fun z => (F z-c)^2) γ := (h2F.sub (memLp_const c)).integrable_sq
    have hpoint (z : State N) : (g z-c)^2≤2*(F z-c)^2+2*(g z-F z)^2 := by
      nlinarith [sq_nonneg (F z-c-(g z-F z))]
    have hh := integral_mono hcg ((hcF.const_mul 2).add (hδi.const_mul 2)) hpoint
    change (∫ z,(g z-c)^2 ∂γ)≤∫ z,2*(F z-c)^2+2*(g z-F z)^2 ∂γ at hh
    rw [integral_add (hcF.const_mul 2) (hδi.const_mul 2),integral_const_mul,integral_const_mul] at hh
    have he : (∫ z,(F z-c)^2 ∂γ)=variance F γ := (variance_eq_integral hFm.measurable.aemeasurable).symm
    rw [he] at hh
    exact (variance_le_center_sq hgm.aestronglyMeasurable c).trans hh
  have hv : variance f (sphereLaw N)=variance g γ := by
    rw [sphereLaw,gaussianLaw,variance_map hf.continuous.measurable.aemeasurable (normalize_measurable N).aemeasurable]
  rw [hv]
  have hfinal := hvar.trans (add_le_add (mul_le_mul_of_nonneg_left hvarF (by norm_num))
    (mul_le_mul_of_nonneg_left (hδ.trans (mul_le_mul_of_nonneg_left hprob (sq_nonneg M))) (by norm_num)))
  have hAsq : A^2≤128*(transitionBound : ℝ)^2*M^2/(N : ℝ)+8*L^2 := by
    have hsquare := Real.sq_sqrt (Nat.cast_nonneg N)
    have hh : A^2≤2*(8*(transitionBound : ℝ)*M/Real.sqrt N)^2+2*(2*L)^2 := by
      dsimp [A]
      nlinarith [sq_nonneg (8*(transitionBound : ℝ)*M/Real.sqrt N-2*L)]
    refine hh.trans_eq ?_
    rw [div_pow,hsquare]
    ring
  calc
    _ ≤ 2*((Real.pi^2/8)*A^2)+2*(M^2*(2*Real.pi^2/(N : ℝ))) := hfinal
    _ ≤ 2*((Real.pi^2/8)*(128*(transitionBound : ℝ)^2*M^2/(N : ℝ)+8*L^2))+
        2*(M^2*(2*Real.pi^2/(N : ℝ))) :=
      add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAsq (by positivity)) (by norm_num)) le_rfl
    _ = _ := by unfold sphereVarianceConstant;ring

end SphericalAging.SphereGaussianVariance
