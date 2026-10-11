module

public import SphericalAging.GaussianSphereDirection
public import SphericalAging.HamiltonianBallBounds
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul

public section

/-! Genuine Gaussian seed normalization, Holder, and expectation comparison
for algorithms which may depend on their Gaussian seed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.GaussianSeedOverlapBounds
open Set MeasureTheory ProbabilityTheory FiniteModel SphereInitialLaw
  GaussianSphereDirection HamiltonianBallBounds
open scoped InnerProductSpace ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem probability_power_mean_le {f : Ω→ℝ} (hf : AEStronglyMeasurable f P)
    (hb : ∀ᵐω ∂P,f ω∈Icc (0:ℝ) 1) (p : ℕ) :
    Integrable f P ∧ Integrable (fun ω => f ω^p) P ∧
      (∫ω,f ω ∂P)^p≤∫ω,f ω^p ∂P := by
  have hi : Integrable f P := (integrable_const (1:ℝ)).mono' hf (by
    filter_upwards [hb] with ω hω
    rw [Real.norm_of_nonneg hω.1]
    exact hω.2)
  have hip : Integrable (fun ω => f ω^p) P := (integrable_const (1:ℝ)).mono' (hf.pow p) (by
    filter_upwards [hb] with ω hω
    rw [Real.norm_of_nonneg (pow_nonneg hω.1 _)]
    exact pow_le_one₀ hω.1 hω.2)
  refine ⟨hi,hip,?_⟩
  exact (convexOn_pow p).map_integral_le (by fun_prop) isClosed_Ici
    (hb.mono fun _ hω => hω.1) hi hip

theorem sphere_overlap_power_mean_le {N : ℕ} (hN : 0<N) {A G : Ω→Vector N}
    (hA : AEStronglyMeasurable A P) (hG : AEStronglyMeasurable G P)
    (hball : ∀ᵐω ∂P,‖A ω‖≤Real.sqrt N) (p : ℕ) :
    Integrable (fun ω => |inner ℝ (A ω) (direction N hN (G ω))/(N:ℝ)|) P ∧
    Integrable (fun ω => |inner ℝ (A ω) (direction N hN (G ω))/(N:ℝ)|^p) P ∧
    (∫ω,|inner ℝ (A ω) (direction N hN (G ω))/(N:ℝ)| ∂P)^p≤
      ∫ω,|inner ℝ (A ω) (direction N hN (G ω))/(N:ℝ)|^p ∂P := by
  have hw := ((direction_measurable hN).comp_aemeasurable hG.aemeasurable).aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun ω => |inner ℝ (A ω) (direction N hN (G ω))/(N:ℝ)|) P := by
    simpa only [Function.comp_def,div_eq_mul_inv,Real.norm_eq_abs] using ((hA.inner hw).mul_const (N:ℝ)⁻¹).norm
  apply probability_power_mean_le hm _ p
  filter_upwards [hball] with ω hω
  refine ⟨abs_nonneg _,?_⟩
  rw [real_inner_comm]
  exact overlap_abs_le_one hN _ _ (direction_norm hN _) hω

theorem gaussian_seed_mean_comparison {N : ℕ} (hN : 0<N) {A G : Ω→Vector N}
    (hA : AEStronglyMeasurable A P) (hG : HasLaw G (gaussianLaw N) P)
    (hball : ∀ᵐω ∂P,‖A ω‖≤Real.sqrt N) :
    Integrable (fun ω => |inner ℝ (A ω) (G ω)/(N:ℝ)|) P ∧
    (∫ω,|inner ℝ (A ω) (G ω)/(N:ℝ)| ∂P)≤
      (∫ω,|inner ℝ (A ω) (direction N hN (G ω))/(N:ℝ)| ∂P)+
        Real.sqrt (Real.pi^2/(2*(N:ℝ))) := by
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hr : 0<Real.sqrt N := Real.sqrt_pos.mpr hn
  have hGmeas : AEStronglyMeasurable G P := hG.aemeasurable.aestronglyMeasurable
  have hw := ((direction_measurable hN).comp_aemeasurable hG.aemeasurable).aestronglyMeasurable
  have hsphere := sphere_overlap_power_mean_le hN hA hGmeas hball 1
  have hrad := radial_error_mean_le hN
  have hradInt : Integrable (fun ω => ‖G ω-direction N hN (G ω)‖/Real.sqrt N) P :=
    hG.integrable_comp hrad.1
  have hradMean : (∫ω,‖G ω-direction N hN (G ω)‖/Real.sqrt N ∂P)≤
      Real.sqrt (Real.pi^2/(2*(N:ℝ))) := by
    have he := hG.integral_comp hrad.1.aestronglyMeasurable
    have he' : (∫ω,‖G ω-direction N hN (G ω)‖/Real.sqrt N ∂P)=
        ∫x : Vector N,‖x-direction N hN x‖/Real.sqrt N ∂gaussianLaw N := by
      simpa only [Function.comp_def] using he
    exact he'.trans_le hrad.2
  have hbound : ∀ᵐω ∂P,|inner ℝ (A ω) (G ω)/(N:ℝ)|≤
      |inner ℝ (A ω) (direction N hN (G ω))/(N:ℝ)|+
        ‖G ω-direction N hN (G ω)‖/Real.sqrt N := by
    filter_upwards [hball] with ω hω
    have he : inner ℝ (A ω) (G ω)=inner ℝ (A ω) (direction N hN (G ω))+
        inner ℝ (A ω) (G ω-direction N hN (G ω)) := by rw [inner_sub_right];ring
    have hh := (abs_real_inner_le_norm (A ω) (G ω-direction N hN (G ω))).trans
      (mul_le_mul_of_nonneg_right hω (norm_nonneg _))
    have hdiff : |inner ℝ (A ω) (G ω-direction N hN (G ω))|/(N:ℝ)≤
        ‖G ω-direction N hN (G ω)‖/Real.sqrt N := by
      apply (div_le_iff₀ hn).mpr
      have heN : (‖G ω-direction N hN (G ω)‖/Real.sqrt N)*(N:ℝ)=
          Real.sqrt N*‖G ω-direction N hN (G ω)‖ := by
        calc
          _ = (‖G ω-direction N hN (G ω)‖/Real.sqrt N)*(Real.sqrt N*Real.sqrt N) := by
            rw [Real.mul_self_sqrt hn.le]
          _ = _ := by field_simp
      rw [heN]
      exact hh
    rw [abs_div,abs_of_pos hn,he]
    have hadd := div_le_div_of_nonneg_right (abs_add_le
      (inner ℝ (A ω) (direction N hN (G ω)))
      (inner ℝ (A ω) (G ω-direction N hN (G ω)))) hn.le
    rw [add_div] at hadd
    have hnabs : |inner ℝ (A ω) (direction N hN (G ω))/(N:ℝ)|=
        |inner ℝ (A ω) (direction N hN (G ω))|/(N:ℝ) := by rw [abs_div,abs_of_pos hn]
    rw [hnabs]
    exact hadd.trans (add_le_add le_rfl hdiff)
  have hi : Integrable (fun ω => |inner ℝ (A ω) (G ω)/(N:ℝ)|) P := by
    have hm : AEStronglyMeasurable (fun ω => |inner ℝ (A ω) (G ω)/(N:ℝ)|) P := by
      simpa only [div_eq_mul_inv,Real.norm_eq_abs] using ((hA.inner hGmeas).mul_const (N:ℝ)⁻¹).norm
    apply (hsphere.1.add hradInt).mono' hm
    filter_upwards [hbound] with ω hω
    simpa only [Real.norm_eq_abs,abs_abs,Pi.add_apply] using hω
  refine ⟨hi,?_⟩
  have hh := integral_mono_ae (f := fun ω => |inner ℝ (A ω) (G ω)/(N:ℝ)|)
    (g := fun ω => |inner ℝ (A ω) (direction N hN (G ω))/(N:ℝ)|+
      ‖G ω-direction N hN (G ω)‖/Real.sqrt N) hi (hsphere.1.add hradInt) hbound
  rw [integral_add (f := fun ω => |inner ℝ (A ω) (direction N hN (G ω))/(N:ℝ)|)
    (g := fun ω => ‖G ω-direction N hN (G ω)‖/Real.sqrt N) hsphere.1 hradInt] at hh
  exact hh.trans (add_le_add le_rfl hradMean)

end SphericalAging.GaussianSeedOverlapBounds
