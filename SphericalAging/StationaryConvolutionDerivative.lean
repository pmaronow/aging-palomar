module

public import SphericalAging.StationaryShiftedProfiles
public import Mathlib.Analysis.Calculus.ParametricIntegral

public section

/-! Differentiating actual causal convolutions under local C1 hypotheses. -/

open Set MeasureTheory Filter
open scoped Topology

namespace SphericalAging.StationaryConvolutionDerivative
noncomputable section
open StationaryNormalization

/-- Fixed unit-interval representation, including time zero. -/
theorem causal_unit_interval (F G : ℝ → ℝ) (t : ℝ) :
    causalConvolution F G t = t * ∫ z in 0..1, F (t*(1-z))*G (t*z) := by
  have he := intervalIntegral.smul_integral_comp_mul_left (fun s => F (t-s)*G s) t (a:=0) (b:=1)
  simp only [smul_eq_mul,mul_zero,mul_one] at he
  unfold causalConvolution
  rw [← he]
  congr 1
  apply intervalIntegral.integral_congr
  intro z _
  change F (t-t*z)*G (t*z) = F (t*(1-z))*G (t*z)
  rw [show t-t*z=t*(1-z) by ring]

/-- Local C1 input data. The derivative functions are actual HasDerivAt
slopes, not conclusions about the convolution. -/
theorem continuousAt_scaled_one_sub (c z : ℝ) : ContinuousAt (fun w : ℝ => c*(1-w)) z := by fun_prop
theorem continuousAt_scaled (c z : ℝ) : ContinuousAt (fun w : ℝ => c*w) z := by fun_prop

structure C1Input (F F' : ℝ → ℝ) : Prop where
  derivative : ∀ x > -1, HasDerivAt F (F' x) x
  derivative_continuous : ContinuousOn F' (Ioi (-1))

theorem C1Input.continuousOn {F F' : ℝ → ℝ} (h : C1Input F F') :
    ContinuousOn F (Ioi (-1)) := by
  intro x hx
  exact (h.derivative x hx).continuousAt.continuousWithinAt

/-- The fixed-unit integral has its actual parameter derivative. -/
theorem unit_integral_hasDerivAt (F F' G G' : ℝ → ℝ)
    (hF : C1Input F F') (hG : C1Input G G') (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun x => ∫ z in 0..1, F (x*(1-z))*G (x*z))
      (∫ z in 0..1, F' (t*(1-z))*(1-z)*G (t*z)+F (t*(1-z))*G' (t*z)*z) t := by
  let K := Icc (-1/2:ℝ) (t+1)
  have hKsub : K ⊆ Ioi (-1) := by intro x hx; dsimp [K] at hx; change -1 < x; linarith [hx.1]
  have hcontF := hF.continuousOn.mono hKsub
  have hcontG := hG.continuousOn.mono hKsub
  have hcontF' := hF.derivative_continuous.mono hKsub
  have hcontG' := hG.derivative_continuous.mono hKsub
  obtain ⟨AF,hAF⟩ := isCompact_Icc.bddAbove_image hcontF.abs
  obtain ⟨AG,hAG⟩ := isCompact_Icc.bddAbove_image hcontG.abs
  obtain ⟨AF',hAF'⟩ := isCompact_Icc.bddAbove_image hcontF'.abs
  obtain ⟨AG',hAG'⟩ := isCompact_Icc.bddAbove_image hcontG'.abs
  let C := (max AF' 0)*(max AG 0)+(max AF 0)*(max AG' 0)
  let μ := volume.restrict (Ioc (0:ℝ) 1)
  let H := fun x z : ℝ => F (x*(1-z))*G (x*z)
  let H' := fun x z : ℝ => F' (x*(1-z))*(1-z)*G (x*z)+F (x*(1-z))*G' (x*z)*z
  have hargs (x z : ℝ) (hx : x ∈ Ioo (t-1/2) (t+1/2)) (hz : z ∈ Icc (0:ℝ) 1) :
      x*(1-z) ∈ K ∧ x*z ∈ K := by
    have hxx : -1/2 < x ∧ x < t+1 := by constructor <;> linarith [hx.1,hx.2]
    have hz0 := hz.1
    have hz1 := hz.2
    have hm0 : 0 ≤ 1-z := by linarith
    have hm1 : 1-z ≤ 1 := by linarith
    have lower (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : -1/2 ≤ x*y := by
      by_cases hxp : 0 ≤ x
      · nlinarith
      · have hxy := mul_le_mul_of_nonpos_left hy1 (le_of_not_ge hxp)
        nlinarith
    have upper (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : x*y ≤ t+1 := by
      by_cases hxp : 0 ≤ x
      · nlinarith [mul_le_mul_of_nonneg_left hy1 hxp]
      · have hxy := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hxp) hy0
        linarith
    exact ⟨⟨lower (1-z) hm0 hm1,upper (1-z) hm0 hm1⟩,⟨lower z hz0 hz1,upper z hz0 hz1⟩⟩
  have hderiv (x z : ℝ) (hx : x ∈ Ioo (t-1/2) (t+1/2)) (hz : z ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun x => H x z) (H' x z) x := by
    obtain ⟨hleft,hright⟩ := hargs x z hx hz
    have hd := ((hF.derivative _ (hKsub hleft)).comp x ((hasDerivAt_id x).mul_const (1-z))).mul
      ((hG.derivative _ (hKsub hright)).comp x ((hasDerivAt_id x).mul_const z))
    convert hd using 1
    · rfl
    · simp only [H', Function.comp_apply,id_eq,one_mul]
      ring
  have hbound : ∀ᵐ z ∂μ, ∀ x ∈ Ioo (t-1/2) (t+1/2), ‖H' x z‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    intro x hx
    obtain ⟨hl,hr⟩ := hargs x z hx ⟨hz.1.le,hz.2⟩
    have hf := (hAF ⟨_,hl,rfl⟩).trans (le_max_left AF 0)
    have hg := (hAG ⟨_,hr,rfl⟩).trans (le_max_left AG 0)
    have hf' := (hAF' ⟨_,hl,rfl⟩).trans (le_max_left AF' 0)
    have hg' := (hAG' ⟨_,hr,rfl⟩).trans (le_max_left AG' 0)
    have hzabs : |z| ≤ 1 := by rw [abs_of_nonneg hz.1.le]; exact hz.2
    have h1abs : |1-z| ≤ 1 := by rw [abs_of_nonneg (by linarith [hz.2] : 0 ≤ 1-z)]; linarith [hz.1]
    dsimp [H',C]
    calc
      _ ≤ |F' (x*(1-z))| *|1-z| *|G (x*z)|+|F (x*(1-z))| *|G' (x*z)| *|z| := by
        simpa only [abs_mul] using abs_add_le (F' (x*(1-z))*(1-z)*G (x*z)) (F (x*(1-z))*G' (x*z)*z)
      _ ≤ _ := by
        have h1 := mul_le_mul (mul_le_mul hf' h1abs (abs_nonneg _) (by positivity)) hg (abs_nonneg _) (by positivity)
        have h2 := mul_le_mul (mul_le_mul hf hg' (abs_nonneg _) (by positivity)) hzabs (abs_nonneg _) (by positivity)
        simpa only [mul_one] using add_le_add h1 h2
  have hHt : ContinuousOn (H t) (Icc (0:ℝ) 1) := by
    intro z hz
    obtain ⟨hl,hr⟩ := hargs t z (by constructor <;> linarith) hz
    exact (((hF.derivative _ (hKsub hl)).continuousAt.comp_of_eq (continuousAt_scaled_one_sub t z) rfl).mul
      ((hG.derivative _ (hKsub hr)).continuousAt.comp_of_eq (continuousAt_scaled t z) rfl)).continuousWithinAt
  have hH't : ContinuousOn (H' t) (Icc (0:ℝ) 1) := by
    have hx : ContinuousOn (fun z : ℝ => t*(1-z)) (Icc 0 1) := by fun_prop
    have hy : ContinuousOn (fun z : ℝ => t*z) (Icc 0 1) := by fun_prop
    have hl : MapsTo (fun z : ℝ => t*(1-z)) (Icc 0 1) K := fun z hz => (hargs t z (by constructor <;> linarith) hz).1
    have hr : MapsTo (fun z : ℝ => t*z) (Icc 0 1) K := fun z hz => (hargs t z (by constructor <;> linarith) hz).2
    exact (((hcontF'.comp hx hl).mul (by fun_prop)).mul (hcontG.comp hy hr)).add
      (((hcontF.comp hx hl).mul (hcontG'.comp hy hr)).mul (by fun_prop))
  have hmeas : ∀ᶠ x in 𝓝 t, AEStronglyMeasurable (H x) μ := by
    filter_upwards [Ioo_mem_nhds (by linarith : t-1/2 < t) (by linarith : t < t+1/2)] with x hx
    apply ContinuousOn.aestronglyMeasurable (s := Ioc 0 1) _ measurableSet_Ioc
    intro z hz
    obtain ⟨hl,hr⟩ := hargs x z hx ⟨hz.1.le,hz.2⟩
    exact (((hF.derivative _ (hKsub hl)).continuousAt.comp_of_eq (continuousAt_scaled_one_sub x z) rfl).mul
      ((hG.derivative _ (hKsub hr)).continuousAt.comp_of_eq (continuousAt_scaled x z) rfl)).continuousWithinAt
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=μ) (F:=H) (F':=H') (bound:=fun _ => C)
    (Ioo_mem_nhds (by linarith : t-1/2 < t) (by linarith : t < t+1/2))
    hmeas (hHt.intervalIntegrable_of_Icc (μ:=volume) (by norm_num)).1
    ((hH't.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    hbound (integrable_const C)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz; exact fun x hx => hderiv x z hx ⟨hz.1.le,hz.2⟩)
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] using hd.2


theorem C1Input.derivative_continuousAt {F F' : ℝ → ℝ} (h : C1Input F F') (x : ℝ) (hx : -1 < x) :
    ContinuousAt F' x :=
  h.derivative_continuous.continuousAt (Ioi_mem_nhds hx)

/-- Actual C1 causal convolution derivative, including t=0. -/
theorem causal_convolution_hasDerivAt (F F' G G' : ℝ → ℝ)
    (hF : C1Input F F') (hG : C1Input G G') (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (causalConvolution F G) (F t*G 0+causalConvolution F G' t) t := by
  let A := fun z : ℝ => (1-z)*F (t*(1-z))*G (t*z)
  let A' := fun z : ℝ => -F (t*(1-z))*G (t*z)-t*(1-z)*F' (t*(1-z))*G (t*z)+t*(1-z)*F (t*(1-z))*G' (t*z)
  let H := fun z : ℝ => F (t*(1-z))*G (t*z)
  let H' := fun z : ℝ => F' (t*(1-z))*(1-z)*G (t*z)+F (t*(1-z))*G' (t*z)*z
  let J := fun z : ℝ => F (t*(1-z))*G' (t*z)
  have hargs (z : ℝ) (hz : z ∈ Icc (0:ℝ) 1) : -1 < t*(1-z) ∧ -1 < t*z := by
    constructor <;> nlinarith [hz.1,hz.2]
  have hderiv (z : ℝ) (hz : z ∈ Icc (0:ℝ) 1) : HasDerivAt A (A' z) z := by
    obtain ⟨hl,hr⟩ := hargs z hz
    have hd := (((hasDerivAt_id z).const_sub 1).mul
      ((hF.derivative _ hl).comp z ((hasDerivAt_id z).const_sub 1 |>.const_mul t))).mul
      ((hG.derivative _ hr).comp z ((hasDerivAt_id z).const_mul t))
    convert hd using 1
    · rfl
    · simp only [A',Function.comp_apply,id_eq,Pi.mul_apply]
      ring
  have hcontH : ContinuousOn H (Icc (0:ℝ) 1) := by
    intro z hz
    obtain ⟨hl,hr⟩ := hargs z hz
    have hcF := (hF.derivative _ hl).continuousAt.comp_of_eq (continuousAt_scaled_one_sub t z) rfl
    have hcG := (hG.derivative _ hr).continuousAt.comp_of_eq (continuousAt_scaled t z) rfl
    exact (hcF.mul hcG).continuousWithinAt
  have hcontH' : ContinuousOn H' (Icc (0:ℝ) 1) := by
    intro z hz
    obtain ⟨hl,hr⟩ := hargs z hz
    have hcF := (hF.derivative _ hl).continuousAt.comp_of_eq (continuousAt_scaled_one_sub t z) rfl
    have hcG := (hG.derivative _ hr).continuousAt.comp_of_eq (continuousAt_scaled t z) rfl
    have hcF' := (hF.derivative_continuousAt _ hl).comp_of_eq (continuousAt_scaled_one_sub t z) rfl
    have hcG' := (hG.derivative_continuousAt _ hr).comp_of_eq (continuousAt_scaled t z) rfl
    exact (((hcF'.mul (continuousAt_const.sub continuousAt_id)).mul hcG).add
      ((hcF.mul hcG').mul continuousAt_id)).continuousWithinAt
  have hcontJ : ContinuousOn J (Icc (0:ℝ) 1) := by
    intro z hz
    obtain ⟨hl,hr⟩ := hargs z hz
    exact (((hF.derivative _ hl).continuousAt.comp_of_eq (continuousAt_scaled_one_sub t z) rfl).mul
      ((hG.derivative_continuousAt _ hr).comp_of_eq (continuousAt_scaled t z) rfl)).continuousWithinAt
  have hAP : ∀ z, A' z = -H z-t*H' z+t*J z := by
    intro z
    dsimp [A',H,H',J]
    ring
  have hAI : IntervalIntegrable A' volume 0 1 := by
    have hi : IntervalIntegrable ((-H - fun z => t*H' z) + fun z => t*J z) volume 0 1 := ((hcontH.neg.sub (hcontH'.const_mul t)).add (hcontJ.const_mul t)).intervalIntegrable_of_Icc (μ:=volume) (by norm_num)
    convert hi using 1
    funext z
    exact hAP z
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun z hz => hderiv z (by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hz)) hAI
  have hIA : (∫ z in 0..1, A' z) = -(∫ z in 0..1, H z)-t*(∫ z in 0..1, H' z)+t*(∫ z in 0..1, J z) := by
    simp_rw [hAP]
    have hN : IntervalIntegrable (fun z => -H z-t*H' z) volume 0 1 := by
      convert ((hcontH.neg.sub (hcontH'.const_mul t)).intervalIntegrable_of_Icc (μ:=volume) (by norm_num)) using 1
    rw [intervalIntegral.integral_add hN ((hcontJ.const_mul t).intervalIntegrable_of_Icc (μ:=volume) (by norm_num))]
    have hNeg : IntervalIntegrable (fun z => -H z) volume 0 1 := by
      convert hcontH.neg.intervalIntegrable_of_Icc (μ:=volume) (by norm_num) using 1
    rw [intervalIntegral.integral_sub hNeg ((hcontH'.const_mul t).intervalIntegrable_of_Icc (μ:=volume) (by norm_num)),
      intervalIntegral.integral_neg,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have hFTC' : (∫ z in 0..1,H z)+t*(∫ z in 0..1,H' z) = F t*G 0+t*(∫ z in 0..1,J z) := by
    rw [hIA] at hFTC
    dsimp [A] at hFTC
    simp only [sub_self,zero_mul,mul_zero,sub_zero,mul_one,one_mul] at hFTC
    linarith
  have hd := (hasDerivAt_id t).mul (unit_integral_hasDerivAt F F' G G' hF hG t ht)
  have hd' : HasDerivAt (fun x => x*∫ z in 0..1,F (x*(1-z))*G (x*z))
      (F t*G 0+causalConvolution F G' t) t := by
    convert hd using 1
    · rfl
    · rw [causal_unit_interval]
      change F t*G 0+t*(∫ z in 0..1,J z) = 1*(∫ z in 0..1,H z)+t*(∫ z in 0..1,H' z)
      simpa only [one_mul] using hFTC'.symm
  exact hd'.congr_of_eventuallyEq (Filter.Eventually.of_forall (causal_unit_interval F G))


/-- The manuscript's corrected profiles satisfy the genuine local C1 input. -/
theorem correctedPower_c1 (a ε : ℝ) : C1Input (StationaryPowerProfiles.correctedPower a ε)
    (deriv (StationaryPowerProfiles.correctedPower a ε)) := by
  open StationaryPowerProfiles in
  have hg : ContDiffOn ℝ 1 (shiftedPower a) (Ioi (-1)) := by
    have hc : ContDiffOn ℝ 1 (fun t : ℝ => 1+t) (Ioi (-1)) := (contDiff_const.add contDiff_id).contDiffOn
    exact hc.rpow_const_of_ne (fun t ht => by change -1<t at ht; linarith)
  have hf : ContDiffOn ℝ 1 (correctedPower a ε) (Ioi (-1)) :=
    (contDiffOn_const.mul hg).sub (contDiffOn_const.mul (hg.pow 2))
  exact ⟨fun t ht => (correctedPower_hasDerivAt a ε t ht).differentiableAt.hasDerivAt,
    hf.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)⟩

/-- All natural powers of the corrected profile have actual local C1 data. -/
theorem correctedPower_pow_c1 (a ε : ℝ) (j : ℕ) :
    C1Input (fun s => StationaryPowerProfiles.correctedPower a ε s^j)
      (deriv (fun s => StationaryPowerProfiles.correctedPower a ε s^j)) := by
  have h := correctedPower_c1 a ε
  refine ⟨fun t ht => ((h.derivative t ht).pow j).differentiableAt.hasDerivAt,?_⟩
  intro t ht
  have heq : deriv (fun s => StationaryPowerProfiles.correctedPower a ε s^j) =ᶠ[𝓝 t]
      (fun s => (j:ℝ)*StationaryPowerProfiles.correctedPower a ε s^(j-1)*
        deriv (StationaryPowerProfiles.correctedPower a ε) s) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact ((h.derivative s hs).pow j).deriv
  have hcF := (h.derivative t ht).continuousAt
  have hcF' := h.derivative_continuousAt t ht
  exact (((continuousAt_const.mul (hcF.pow (j-1))).mul hcF').congr_of_eventuallyEq heq).continuousWithinAt

/-- This is the actual derivative identity used in the ideal residual expansion. -/
theorem corrected_power_convolution_derivative_identity (a ε t : ℝ) (j : ℕ) (ht : 0 ≤ t) :
    deriv (causalConvolution (fun s => StationaryPowerProfiles.correctedPower a ε s^j)
      (StationaryPowerProfiles.correctedPower a ε)) t =
      StationaryPowerProfiles.correctedPower a ε t^j +
        causalConvolution (fun s => StationaryPowerProfiles.correctedPower a ε s^j)
          (deriv (StationaryPowerProfiles.correctedPower a ε)) t := by
  rw [(causal_convolution_hasDerivAt _ _ _ _ (correctedPower_pow_c1 a ε j) (correctedPower_c1 a ε) t ht).deriv,
    StationaryPowerProfiles.correctedPower_zero,mul_one]

end
end SphericalAging.StationaryConvolutionDerivative
