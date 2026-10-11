module

public import SphericalAging.StationaryAveragingRegularity
public import Mathlib.MeasureTheory.Group.IntegralConvolution

public section

/-! Genuine finite renewal iteration and disappearance of the bounded
negative-time remainder, proved by the actual exponential transform. -/
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SphericalAging.RenewalRemainder
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AbsorptionCutoff.Renewal StationaryAveragingRegularity

@[expose] def renewalAverage (μ : Measure ℝ) (F : ℝ → ℝ) (n : ℕ) (x : ℝ) :=
  ∫ s,F (x-s) ∂convPow μ n

theorem convPow_real_Iic_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (θ : ℝ) (hθ : 0<θ) (hTransform : expTransform θ μ<1) (b : ℝ) :
    Tendsto (fun n : ℕ => (convPow μ n).real (Iic b)) atTop (𝓝 0) := by
  have hTransformFinite : expTransform θ μ≠∞ := ne_of_lt (hTransform.trans (by simp))
  have hr : (expTransform θ μ).toReal<1 := by
    simpa only [ENNReal.toReal_one] using (ENNReal.toReal_lt_toReal hTransformFinite ENNReal.one_ne_top).mpr hTransform
  apply squeeze_zero _ _ (show Tendsto (fun n : ℕ => Real.exp (θ*b)*(expTransform θ μ).toReal^n) atTop (𝓝 0) from ?_)
  · intro n
    exact measureReal_nonneg
  · intro n
    have hb := measure_le_expTransform hθ (convPow μ n) measurableSet_Iic (Subset.refl (Iic b))
    rw [expTransform_convPow] at hb
    have ht : ENNReal.ofReal (Real.exp (θ*b))*expTransform θ μ^n≠∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hTransformFinite)
    have he := ENNReal.toReal_mono ht hb
    simpa only [measureReal_def,ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_pow] using he
  · simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one ENNReal.toReal_nonneg hr).const_mul (Real.exp (θ*b))

/-- The actual renewal remainder vanishes for each x. No random-walk law
of large numbers is postulated; a proved Chernoff estimate suffices. -/
theorem renewalAverage_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (θ : ℝ) (hθ : 0<θ) (hTransform : expTransform θ μ<1)
    (F : ℝ → ℝ) (hF : Measurable F) (M : ℝ) (hM : 0≤M) (hb : ∀ y,‖F y‖≤M)
    (hBot : Tendsto F atBot (𝓝 0)) (x : ℝ) :
    Tendsto (fun n : ℕ => renewalAverage μ F n x) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hδ : 0<ε/2 := by linarith
  have he := Metric.tendsto_nhds.mp hBot (ε/2) hδ
  obtain ⟨R,hR⟩ := eventually_atBot.mp he
  have hmass := (convPow_real_Iic_tendsto_zero μ θ hθ hTransform (x-R)).const_mul M
  have hmε : ∀ᶠ n : ℕ in atTop,M*(convPow μ n).real (Iic (x-R))<ε/2 := by
    exact (show Tendsto (fun n : ℕ => M*(convPow μ n).real (Iic (x-R))) atTop (𝓝 0) from
      by simpa only [mul_zero] using hmass).eventually (gt_mem_nhds hδ)
  filter_upwards [hmε] with n hn
  let ν := convPow μ n
  let G := fun s : ℝ => ε/2+M*(Iic (x-R)).indicator (fun _ => (1:ℝ)) s
  have hG : Integrable G ν :=
    (integrable_const (ε/2)).add (((integrable_const (1:ℝ)).indicator measurableSet_Iic).const_mul M)
  have hBound : ∀ᵐ s ∂ν,‖F (x-s)‖≤G s := by
    apply Eventually.of_forall
    intro s
    by_cases hs : s≤x-R
    · simp only [G,indicator_of_mem (show s∈Iic (x-R) from hs),mul_one]
      linarith [hb (x-s)]
    · have hs' : x-s≤R := by linarith
      have hh := (hR (x-s) hs').le
      simp only [dist_zero_right] at hh
      simp only [G,indicator_of_notMem (show s∉Iic (x-R) from hs),mul_zero,add_zero]
      exact hh
  have hI := norm_integral_le_of_norm_le hG hBound
  have hGI : (∫ s,G s ∂ν)=ε/2+M*ν.real (Iic (x-R)) := by
    dsimp [G]
    rw [integral_add (integrable_const _) (((integrable_const (1:ℝ)).indicator measurableSet_Iic).const_mul M),
      integral_const_mul,integral_indicator measurableSet_Iic,integral_const,integral_const]
    simp only [probReal_univ,one_smul,smul_eq_mul,mul_one,one_mul,measureReal_restrict_apply MeasurableSet.univ,univ_inter]
  rw [hGI] at hI
  change dist (renewalAverage μ F n x) 0<ε
  rw [dist_zero_right]
  exact hI.trans_lt (by dsimp [ν] at *; linarith)

/-- Actual convolution powers compose the causal averaging operators. -/
theorem renewalAverage_succ (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (F : ℝ → ℝ) (hF : Measurable F) (M : ℝ) (hb : ∀ y,‖F y‖≤M) (n : ℕ) (x : ℝ) :
    renewalAverage μ F (n+1) x=renewalAverage μ (fun y => renewalAverage μ F 1 y) n x := by
  have hi : Integrable (fun s => F (x-s)) (convPow μ n ∗ μ) := by
    rw [←convPow_succ]
    exact translatedAverage_integrable (convPow μ (n+1)) (fun s : ℝ => -s) F
      measurable_neg hF M hb x
  unfold renewalAverage
  rw [convPow_succ,integral_conv hi]
  simp only [convPow_one]
  apply integral_congr_ae
  exact Eventually.of_forall (fun s => by
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => by change F (x-(s+t))=F ((x-s)-t); rw [show x-(s+t)=(x-s)-t by ring]))

/-- Finite iteration of the actual equation f-Bf=g, with no representation
or asymptotic statement among the assumptions. -/
theorem finite_renewal_iteration (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (F G : ℝ → ℝ) (hF : Measurable F) (hG : Measurable G)
    (MF MG : ℝ) (hbF : ∀ y,‖F y‖≤MF) (hbG : ∀ y,‖G y‖≤MG)
    (hEq : ∀ x,F x-renewalAverage μ F 1 x=G x) (n : ℕ) (x : ℝ) :
    F x=(∑ j∈Finset.range n,renewalAverage μ G j x)+renewalAverage μ F n x := by
  have hstep (j : ℕ) : renewalAverage μ G j x=
      renewalAverage μ F j x-renewalAverage μ F (j+1) x := by
    rw [renewalAverage_succ μ F hF MF hbF j x]
    unfold renewalAverage
    have hComp : Integrable (fun s => renewalAverage μ F 1 (x-s)) (convPow μ j) := by
      have hm : Measurable (fun y => renewalAverage μ F 1 y) := by
        have hm := translatedAverage_measurable μ (fun s : ℝ => -s) F measurable_neg hF
        change Measurable (fun y : ℝ => ∫ s,F (y+(-s)) ∂μ) at hm
        simpa only [renewalAverage,convPow_one,sub_eq_add_neg] using hm
      have hBound : ∀ y,‖renewalAverage μ F 1 y‖≤MF := by
        intro y
        simpa only [renewalAverage,convPow_one,translatedAverage,sub_eq_add_neg] using translatedAverage_bound μ (fun s : ℝ => -s) F MF hbF y
      exact translatedAverage_integrable (convPow μ j) (fun s : ℝ => -s) _ measurable_neg hm MF hBound x
    have hFI : Integrable (fun s => F (x-s)) (convPow μ j) := by
      simpa only [sub_eq_add_neg] using translatedAverage_integrable (convPow μ j) (fun s : ℝ => -s) F measurable_neg hF MF hbF x
    change (∫ s,G (x-s) ∂convPow μ j)=
      (∫ s,F (x-s) ∂convPow μ j)-(∫ s,renewalAverage μ F 1 (x-s) ∂convPow μ j)
    rw [←integral_sub hFI hComp]
    apply integral_congr_ae
    exact Eventually.of_forall (fun s => (hEq (x-s)).symm)
  rw [Finset.sum_congr rfl (fun j _ => hstep j),Finset.sum_range_sub']
  simp only [renewalAverage,convPow_zero,integral_dirac,sub_zero]
  ring

end
end SphericalAging.RenewalRemainder
