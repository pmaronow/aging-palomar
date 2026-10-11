module

public import SphericalAging.WeightedSlowRatioTheorem
public import SphericalAging.ResponseTransport

public section

/-! The actual remote response budget and genuine CK-row transport inputs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.RemoteWeightedBudget
open CKSpecification CKPhysicalConsequences GreenCovariance EarlierCovariance
  WeightedResponseIdentities RecentWeightedResponseLimit WeightedSlowRatioTheorem
  GeneralCenterDeficit StrongBackwardDefect ResponseTransport

@[expose] def initialIntegrand (p : ℕ) (d : CKData) (t u : ℝ) : ℝ :=
  clampedCorrelation d t u^(p-1)*clampedResponse d t u

theorem initial_weighted_mass_tendsto {p : ℕ} {β S : ℝ} {d : CKData}
    (h : CKEquations p β d) (hS : 0≤S)
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => (p:ℝ)*(∫ u in (0:ℝ)..S,d.C t u^(p-1)*d.R t u))
      atTop (𝓝 0) := by
  have hi : Tendsto (fun t : ℝ => ∫ u in (0:ℝ)..S,initialIntegrand p d t u)
      atTop (𝓝 (∫ _u in (0:ℝ)..S,(0:ℝ))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (1:ℝ))
    · exact Eventually.of_forall (fun t =>
        (((clampedCorrelation_continuous h).comp (continuous_const.prodMk continuous_id)).pow
          (p-1) |>.mul ((clampedResponse_continuous h).comp
            (continuous_const.prodMk continuous_id))).aestronglyMeasurable)
    · exact Eventually.of_forall (fun t => ae_of_all _ (fun u _ => by
        have hb := recentIntegrand_bound h t (t-u)
        simpa only [recentIntegrand,initialIntegrand,sub_sub_cancel,Real.norm_eq_abs] using hb))
    · exact intervalIntegrable_const
    · apply ae_of_all
      intro u hu
      rw [uIoc_of_le hS] at hu
      have hr := response_fixed_wait_tendsto h (physical_bounds_of_equations h) hf hu.1.le
      have hh := ((hf u hu.1.le).pow (p-1)).mul hr
      simp only [mul_zero] at hh
      apply hh.congr'
      filter_upwards [eventually_ge_atTop S] with t ht
      unfold initialIntegrand
      rw [clampedCorrelation_eq (hS.trans ht) hu.1.le,clampedResponse_eq hu.1.le (hu.2.trans ht)]
  have hl := hi.const_mul (p:ℝ)
  simp only [intervalIntegral.integral_zero,mul_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_ge_atTop S] with t ht
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hS] at hu
  unfold initialIntegrand
  rw [clampedCorrelation_eq (hS.trans ht) hu.1,clampedResponse_eq hu.1 (hu.2.trans ht)]

theorem remote_weighted_budget_tendsto {p : ℕ} {β S L : ℝ} {d : CKData}
    {h : CKEquations p β d} {c r : ℝ → ℝ} {q : ℝ}
    (H : SelectedInputs h c r q) (hS : 0≤S) (hL : 0≤L)
    (hE : Tendsto (energy p β d) atTop (𝓝 (PlateauAlgebra.selectedEnergy p β q)))
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => (p:ℝ)*(∫ u in S..t-L,d.C t u^(p-1)*d.R t u))
      atTop (𝓝 (c L^p-defectBudget p q)) := by
  have hh := (oldWeightedMass_tendsto H hE hL).sub (initial_weighted_mass_tendsto h hS hf)
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (S+L)] with t ht
  have ht0 : 0≤t := by linarith
  have hc := ((correlation_row_continuous h ht0).pow (p-1)).mul (response_row_continuous h)
  have hI := (hc.mono (Icc_subset_Icc le_rfl (by linarith : S≤t))).intervalIntegrable_of_Icc (μ:=volume) hS
  have hJ := (hc.mono (Icc_subset_Icc hS (by linarith : t-L≤t))).intervalIntegrable_of_Icc (μ:=volume)
    (by linarith : S≤t-L)
  have he := intervalIntegral.integral_add_adjacent_intervals hI hJ
  unfold oldWeightedMass
  dsimp only [Pi.mul_apply,Pi.pow_apply] at he
  nlinarith

theorem correlation_row_ac {p : ℕ} {β t : ℝ} {d : CKData}
    (h : CKEquations p β d) (ht : 0≤t) : AbsolutelyContinuousOnInterval (d.C t) 0 t := by
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image (slope_row_continuous h |>.nnnorm)
  have hl : LipschitzOnWith B (d.C t) (Icc 0 t) :=
    (convex_Icc 0 t).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun u hu => correlation_earlier_hasDerivWithinAt h hu.1 hu.2)
      (fun u hu => hB ⟨u,hu,rfl⟩)
  rw [←uIcc_of_le ht] at hl
  exact hl.absolutelyContinuousOnInterval

end SphericalAging.RemoteWeightedBudget
