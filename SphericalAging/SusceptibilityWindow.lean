module

public import SphericalAging.UniformResponseRows
public import SphericalAging.ForkParameterBounds

public section

/-! Actual finite-window response masses converge by the selected translated
response, and their source susceptibility formula is an exact change of variable. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.SusceptibilityWindow
open CKSpecification CKPhysicalConsequences GreenCovariance BackwardResponse
open CubicResponseLocalization ProfileCenterEnergy

@[expose] def windowMass (d : CKData) (t W : ℝ) : ℝ := ∫ τ in (0:ℝ)..W,d.R t (t-τ)

theorem windowMass_eq (d : CKData) (t W : ℝ) :
    windowMass d t W=susceptibility d t (t-W) := by
  unfold windowMass susceptibility
  simpa only [sub_zero] using intervalIntegral.integral_comp_sub_left (a:=0) (b:=W) (fun u => d.R t u) t

theorem windowMass_tendsto {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q) {W : ℝ} (hW : 0≤W) :
    Tendsto (fun t : ℝ => windowMass d t W) atTop (𝓝 (1-c W)) := by
  let F : ℝ → ℝ → ℝ := fun T τ => clampedResponse d (T+W) (T+W-τ)
  have hF (T : ℝ) : Continuous (F T) :=
    (clampedResponse_continuous h).comp (continuous_const.prodMk (continuous_const.sub continuous_id))
  have hp (τ : ℝ) (hτ : τ∈Icc (0:ℝ) W) :
      Tendsto (fun T => F T τ) atTop (𝓝 (r τ)) := by
    have hl := (H.translated_response W hW).tendsto_at
      (x:=(W,W-τ)) ⟨⟨hW,le_rfl⟩,⟨by linarith [hτ.2],by linarith [hτ.1]⟩⟩
    simp only [show W-(W-τ)=τ by ring] at hl
    apply hl.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    dsimp [F]
    rw [clampedResponse_eq (by linarith [hτ.2]) (by linarith [hτ.1])]
    congr 1
    ring
  have hi : Tendsto (fun T => ∫ τ in (0:ℝ)..W,F T τ) atTop (𝓝 (∫ τ in (0:ℝ)..W,r τ)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (1:ℝ))
    · exact Eventually.of_forall (fun T => (hF T).aestronglyMeasurable)
    · exact Eventually.of_forall (fun T => ae_of_all _ (fun τ _ => by
        have hh := response_correlation_bounds h (physical_bounds_of_equations h) (le_max_left (0:ℝ) (T+W-τ))
          (le_max_right (T+W) (max 0 (T+W-τ)))
        change ‖d.R (max (T+W) (max 0 (T+W-τ))) (max 0 (T+W-τ))‖≤1
        simpa only [Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2.1.trans hh.2.2))
    · exact intervalIntegrable_const
    · apply ae_of_all
      intro τ hτ
      rw [uIoc_of_le hW] at hτ
      exact hp τ (Ioc_subset_Icc_self hτ)
  rw [ForkParameterBounds.response_interval_mass (profile H) hW] at hi
  have hshift : Tendsto (fun t : ℝ => t-W) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-W) tendsto_id
  apply (hi.comp hshift).congr'
  filter_upwards [eventually_ge_atTop W] with t ht
  unfold windowMass
  apply intervalIntegral.integral_congr
  intro τ hτ
  rw [uIcc_of_le hW] at hτ
  dsimp [F]
  rw [sub_add_cancel,clampedResponse_eq (by linarith [hτ.2]) (by linarith [hτ.1])]

end SphericalAging.SusceptibilityWindow
