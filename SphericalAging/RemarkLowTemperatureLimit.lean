module

public import SphericalAging.RemarkLowTemperatureAlgebra

public section

/-! The three limits in Remark 8.6, for the actual selected root family.
The preceding selected-sector theorem supplies exactly the eventual
marginality and plateau bounds used here. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.RemarkLowTemperatureLimit
open PlateauAlgebra RemarkLowTemperatureAlgebra Filter
open scoped BigOperators Topology

theorem source8_6 {ι : Type*} {l : Filter ι} {p : ℕ} (hp : 3≤p)
    (β q : ι→ℝ) (hβ : Tendsto β l atTop)
    (hselected : ∀ᶠθ in l,0<β θ ∧ transitionPlateau p≤q θ ∧ q θ<1 ∧
      (β θ)^2*marginalityPolynomial p (q θ)=1) :
    Tendsto q l (𝓝 1) ∧
    Tendsto (fun θ => β θ*(1-q θ)) l (𝓝 (1/Real.sqrt ((p:ℝ)*((p:ℝ)-1)))) ∧
    Tendsto (fun θ => selectedEnergy p (β θ) (q θ)) l
      (𝓝 (ExternalFieldElementaryPenalty.thresholdEnergy p)) := by
  have hdeficit : Tendsto (fun θ => 1-q θ) l (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards [hselected] with θ h
      exact (scaled_deficit_bound hp h.1 h.2.1 h.2.2.1 h.2.2.2).1
    · filter_upwards [hselected] with θ h
      exact (scaled_deficit_bound hp h.1 h.2.1 h.2.2.1 h.2.2.2).2
    · exact tendsto_const_nhds.div_atTop hβ
  have hq : Tendsto q l (𝓝 1) := by
    simpa only [sub_sub_cancel,sub_zero] using (tendsto_const_nhds : Tendsto (fun _ : ι => (1:ℝ)) l (𝓝 1)).sub hdeficit
  have hA : 0<(p:ℝ)*((p:ℝ)-1) := mul_pos (spin_positive hp) (spin_minus_one_positive hp)
  have hs : Real.sqrt ((p:ℝ)*((p:ℝ)-1))≠0 := (Real.sqrt_pos.mpr hA).ne'
  have hroot : Tendsto (fun θ => Real.sqrt ((p:ℝ)*((p:ℝ)-1)*(q θ)^(p-2))) l
      (𝓝 (Real.sqrt ((p:ℝ)*((p:ℝ)-1)))) := by
    simpa only [one_pow,mul_one] using ((hq.pow (p-2)).const_mul ((p:ℝ)*((p:ℝ)-1))).sqrt
  have hscaled : Tendsto (fun θ => β θ*(1-q θ)) l (𝓝 (1/Real.sqrt ((p:ℝ)*((p:ℝ)-1)))) := by
    apply (tendsto_const_nhds.div hroot hs).congr'
    filter_upwards [hselected] with θ h
    exact (scaled_deficit_exact hp h.1 ((transition_plateau_pos hp).trans_le h.2.1)
      h.2.2.1 h.2.2.2).symm
  refine ⟨hq,hscaled,?_⟩
  have hf : Tendsto (fun θ => energyFactor p (q θ)) l (𝓝 (2*((p:ℝ)-1))) := by
    simpa only [energyFactor_one hp,Function.comp_def] using (energyFactor_continuous p).tendsto 1 |>.comp hq
  have he := hscaled.mul hf
  have hvalue : (1/Real.sqrt ((p:ℝ)*((p:ℝ)-1)))*(2*((p:ℝ)-1))=
      ExternalFieldElementaryPenalty.thresholdEnergy p := by
    rw [ExternalFieldSharpScalar.thresholdEnergy_eq hp]
    have hsq := Real.sq_sqrt hA.le
    field_simp [hs,(spin_positive hp).ne']
    nlinarith [hsq]
  rw [hvalue] at he
  exact he.congr' (Filter.Eventually.of_forall (fun θ => (selectedEnergy_factor hp (β θ) (q θ)).symm))

end SphericalAging.RemarkLowTemperatureLimit
