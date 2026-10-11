module

public import SphericalAging.StationaryAmplitude

public section

/-! Exact transfer of genuine normalized amplitude limits to physical lag. -/
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.StationaryPhysicalScaling
noncomputable section
set_option backward.isDefEq.respectTransparency false
open StationaryNormalization

/-- Actual raw-power scaling and natural derivative chain factors. -/
theorem weighted_chain_scaling (s a t d : ℝ) (n : ℕ) (hs : 0<s) (ht : 0<t) :
    t^(a+(n:ℝ))*(s*(1/s)^n*d)=s^(1+a)*((t/s)^(a+(n:ℝ))*d) := by
  rw [Real.div_rpow ht.le hs.le,Real.rpow_add hs a (n:ℝ),Real.rpow_add hs 1 a,
    Real.rpow_one,Real.rpow_natCast,div_pow]
  field_simp [ne_of_gt hs,ne_of_gt (Real.rpow_pos_of_pos hs a)]
  <;> ring

/-- Genuine affine time rescaling of an actual power-normalized limit. -/
theorem weighted_scaled_limit (H : ℝ → ℝ) (s a A : ℝ) (n : ℕ) (hs : 0<s)
    (hH : Tendsto (fun t : ℝ => t^(a+(n:ℝ))*H t) atTop (𝓝 A)) :
    Tendsto (fun t : ℝ => t^(a+(n:ℝ))*(s*(1/s)^n*H (t/s))) atTop (𝓝 (s^(1+a)*A)) := by
  have he := (hH.comp ((tendsto_div_const_atTop_of_pos hs).mpr tendsto_id)).const_mul (s^(1+a))
  apply he.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  exact (weighted_chain_scaling s a t (H (t/s)) n hs ht).symm

/-- Exact reconstruction from normalized time at every physical lag. -/
theorem physical_profile_reconstruct (q : ℝ) (hq : q<1) (c : ℝ → ℝ) (t : ℝ) :
    c t-q=(1-q)*normalizedProfile q c (t/(1-q)) := by
  have he := normalizedProfile_reconstruct q hq c (t/(1-q))
  rw [mul_div_cancel₀ t (show 1-q≠0 by linarith)] at he
  linarith

/-- The actual correlation tail gets exactly the source amplitude factor. -/
theorem physical_profile_amplitude (q a A0 : ℝ) (hq : q<1) (c : ℝ → ℝ)
    (hAmp : Tendsto (fun t : ℝ => t^a*normalizedProfile q c t) atTop (𝓝 A0)) :
    Tendsto (fun t : ℝ => t^a*(c t-q)) atTop (𝓝 ((1-q)^(1+a)*A0)) := by
  have hs : 0<1-q := by linarith
  have he := weighted_scaled_limit (normalizedProfile q c) (1-q) a A0 0 hs
    (by simpa only [Nat.cast_zero,add_zero] using hAmp)
  simp only [Nat.cast_zero,add_zero,pow_zero,mul_one] at he
  apply he.congr
  intro t
  rw [physical_profile_reconstruct q hq c t]

end
end SphericalAging.StationaryPhysicalScaling
