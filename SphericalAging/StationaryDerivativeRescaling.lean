module

public import SphericalAging.CompleteMonotoneDerivativeAsymptotics

public section

/-! Genuine physical-lag rescaling of every positive-order stationary derivative.
Only smoothness on the positive ray is needed; no negative-lag extension is assumed. -/
namespace SphericalAging.StationaryDerivativeRescaling

open Set Filter StationaryNormalization CompleteMonotoneDerivativeAsymptotics
open scoped Topology

/-- Actual positive-ray chain rule for an arbitrary order under division of the lag. -/
theorem iteratedDeriv_comp_div_on_ray {u : ℝ → ℝ} {k t : ℝ} {n : ℕ}
    (hk : 0<k) (ht : 0<t) (hu : ContDiffOn ℝ n u (Ioi 0)) :
    iteratedDeriv n (fun x => u (x/k)) t=k⁻¹^n*iteratedDeriv n u (t/k) := by
  have hmaps : MapsTo (fun x : ℝ => k⁻¹*x) (Ioi 0) (Ioi 0) :=
    fun x hx => mul_pos (inv_pos.mpr hk) hx
  have hcomp := iteratedDerivWithin_comp_const_smul (show t ∈ Ioi (0 : ℝ) from ht) isOpen_Ioi.uniqueDiffOn hu k⁻¹ hmaps
  rw [iteratedDerivWithin_of_isOpen isOpen_Ioi ht,
    iteratedDerivWithin_of_isOpen isOpen_Ioi (hmaps ht)] at hcomp
  simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm k⁻¹] using hcomp

/-- Positive-order derivatives of an affine rescaled profile, from actual pointwise equality. -/
theorem affine_profile_iteratedDeriv {c u : ℝ → ℝ} {q k t : ℝ} {n : ℕ}
    (hk : 0<k) (ht : 0<t) (hn : 0<n) (hu : ContDiffOn ℝ n u (Ioi 0))
    (heq : ∀ x,0<x → c x=q+k*u (x/k)) :
    iteratedDeriv n c t=(k/k^n)*iteratedDeriv n u (t/k) := by
  have hh : EqOn c (fun x => q+k*u (x/k)) (Ioi 0) := heq
  rw [hh.iteratedDeriv_of_isOpen isOpen_Ioi n ht,iteratedDeriv_const_add hn,
    iteratedDeriv_const_mul_field,iteratedDeriv_comp_div_on_ray hk ht hu]
  simp only [inv_pow,div_eq_mul_inv]
  ring

/-- The exact integer-power form of the physical-lag derivative coefficient. -/
theorem affine_profile_iteratedDeriv_zpow {c u : ℝ → ℝ} {q k t : ℝ} {n : ℕ}
    (hk : 0<k) (ht : 0<t) (hn : 0<n) (hu : ContDiffOn ℝ n u (Ioi 0))
    (heq : ∀ x,0<x → c x=q+k*u (x/k)) :
    iteratedDeriv n c t=k^(1-(n : ℤ))*iteratedDeriv n u (t/k) := by
  rw [affine_profile_iteratedDeriv hk ht hn hu heq,zpow_sub₀ hk.ne',zpow_one,zpow_natCast]

/-- The genuine source normalized profile gives the physical-lag derivative identity. -/
theorem normalized_physical_iteratedDeriv (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) (hq : q<1) {t : ℝ}
    (ht : 0<t) {n : ℕ} (hn : 0<n) :
    iteratedDeriv n c t=(1-q)^(1-(n : ℤ))*
      iteratedDeriv n (normalizedProfile q c) (t/(1-q)) := by
  apply affine_profile_iteratedDeriv_zpow (sub_pos.mpr hq) ht hn
    (h.profile_smooth.of_le (by exact_mod_cast le_top))
  intro x _
  rw [normalizedProfile_reconstruct q hq c]
  congr 1
  field_simp [sub_pos.mpr hq |>.ne']

/-- Rescaling the weighted derivative retains the same physical amplitude in all orders. -/
theorem weighted_derivative_rescaling {c u : ℝ → ℝ} {q k t a : ℝ} {n : ℕ}
    (hk : 0<k) (ht : 0<t) (hn : 0<n) (hu : ContDiffOn ℝ n u (Ioi 0))
    (heq : ∀ x,0<x → c x=q+k*u (x/k)) :
    t^(a+(n : ℝ))*((-1 : ℝ)^n*iteratedDeriv n c t)=
      k^(a+1)*((t/k)^(a+(n : ℝ))*((-1 : ℝ)^n*iteratedDeriv n u (t/k))) := by
  rw [affine_profile_iteratedDeriv hk ht hn hu heq,
    Real.div_rpow ht.le hk.le,Real.rpow_add hk,Real.rpow_add hk,Real.rpow_natCast,
    Real.rpow_one]
  field_simp

/-- The actual normalized amplitude yields every physical derivative limit. -/
theorem physical_all_order_derivative_asymptotics (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) (hq : q<1) {a A : ℝ}
    (hAmp : Tendsto (fun t : ℝ => t^a*normalizedProfile q c t) atTop (𝓝 A))
    {n : ℕ} (hn : 0<n) :
    Tendsto (fun t : ℝ => t^(a+(n : ℝ))*((-1 : ℝ)^n*iteratedDeriv n c t))
      atTop (𝓝 ((1-q)^(a+1)*A*risingFactor a n)) := by
  have hk : 0<1-q := sub_pos.mpr hq
  have htime : Tendsto (fun t : ℝ => t/(1-q)) atTop atTop := by
    simpa only [div_eq_mul_inv,mul_comm,id_eq] using
      (tendsto_const_mul_atTop_of_pos (inv_pos.mpr hk)).mpr tendsto_id
  have hh := ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1-q)^(a+1)) atTop (𝓝 ((1-q)^(a+1)))).mul
    ((normalized_all_order_derivative_asymptotics p β γ q c r h hAmp n).comp htime))
  have hhh : Tendsto (fun t : ℝ => (1-q)^(a+1)*
      ((t/(1-q))^(a+(n : ℝ))*((-1 : ℝ)^n*iteratedDeriv n (normalizedProfile q c) (t/(1-q)))))
      atTop (𝓝 ((1-q)^(a+1)*A*risingFactor a n)) := by
    simpa only [mul_assoc,Function.comp_def] using hh
  apply hhh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  symm
  apply weighted_derivative_rescaling hk ht hn
    (h.profile_smooth.of_le (by exact_mod_cast le_top))
  intro x _
  rw [normalizedProfile_reconstruct q hq c]
  congr 1
  field_simp [hk.ne']

end SphericalAging.StationaryDerivativeRescaling
