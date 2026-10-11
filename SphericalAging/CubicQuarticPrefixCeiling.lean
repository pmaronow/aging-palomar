module

public import SphericalAging.MainStationaryAgingTheorem
public import SphericalAging.TreeEnergyHomogeneity
public import SphericalAging.GeneralCenterDeficit

public section

/-! Source8.1(a) is derived for cubic and quartic CK clusters from the
actual homogeneous tree ceiling and the exact stationary prefix limits. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
open Set Filter
open scoped Topology InnerProductSpace
namespace SphericalAging.CubicQuarticPrefixCeiling
open CKSpecification CausalTree CausalTreeRealization TreeEnergyCeilings
  TreeEnergyHomogeneity CenterNormalization StationaryClusterInputs
  StationaryMultiplierSelection PrefixReflection PrefixRectangleStability
  StationaryReflectionFromTranslation StationaryPrefixConsequences ProfileCenterEnergy

theorem treeEnergy_eq_energy {p : ℕ} (hp : 1≤p) (v : Space (p-1)) :
    treeEnergy p v=TreeEnergyCeilings.energy v := by
  have he : ((p-1:ℕ):ℝ)+1=(p:ℝ) := by exact_mod_cast Nat.sub_add_cancel hp
  simp only [treeEnergy,TreeEnergyCeilings.energy,TreeCeilings.functional,he]

theorem homogeneous_ceiling {p : ℕ} (hp : p=3 ∨ p=4) (v : Space (p-1)) :
    treeEnergy p v≤threshold p*‖v‖^p := by
  have hp0 : 0<p := by rcases hp with rfl|rfl <;> omega
  by_cases hv : ‖v‖=0
  · have he : v=0 := norm_eq_zero.mp hv
    rw [he]
    simp only [treeEnergy,TreeCeilings.functional,inner_zero_left,mul_zero,norm_zero,
      zero_pow (Nat.ne_of_gt hp0)]
    exact le_rfl
  · have hvp : 0<‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    have hc := energy_strict hp (unitize v) (unitize_norm hvp)
    rw [←treeEnergy_eq_energy (by omega),treeEnergy_unitize hp0] at hc
    have hl : treeEnergy p v/‖v‖^p≤threshold p := (le_abs_self _).trans hc.le
    exact (div_le_iff₀ (pow_pos hvp p)).mp hl

theorem actual_prefix_ceiling {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hp : p=3 ∨ p=4) : PrefixCeiling h := by
  intro T c r ell q H hq L hL
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp (H.late.eventually (eventually_ge_atTop (0:ℝ)))
  let φ : ℕ → ℕ := fun n => n+n0
  have hφ : Tendsto φ atTop atTop := tendsto_atTop_mono
    (fun n => show n≤φ n from Nat.le_add_right n n0) tendsto_id
  let S : ℕ → ℝ := T∘φ
  have hS : ∀n,0≤S n := fun n => hn0 _ (by dsimp [φ]; omega)
  have hQ := prefix_reflection_of_uniform_translation_and_fdt h H.late
    H.correlation H.response H.multiplier H.fdt L hL
  have he := prefix_energy_of_uniform_translation h hS hL
    ((H.correlation L hL).seq_tendstoUniformlyOn φ hφ)
    ((H.response L hL).seq_tendstoUniformlyOn φ hφ)
    (hQ.seq_tendstoUniformlyOn φ hφ)
    (((H.multiplier L hL).tendsto_at ⟨hL,le_rfl⟩).comp hφ)
  have hn := prefix_norm_of_uniform_reflection h hL (hQ.seq_tendstoUniformlyOn φ hφ)
  have hnorm : Tendsto (fun n => ‖prefixVector h (S n) (S n+L)‖^p)
      atTop (𝓝 ((Real.sqrt (c (2*L)))^p)) := by
    simpa only [S,Function.comp_def,Real.sqrt_sq (norm_nonneg _)] using hn.sqrt.pow p
  have hlim : prefixEnergyLimit p β ell c r L≤threshold p*(Real.sqrt (c (2*L)))^p := by
    apply le_of_tendsto_of_tendsto he (hnorm.const_mul (threshold p))
    exact Eventually.of_forall (fun n => homogeneous_ceiling hp (prefixVector h (S n) (S n+L)))
  rwa [←NormalizedCenterAMGM.sqrt_pow_eq_rpow
    ((H.physical (2*L) (by positivity)).1.trans (H.physical (2*L) (by positivity)).2.1) p,
    GeneralCenterDeficit.sqrt_pow_nonnegative
      ((H.physical (2*L) (by positivity)).1.trans (H.physical (2*L) (by positivity)).2.1) p]

end SphericalAging.CubicQuarticPrefixCeiling
