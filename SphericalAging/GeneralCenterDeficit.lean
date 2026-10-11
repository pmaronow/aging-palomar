module

public import SphericalAging.CubicResponseLocalization

public section

/-! Genuine all-spin positive-plateau normalized-prefix energy saturation.
This proves the actual threshold-deficit limit from scalar marginality. It
does not assert the general-spin ceiling or white-prefix localization. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.GeneralCenterDeficit
open CKSpecification CausalCenterAverage CenterAverageReal CenterNormalization
open PrefixReflection PrefixRectangleStability CausalTreeRealization ProfileCenterEnergy TreeEnergyHomogeneity

structure SelectedInputs {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (c r : ℝ → ℝ) (q : ℝ) : Prop where
  q_positive : 0<q
  plateau_lt_one : q<1
  correlation_continuous : ContinuousOn c (Ici 0)
  correlation_initial : c 0=1
  correlation_bounds : ∀ t : ℝ,0≤t → q≤c t ∧ c t≤1
  plateau_limit : Tendsto c atTop (nhds q)
  response_continuous : ContinuousOn r (Ici 0)
  response_integrable : IntegrableOn r (Ici 0)
  fdt : ∀ t : ℝ,0<t → HasDerivAt c (-r t) t
  multiplier_limit : Tendsto d.multiplier atTop (nhds (PlateauAlgebra.multiplier p β q))
  translated_correlation : ∀ A : ℝ,0≤A → TendstoUniformlyOn
    (fun T (z : ℝ×ℝ) => d.C (T+z.1) (T+z.2)) (fun z => c |z.1-z.2|) atTop (square A)
  translated_response : ∀ A : ℝ,0≤A → TendstoUniformlyOn
    (fun T (z : ℝ×ℝ) => d.R (T+z.1) (T+z.2)) (fun z => r (z.1-z.2)) atTop (triangle A)
  reflected_prefix : ∀ A : ℝ,0≤A → TendstoUniformlyOn
    (fun T => Function.uncurry (futureKernel h T)) (fun z => c (z.1+z.2)) atTop (square A)

theorem profile {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q) : Profile c r q := by
  refine ⟨H.correlation_continuous,H.response_continuous,?_,H.correlation_initial,
    H.plateau_limit,H.response_integrable.mono_set Ioi_subset_Ici_self,H.fdt⟩
  intro t ht
  exact ⟨H.q_positive.le.trans (H.correlation_bounds t ht).1,(H.correlation_bounds t ht).2⟩

theorem center_energy_real_limit {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q) {D : ℝ} (hD : 0≤D) :
    Tendsto (fun T : ℝ => treeEnergy p (localCenter h T D)) atTop
      (nhds (prefixEnergyLimit p β (PlateauAlgebra.multiplier p β q) c r D)) := by
  apply tendsto_iff_seq_tendsto.mpr
  intro T hT
  let S : ℕ → ℝ := fun n => max 0 (T n)
  have hS : Tendsto S atTop atTop := tendsto_atTop_mono (fun n => le_max_right 0 (T n)) hT
  have hshift : Tendsto (fun n => S n+D) atTop atTop := tendsto_atTop_add_const_right atTop D hS
  have hl := StationaryPrefixConsequences.prefix_energy_of_uniform_translation h
    (T:=S) (fun n => le_max_left 0 (T n)) hD
    ((H.translated_correlation D hD).seq_tendstoUniformlyOn S hS)
    ((H.translated_response D hD).seq_tendstoUniformlyOn S hS)
    ((H.reflected_prefix D hD).seq_tendstoUniformlyOn S hS)
    (H.multiplier_limit.comp hshift)
  apply hl.congr'
  filter_upwards [hT.eventually (eventually_ge_atTop (0:ℝ))] with n hn
  change treeEnergy p (localCenter h (max 0 (T n)) D)=treeEnergy p (localCenter h (T n) D)
  rw [max_eq_right hn]

/-- Literal source delta_L in energy units, for every pure spin. -/
@[expose] def deficitLimit (p : ℕ) (β q : ℝ) (c r : ℝ → ℝ) (D : ℝ) : ℝ :=
  TreeEnergyCeilings.threshold p-
    prefixEnergyLimit p β (PlateauAlgebra.multiplier p β q) c r D/(Real.sqrt (c (2*D)))^p

theorem center_deficit_real_limit {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q) {D : ℝ} (hD : 0≤D) :
    Tendsto (fun s : ℝ => TreeEnergyCeilings.threshold p-treeEnergy p (normalizedCenter h s D)) atTop
      (nhds (deficitLimit p β q c r D)) := by
  have hp : 0<p := by have hg:=h.spin_ge_three; omega
  have hn := center_real_norm_limit h hD (H.reflected_prefix D hD)
  have hA : 0<c (2*D) := H.q_positive.trans_le (H.correlation_bounds _ (by positivity)).1
  have hden : (Real.sqrt (c (2*D)))^p≠0 := by positivity
  have hl := (tendsto_const_nhds (x:=TreeEnergyCeilings.threshold p)).sub
    ((center_energy_real_limit H hD).div (hn.pow p) hden)
  have hs : Tendsto (fun s : ℝ => s-D) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-D) tendsto_id
  apply (hl.comp hs).congr'
  exact Eventually.of_forall (fun s => by
    dsimp only [Function.comp_def,Pi.div_apply]
    rw [normalizedCenter,treeEnergy_unitize hp])

theorem sqrt_pow_nonnegative {q : ℝ} (hq : 0≤q) (n : ℕ) : Real.sqrt (q^n)=(Real.sqrt q)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg hq n),ih,pow_succ]

/-- The source p-center-deficit saturation limit is proved for every p>=3
from FDT and the actual scalar marginality identity. No deficit is assumed. -/
theorem deficitLimit_tendsto {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q)
    (hmarg : β^2*PlateauAlgebra.marginalityPolynomial p q=1) :
    Tendsto (deficitLimit p β q c r) atTop (nhds 0) := by
  have htwo : Tendsto (fun D : ℝ => 2*D) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (show (0:ℝ)<2 by norm_num)).mpr tendsto_id
  have hnorm := (H.plateau_limit.comp htwo).sqrt.pow p
  have hden : (Real.sqrt q)^p≠0 := pow_ne_zero _ (Real.sqrt_ne_zero'.mpr H.q_positive)
  have hlim := (tendsto_const_nhds (x:=TreeEnergyCeilings.threshold p)).sub
    ((prefixEnergyLimit_tendsto (β:=β) h.spin_ge_three (profile H)).div hnorm hden)
  have he := (PlateauAlgebra.normalized_center_energy_eq_iff h.spin_ge_three
    h.beta_pos H.q_positive H.plateau_lt_one).mpr hmarg
  rw [sqrt_pow_nonnegative H.q_positive.le] at he
  change PlateauAlgebra.centerEnergy p β q/(Real.sqrt q)^p=TreeEnergyCeilings.threshold p at he
  rw [he,sub_self] at hlim
  change Tendsto (fun D : ℝ => TreeEnergyCeilings.threshold p-
    prefixEnergyLimit p β (PlateauAlgebra.multiplier p β q) c r D/(Real.sqrt (c (2*D)))^p)
    atTop (nhds 0)
  simpa only [Function.comp_def,Pi.div_apply] using hlim

/-- Actual unit normalized-prefix energies approach the source threshold
in the uniform nested real eventual form, for every p>=3. -/
theorem centers_approach_threshold {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q)
    (hmarg : β^2*PlateauAlgebra.marginalityPolynomial p q=1) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ D : ℝ in atTop,0<D ∧ ∀ᶠ S : ℝ in atTop,∀ s : ℝ,S+D≤s →
      ‖normalizedCenter h s D‖=1 ∧
      TreeEnergyCeilings.threshold p-treeEnergy p (normalizedCenter h s D)≤ε := by
  have hsmall := (deficitLimit_tendsto H hmarg).eventually
    (gt_mem_nhds (by linarith : (0:ℝ)<ε/2))
  filter_upwards [eventually_gt_atTop (0:ℝ),hsmall] with D hD hsmall
  refine ⟨hD,?_⟩
  have hwait := (center_deficit_real_limit H hD.le).eventually
    (gt_mem_nhds (by linarith : deficitLimit p β q c r D<ε))
  obtain ⟨U,hU⟩ := eventually_atTop.mp hwait
  have hunit := CenterNormWaiting.normalized_centers_eventually_unit h hD.le
    (H.q_positive.trans_le (H.correlation_bounds _ (by positivity)).1) (H.reflected_prefix D hD.le)
  filter_upwards [hunit,eventually_ge_atTop U] with S hunit hSU
  intro s hs
  exact ⟨(hunit s hs).2,(hU s (by linarith)).le⟩

theorem cubic_inputs_of_marginality {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q)
    (hmarg : β^2*PlateauAlgebra.marginalityPolynomial 3 q=1) :
    CubicResponseLocalization.Inputs h c r q :=
  ⟨H.q_positive,H.plateau_lt_one,H.correlation_continuous,H.correlation_initial,
    H.correlation_bounds,H.plateau_limit,H.response_continuous,H.response_integrable,
    H.fdt,H.multiplier_limit,H.translated_correlation,H.translated_response,H.reflected_prefix,hmarg⟩

/-- The actual normalized energies converge to the threshold from both sides,
without supplying a general-spin ceiling as a hypothesis. -/
theorem centers_approach_threshold_absolute {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q)
    (hmarg : β^2*PlateauAlgebra.marginalityPolynomial p q=1) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ D : ℝ in atTop,0<D ∧ ∀ᶠ S : ℝ in atTop,∀ s : ℝ,S+D≤s →
      ‖normalizedCenter h s D‖=1 ∧
      |TreeEnergyCeilings.threshold p-treeEnergy p (normalizedCenter h s D)|≤ε := by
  have hsmall := Metric.tendsto_nhds.mp (deficitLimit_tendsto H hmarg) (ε/2) (by positivity)
  filter_upwards [eventually_gt_atTop (0:ℝ),hsmall] with D hD hsmall
  rw [Real.dist_eq,sub_zero] at hsmall
  refine ⟨hD,?_⟩
  have hwait := Metric.tendsto_nhds.mp (center_deficit_real_limit H hD.le) (ε/2) (by positivity)
  obtain ⟨U,hU⟩ := eventually_atTop.mp hwait
  have hunit := CenterNormWaiting.normalized_centers_eventually_unit h hD.le
    (H.q_positive.trans_le (H.correlation_bounds _ (by positivity)).1) (H.reflected_prefix D hD.le)
  filter_upwards [hunit,eventually_ge_atTop U] with S hunit hSU
  intro s hs
  refine ⟨(hunit s hs).2,?_⟩
  have hh := hU s (by linarith)
  rw [Real.dist_eq] at hh
  have ha := abs_sub_le (TreeEnergyCeilings.threshold p-treeEnergy p (normalizedCenter h s D))
    (deficitLimit p β q c r D) 0
  simp only [sub_zero] at ha
  linarith

end SphericalAging.GeneralCenterDeficit
