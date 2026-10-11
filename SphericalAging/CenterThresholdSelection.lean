module

public import SphericalAging.AgingCenterGram
public import SphericalAging.ProfileCenterEnergy
public import SphericalAging.TreeEnergyHomogeneity

public section

/-! Actual normalized centers approach the cubic ceiling, from translated
coefficients, reflection, profile FDT and scalar marginality. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.CenterThresholdSelection
open CKSpecification CausalCenterAverage CenterAverageReal CenterNormalization
open PrefixReflection PrefixRectangleStability CausalTreeRealization TreeCeilings
open ProfileCenterEnergy TreeEnergyHomogeneity

structure Inputs {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    (c r : ℝ → ℝ) (q : ℝ) : Prop extends AgingCenterGram.Inputs h c r q where
  plateau_lt_one : q<1
  fdt : ∀ t : ℝ,0<t → HasDerivAt c (-r t) t
  multiplier_limit : Tendsto d.multiplier atTop (nhds (PlateauAlgebra.multiplier 3 β q))
  translated_response : ∀ A : ℝ,0≤A → TendstoUniformlyOn
    (fun T (z : ℝ×ℝ) => d.R (T+z.1) (T+z.2)) (fun z => r (z.1-z.2)) atTop (triangle A)
  marginality : β^2*PlateauAlgebra.marginalityPolynomial 3 q=1

theorem profile {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q) : Profile c r q := by
  refine ⟨H.correlation_continuous,H.response_continuous,?_,
    AgingCenterGram.profile_initial H.toInputs,H.plateau_limit,
    H.response_integrable.mono_set Ioi_subset_Ici_self,H.fdt⟩
  intro t ht
  exact ⟨H.q_positive.le.trans (H.correlation_bounds t ht).1,(H.correlation_bounds t ht).2⟩

/-- The source h_D is obtained as a limit of the actual tree energy over the
entire real waiting-time ray. -/
theorem center_energy_real_limit {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q) {D : ℝ} (hD : 0≤D) :
    Tendsto (fun T : ℝ => treeEnergy 3 (localCenter h T D)) atTop
      (nhds (prefixEnergyLimit 3 β (PlateauAlgebra.multiplier 3 β q) c r D)) := by
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
  change treeEnergy 3 (localCenter h (max 0 (T n)) D)=treeEnergy 3 (localCenter h (T n) D)
  rw [max_eq_right hn]

@[expose] def deficitLimit (β q : ℝ) (c r : ℝ → ℝ) (D : ℝ) : ℝ :=
  cubicCeiling-prefixEnergyLimit 3 β (PlateauAlgebra.multiplier 3 β q) c r D/
    (Real.sqrt 3*(Real.sqrt (c (2*D)))^3)

/-- The fixed-age normalized-center deficit limit is proved from the actual
energy and norm formulas, including genuine division by nonzero norms. -/
theorem center_deficit_real_limit {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q) {D : ℝ} (hD : 0≤D) :
    Tendsto (fun s : ℝ => cubicCeiling-functional (normalizedCenter h s D)) atTop
      (nhds (deficitLimit β q c r D)) := by
  have hn := center_real_norm_limit h hD (H.reflected_prefix D hD)
  have hA : 0<c (2*D) := H.q_positive.trans_le (H.correlation_bounds _ (by positivity)).1
  have hden : Real.sqrt 3*(Real.sqrt (c (2*D)))^3≠0 := by positivity
  have hl := (tendsto_const_nhds (x:=cubicCeiling)).sub ((center_energy_real_limit H hD).div
    ((hn.pow 3).const_mul (Real.sqrt 3)) hden)
  have hs : Tendsto (fun s : ℝ => s-D) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-D) tendsto_id
  have hl' := hl.comp hs
  change Tendsto (fun s : ℝ => cubicCeiling-functional (normalizedCenter h s D)) atTop
    (nhds (cubicCeiling-prefixEnergyLimit 3 β (PlateauAlgebra.multiplier 3 β q) c r D/
      (Real.sqrt 3*(Real.sqrt (c (2*D)))^3)))
  apply hl'.congr'
  exact Eventually.of_forall (fun s => by
    dsimp only [Function.comp_def,Pi.div_apply]
    rw [normalizedCenter,functional_unitize_treeEnergy])

/-- Marginality makes the derived finite-age deficit tend to zero. No
threshold-center energy or deficit convergence is supplied as a hypothesis. -/
theorem deficitLimit_tendsto {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q) :
    Tendsto (deficitLimit β q c r) atTop (nhds 0) := by
  have htwo : Tendsto (fun D : ℝ => 2*D) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (show (0:ℝ)<2 by norm_num)).mpr tendsto_id
  have hnorm := ((H.plateau_limit.comp htwo).sqrt.pow 3).const_mul (Real.sqrt 3)
  have hsqrtq : 0<Real.sqrt q := Real.sqrt_pos.mpr H.q_positive
  have hden : Real.sqrt 3*(Real.sqrt q)^3≠0 := by positivity
  have hlim := (tendsto_const_nhds (x:=cubicCeiling)).sub
    ((prefixEnergyLimit_tendsto (β:=β) (by decide : 3≤3) (profile H)).div hnorm hden)
  have hsqrt : Real.sqrt (q^3)=(Real.sqrt q)^3 := by
    rw [show q^3=q^2*q by ring,Real.sqrt_mul (sq_nonneg q),Real.sqrt_sq H.q_positive.le]
    nlinarith [Real.sq_sqrt H.q_positive.le]
  have he := (PlateauAlgebra.normalized_center_energy_eq_iff (by decide : 3≤3)
    h.beta_pos H.q_positive H.plateau_lt_one).mpr H.marginality
  rw [hsqrt] at he
  change PlateauAlgebra.centerEnergy 3 β q/(Real.sqrt q)^3=TreeEnergyCeilings.threshold 3 at he
  rw [TreeEnergyCeilings.cubic_threshold] at he
  have heq : cubicCeiling-PlateauAlgebra.centerEnergy 3 β q/(Real.sqrt 3*(Real.sqrt q)^3)=0 := by
    have hroot : Real.sqrt 3≠0 := by positivity
    rw [show PlateauAlgebra.centerEnergy 3 β q/(Real.sqrt 3*(Real.sqrt q)^3)=
      (PlateauAlgebra.centerEnergy 3 β q/(Real.sqrt q)^3)/Real.sqrt 3 by ring,he]
    field_simp [hroot]
    ring
  rw [heq] at hlim
  unfold deficitLimit
  simpa only [Function.comp_def,Pi.div_apply] using hlim

/-- Source selected-center deficit in the uniform nested eventual form. -/
theorem centers_approach_threshold {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ D : ℝ in atTop,0<D ∧ ∀ᶠ S : ℝ in atTop,∀ s : ℝ,S+D≤s →
      ‖normalizedCenter h s D‖=1 ∧ cubicCeiling-functional (normalizedCenter h s D)≤ε := by
  have hsmall := (deficitLimit_tendsto H).eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/2))
  filter_upwards [eventually_gt_atTop (0:ℝ),hsmall] with D hD hsmall
  refine ⟨hD,?_⟩
  have hwait := (center_deficit_real_limit H hD.le).eventually
    (gt_mem_nhds (by linarith : deficitLimit β q c r D<ε))
  obtain ⟨U,hU⟩ := eventually_atTop.mp hwait
  have hunit := CenterNormWaiting.normalized_centers_eventually_unit h hD.le
    (H.q_positive.trans_le (H.correlation_bounds _ (by positivity)).1) (H.reflected_prefix D hD.le)
  filter_upwards [hunit,eventually_ge_atTop U] with S hunit hSU
  intro s hs
  exact ⟨(hunit s hs).2,(hU s (by linarith)).le⟩

end SphericalAging.CenterThresholdSelection
