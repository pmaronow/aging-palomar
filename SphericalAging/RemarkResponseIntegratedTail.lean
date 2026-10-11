module

public import SphericalAging.ActualCubicQuarticStrongResponse
public import SphericalAging.MainCubicGeometryActualModel
public import SphericalAging.SusceptibilityWindow

public section

/-! Remark 11.8: the actual cubic remote response retains positive integrated
mass while its squared mass has a tail tending to zero. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.RemarkResponseIntegratedTail
open CKSpecification CKPhysicalConsequences GreenCovariance CubicResponseLocalization
open SusceptibilityWindow SusceptibilityLowerLimit StrongResponseConsequences WhitePrefixResponse

@[expose] def remoteMass (d : CKData) (t L : ℝ) : ℝ := ∫u in (0:ℝ)..max 0 (t-L),d.R t u

theorem remoteMass_split {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    {t L : ℝ} (hL : 0≤L) (ht : L≤t) :
    remoteMass d t L=susceptibility d t 0-windowMass d t L := by
  have hc : Continuous (clampedResponse d t) :=
    (clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)
  have he := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (hc.intervalIntegrable 0 (t-L)) (hc.intervalIntegrable (t-L) t)
  have hzero : (∫u in (0:ℝ)..(t-L),clampedResponse d t u)=remoteMass d t L := by
    unfold remoteMass
    rw [max_eq_right (sub_nonneg.mpr ht)]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (sub_nonneg.mpr ht)] at hu
    exact clampedResponse_eq hu.1 (by linarith [hu.2])
  have hrecent : (∫u in (t-L)..t,clampedResponse d t u)=windowMass d t L := by
    rw [windowMass_eq]
    unfold susceptibility
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by linarith : t-L≤t)] at hu
    exact clampedResponse_eq (by linarith [hu.1]) hu.2
  have htotal : (∫u in (0:ℝ)..t,clampedResponse d t u)=susceptibility d t 0 := by
    unfold susceptibility
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (hL.trans ht)] at hu
    exact clampedResponse_eq hu.1 hu.2
  rw [hzero,hrecent,htotal] at he
  linarith

theorem remoteMass_eventually_lower {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : Inputs h c r q) {L : ℝ} (hL : 0≤L) :
    ∀ε : ℝ,0<ε→∀ᶠt : ℝ in atTop,1-q-ε≤remoteMass d t L := by
  intro ε hε
  have hw := (windowMass_tendsto H hL).eventually
    (gt_mem_nhds (by linarith : 1-c L<1-c L+ε/2))
  filter_upwards [eventually_ge_atTop L,eventually_lower_bound H (ε/2) (by positivity),hw]
    with t ht htotal hwindow
  rw [remoteMass_split h hL ht]
  linarith [(H.correlation_bounds L hL).1]

theorem source11_8_of_inputs {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : Inputs h c r q) :
    0<1-q ∧
    (∀L : ℝ,0≤L→ENNReal.ofReal (1-q)≤
      liminf (fun t : ℝ => ENNReal.ofReal (remoteMass d t L)) atTop) ∧
    (∀L : ℝ,0≤L→Tendsto (fun t => remoteTail d t L) atTop (𝓝 (EarlierSmoothing.responseTail r L))) ∧
    Tendsto (EarlierSmoothing.responseTail r) atTop (𝓝 0) := by
  have hb := StrongResponseRows.profile_bounds_of_translation h H.translated_response
  have hi2 := StrongResponseRows.profile_square_integrable H.response_continuous H.response_integrable hb
  refine ⟨by linarith [H.plateau_lt_one],?_,?_,?_⟩
  · exact fun L hL => ofReal_liminf_lower (remoteMass_eventually_lower H hL)
  · exact (cubic_positive_plateau_source11_1 H).squared_tail
  · have hz : Tendsto (fun L : ℝ => ∫v in Ioi L,(r v)^2) atTop (𝓝 0) :=
      tendsto_integral_Ioi_zero tendsto_id
    change Tendsto (fun L : ℝ => ∫v in Ici L,(r v)^2) atTop (𝓝 0)
    simpa only [integral_Ici_eq_integral_Ioi] using hz

theorem source11_8_actual_model {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    (hsector : PlateauAlgebra.transitionBetaSquared 3≤β^2) :
    ∃q : ℝ,∃r : ℝ→ℝ,q=AllTemperatureTheorem.largerPlateau 3 β ∧ 0<1-q ∧
      (∀L : ℝ,0≤L→ENNReal.ofReal (1-q)≤
        liminf (fun t : ℝ => ENNReal.ofReal (remoteMass d t L)) atTop) ∧
      (∀L : ℝ,0≤L→Tendsto (fun t => remoteTail d t L) atTop (𝓝 (EarlierSmoothing.responseTail r L))) ∧
      Tendsto (EarlierSmoothing.responseTail r) atTop (𝓝 0) := by
  obtain ⟨hc,_aF,_hF,_han,_hmass⟩ := ActualSphereCKFisherClosure.actual_stationary_compactness_and_Fisher h
  obtain ⟨_ell,q,_c,r,_T,_H,hs,_hf,hroot,_hqd,_hend⟩ :=
    MainCubicGeometryTheorem.canonical_inputs h hc hsector
  exact ⟨q,r,hroot,source11_8_of_inputs hs⟩

end SphericalAging.RemarkResponseIntegratedTail
