module

public import SphericalAging.CubicResponseLocalization
public import SphericalAging.RemoteResponseToStrongRow
public import SphericalAging.BackwardRowResidual

public section

/-! Genuine strong response rows from white-prefix localization. The positive
plateau theorem is cubic; the zero-plateau theorem holds for every actual CK
spin. No row-convergence, Fisher or center-Gram premise is used. -/
noncomputable section
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.StrongResponseRows
open CKSpecification CKPhysicalConsequences GreenCovariance PrefixRectangleStability
open WhitePrefixResponse RemoteResponseToStrongRow EarlierSmoothing BackwardRowL2 BackwardRowResidual

theorem profile_bounds_of_translation {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ → ℝ}
    (hR : ∀ A : ℝ,0≤A → TendstoUniformlyOn
      (fun T (z : ℝ×ℝ) => d.R (T+z.1) (T+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A)) :
    ∀ v : ℝ,0≤v → 0≤r v ∧ r v≤1 := by
  intro v hv
  have hm : (v,0)∈triangle v := ⟨⟨hv,le_rfl⟩,⟨le_rfl,hv⟩⟩
  have hl := (hR v hv).tendsto_at hm
  simp only [sub_zero,add_zero] at hl
  have hb := physical_bounds_of_equations h
  constructor
  · apply ge_of_tendsto hl
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    exact hb.2 (T+v) T hT (by linarith)
  · apply le_of_tendsto hl
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    exact (response_le_correlation h hT (by linarith)).trans
      (hb.1 (T+v) T (by linarith) hT).2

theorem profile_square_integrable {r : ℝ → ℝ}
    (hr : ContinuousOn r (Ici 0)) (hi : IntegrableOn r (Ici 0))
    (hb : ∀ v : ℝ,0≤v → 0≤r v ∧ r v≤1) :
    IntegrableOn (fun v => (r v)^2) (Ici 0) := by
  apply hi.mono' ((hr.pow 2).aestronglyMeasurable measurableSet_Ici)
  filter_upwards [ae_restrict_mem measurableSet_Ici] with v hv
  have hh := hb v hv
  change ‖(r v)^2‖≤r v
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  nlinarith

/-- Whole half-line squared L2 residual, including the genuine missing tail. -/
theorem full_response_energy_of_remote {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ → ℝ} (hr : ContinuousOn r (Ici 0))
    (hi : IntegrableOn r (Ici 0))
    (hR : ∀ A : ℝ,0≤A → TendstoUniformlyOn
      (fun T (z : ℝ×ℝ) => d.R (T+z.1) (T+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A))
    (hremote : ∀ ε : ℝ,0<ε → ∀ᶠ L : ℝ in atTop,0<L ∧
      ∀ᶠ t : ℝ in atTop,remoteTail d t L≤ε) :
    Tendsto (responseErrorEnergy d r) atTop (nhds 0) ∧
    Tendsto (fun t => ∫ v : ℝ,(responseRow d t v-r v)^2 ∂rayMeasure) atTop (nhds 0) ∧
    Tendsto (fun t => (eLpNorm (fun v => responseRow d t v-r v) 2 rayMeasure).toReal)
      atTop (nhds 0) := by
  have hb := profile_bounds_of_translation h hR
  have hi2 := profile_square_integrable hr hi hb
  have hrb (v : ℝ) (hv : 0≤v) : |r v|≤1 := by
    rw [abs_of_nonneg (hb v hv).1]
    exact (hb v hv).2
  have hrow := response_error_energy_tendsto h hr hrb hi2 hR hremote
  have htail : Tendsto (fun t : ℝ => ∫ v in Ioi t,(r v)^2) atTop (nhds 0) :=
    tendsto_integral_Ioi_zero tendsto_id
  have hfull : Tendsto (fun t => ∫ v : ℝ,(responseRow d t v-r v)^2 ∂rayMeasure)
      atTop (nhds 0) := by
    have he := hrow.add htail
    simp only [zero_add] at he
    apply he.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact (response_row_residual_energy h hr (hi2.mono_set Ioi_subset_Ici_self) ht).symm
  refine ⟨hrow,hfull,?_⟩
  have hsqrt := hfull.sqrt
  simp only [Real.sqrt_zero] at hsqrt
  apply hsqrt.congr'
  exact Eventually.of_forall (fun t =>
    (lpNorm_two_eq_sqrt ((responseRow_memLp_two h t).sub
      (profile_memLp_two hr (hi2.mono_set Ioi_subset_Ici_self)))).symm)

/-- Source 11.1, zero plateau, for every p≥3: the literal zero-extended
actual lag row converges to the selected response in L2(0,∞). -/
theorem zero_plateau_strong_rows {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {c r : ℝ → ℝ} (hc : Tendsto c atTop (nhds 0))
    (hr : ContinuousOn r (Ici 0)) (hi : IntegrableOn r (Ici 0))
    (hR : ∀ A : ℝ,0≤A → TendstoUniformlyOn
      (fun T (z : ℝ×ℝ) => d.R (T+z.1) (T+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A))
    (hQ : ∀ A : ℝ,0≤A → TendstoUniformlyOn
      (fun T => Function.uncurry (PrefixReflection.futureKernel h T))
      (fun z => c (z.1+z.2)) atTop (square A)) :
    Tendsto (responseErrorEnergy d r) atTop (nhds 0) ∧
    Tendsto (fun t => ∫ v : ℝ,(responseRow d t v-r v)^2 ∂rayMeasure) atTop (nhds 0) ∧
    Tendsto (fun t => (eLpNorm (fun v => responseRow d t v-r v) 2 rayMeasure).toReal)
      atTop (nhds 0) :=
  full_response_energy_of_remote h hr hi hR (fun _ hε => zero_plateau_remote_localization h hc hQ hε)

/-- Source 11.1, positive plateau cubic: marginality and actual prefix
energy produce white-prefix localization and hence genuine full L2 rows. -/
theorem cubic_positive_plateau_strong_rows {β : ℝ} {d : CKData}
    {h : CKEquations 3 β d} {c r : ℝ → ℝ} {q : ℝ}
    (H : CubicResponseLocalization.Inputs h c r q) :
    Tendsto (responseErrorEnergy d r) atTop (nhds 0) ∧
    Tendsto (fun t => ∫ v : ℝ,(responseRow d t v-r v)^2 ∂rayMeasure) atTop (nhds 0) ∧
    Tendsto (fun t => (eLpNorm (fun v => responseRow d t v-r v) 2 rayMeasure).toReal)
      atTop (nhds 0) :=
  full_response_energy_of_remote h H.response_continuous H.response_integrable H.translated_response
    (fun _ hε => CubicResponseLocalization.cubic_remote_localization H hε)

end SphericalAging.StrongResponseRows
