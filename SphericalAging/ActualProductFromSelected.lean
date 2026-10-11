module

public import SphericalAging.UniformResponseRows
public import SphericalAging.ActualCorrelationProductSup
public import SphericalAging.ActualCenterAverage
public import SphericalAging.GeneralCenterDeficit

public section

/-! Cubic actual normalized-center and three-time product conclusions from
the independent selected-profile inputs. Response-row convergence is proved;
the preceding Fisher and fixed-wait selection inputs remain explicit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.ActualProductFromSelected
open CKSpecification StrongBackwardDefect StrongResponseRows UniformResponseRows

/-- Constructs the old center-Gram input bundle using the genuine source
11.1 response-row theorem, with no target row, Gram or product premise. -/
theorem center_gram_inputs {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : CubicResponseLocalization.Inputs h c r q)
    (hforget : ∀ s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (nhds 0))
    (hFisher : ∃ a : ℝ → ℝ,FisherMajorant 3 β d a) : AgingCenterGram.Inputs h c r q := by
  have hb := profile_bounds_of_translation h H.translated_response
  exact ⟨H.q_positive,H.correlation_continuous,H.correlation_bounds,H.plateau_limit,
    H.response_continuous,fun _ ht => (hb _ ht).1,cubic_response_antitone H,
    (hb 0 le_rfl).2,H.response_integrable,hforget,hFisher,
    (cubic_positive_plateau_strong_rows H).1,H.translated_correlation,H.reflected_prefix⟩

theorem threshold_inputs {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : CubicResponseLocalization.Inputs h c r q)
    (hforget : ∀ s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (nhds 0))
    (hFisher : ∃ a : ℝ → ℝ,FisherMajorant 3 β d a) : CenterThresholdSelection.Inputs h c r q :=
  ⟨center_gram_inputs H hforget hFisher,H.plateau_lt_one,H.fdt,H.multiplier_limit,
    H.translated_response,H.marginality⟩

/-- Exact source 14.2 normalized actual-center comparison in its literal
double-limit supremum form, with actual response rows derived upstream. -/
theorem source14_2 {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : CubicResponseLocalization.Inputs h c r q)
    (hforget : ∀ s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (nhds 0))
    (hFisher : ∃ a : ℝ → ℝ,FisherMajorant 3 β d a) :
    Tendsto (fun D : ℝ => limsup (AgingCenterGramSup.gramSup h q D) atTop) atTop (nhds 0) :=
  AgingCenterGramSup.aging_center_gram_supremum (center_gram_inputs H hforget hFisher)

/-- Exact source 14.3, each cyclic product, from independent cubic selected
profiles and the actual preceding Fisher/fixed-wait hypotheses. -/
theorem source14_3 {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : CubicResponseLocalization.Inputs h c r q)
    (hforget : ∀ s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (nhds 0))
    (hFisher : ∃ a : ℝ → ℝ,FisherMajorant 3 β d a) (k : Fin 3) :
    Tendsto (fun D : ℝ => limsup (ActualCorrelationProductSup.productSup k d q D) atTop)
      atTop (nhds 0) :=
  ActualCorrelationProductSup.actual_three_time_product_supremum
    (threshold_inputs H hforget hFisher) k

/-- Exact source 14.1 on the full real waiting-time ray, using only preceding
selected-profile/reflection inputs. Neither Fisher nor a response row is needed. -/
theorem source14_1 {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : GeneralCenterDeficit.SelectedInputs h c r q) :
    Tendsto (CenterAverageLimit.errorLimit c) atTop (nhds 0) ∧
    ∀ D : ℝ,0<D → 0≤CenterAverageLimit.errorLimit c D ∧
      Tendsto (fun s : ℝ => ‖CausalCenterAverage.localCenter h (s-D) D-
        CausalCenterAverage.localAverage h (s-D) D‖^2) atTop
        (nhds (CenterAverageLimit.errorLimit c D)) := by
  have hb (t : ℝ) (ht : 0≤t) : |c t|≤1 := by
    rw [abs_of_nonneg (H.q_positive.le.trans (H.correlation_bounds t ht).1)]
    exact (H.correlation_bounds t ht).2
  refine ⟨CenterAverageDecay.errorLimit_tendsto H.correlation_continuous hb H.plateau_limit,?_⟩
  intro D hD
  have hl := CenterAverageReal.center_average_real_limit h H.correlation_continuous hD.le
    (H.translated_correlation D hD.le) (H.reflected_prefix D hD.le)
  have hn : 0≤CenterAverageLimit.errorLimit c D := ge_of_tendsto' hl (fun T => sq_nonneg _)
  have hshift : Tendsto (fun s : ℝ => s-D) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-D) tendsto_id
  exact ⟨hn,hl.comp hshift⟩

/-- The exact beta=beta_d cubic endpoint, q=1/2 and beta^2=4/3. Scalar
marginality is proved by arithmetic; no target response row is assumed. -/
theorem critical_endpoint_source14_3 {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} (hβ : β^2=(4/3:ℝ))
    (H : GeneralCenterDeficit.SelectedInputs h c r (1/2:ℝ))
    (hforget : ∀ s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (nhds 0))
    (hFisher : ∃ a : ℝ → ℝ,FisherMajorant 3 β d a) (k : Fin 3) :
    Tendsto (fun D : ℝ => limsup (ActualCorrelationProductSup.productSup k d (1/2) D) atTop)
      atTop (nhds 0) := by
  have hmarg : β^2*PlateauAlgebra.marginalityPolynomial 3 (1/2)=1 := by
    norm_num [PlateauAlgebra.marginalityPolynomial,hβ]
  exact source14_3 (GeneralCenterDeficit.cubic_inputs_of_marginality H hmarg) hforget hFisher k

end SphericalAging.ActualProductFromSelected
