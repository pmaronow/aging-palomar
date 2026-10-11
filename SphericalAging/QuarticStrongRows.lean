module

public import SphericalAging.QuarticResponseLocalization
public import SphericalAging.UniformResponseRows

public section

/-! Actual positive-plateau quartic source 11.1 and 11.2, from the independent
selected-profile, FDT, reflected-prefix and scalar-marginality inputs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.QuarticStrongRows
open CKSpecification QuarticResponseLocalization StrongResponseConsequences UniformResponseRows

/-- Every source 11.1 assertion, with no row/Fisher/Gram input. -/
theorem quartic_source11_1 {β : ℝ} {d : CKData} {h : CKEquations 4 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q) : Conclusions d r :=
  wholeclaims_of_remote h H.response_continuous H.response_integrable H.translated_response
    (fun _ hε => quartic_remote_localization H hε)

/-- Response monotonicity comes from the law constructed from the actual
reflected prefix and the source ordinary FDT, rather than from a premise. -/
theorem quartic_response_antitone {β : ℝ} {d : CKData} {h : CKEquations 4 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q) : AntitoneOn r (Ici 0) := by
  have hH : HankelReflection.HankelPositive c := by
    apply StationaryPrefixConsequences.hankel_positive_of_uniform_reflection h
      (T:=fun n : ℕ => (n:ℝ))
    intro A hA
    exact (H.reflected_prefix A hA).seq_tendstoUniformlyOn
      (fun n : ℕ => (n:ℝ)) tendsto_natCast_atTop_atTop
  have hb (t : ℝ) (ht : 0≤t) : |c t|≤1 := by
    rw [abs_of_nonneg (H.q_positive.le.trans (H.correlation_bounds t ht).1)]
    exact (H.correlation_bounds t ht).2
  obtain ⟨ν,hν,hneg,hatom,hrep,hcsmooth,hrsmooth,hcsign,hrsign⟩ :=
    StationarySpectralRepresentation.hankel_spectral_representation hH hb
      H.correlation_initial H.correlation_continuous H.plateau_limit H.fdt
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) H.response_continuous
  · simpa only [interior_Ici] using hrsmooth.differentiableOn (by simp)
  · intro t ht
    rw [interior_Ici] at ht
    have hh := hrsign 1 t ht
    simp only [pow_one,iteratedDeriv_one,neg_one_mul] at hh
    linarith

/-- Both source 11.2 assertions in the positive quartic case, with only the
source preceding fixed-wait selection hypothesis additional to Inputs. -/
theorem quartic_source11_2 {β : ℝ} {d : CKData} {h : CKEquations 4 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q)
    (hforget : ∀ s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (nhds 0)) :
    Tendsto (rowSup d r) atTop (nhds 0) ∧
    ∀ s t : ℕ → ℝ,Tendsto s atTop atTop → Tendsto (fun n => t n-s n) atTop atTop →
      Tendsto (fun n => d.R (t n) (s n)) atTop (nhds 0) :=
  source11_2 h H.response_continuous H.response_integrable (quartic_response_antitone H)
    H.translated_response hforget (quartic_source11_1 H)

end SphericalAging.QuarticStrongRows
