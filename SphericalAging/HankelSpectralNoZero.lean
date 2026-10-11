module

public import SphericalAging.HankelSpectralMoments

public section

/-! Normalization and continuity eliminate the zero spectral atom of the
constructed positive contraction law. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped InnerProductSpace NNReal Topology
namespace SphericalAging.HankelSpectralNoZero
open HankelReflection (HankelPositive)
open ComplexHankelShiftNorm ComplexHankelShift
open HankelSpectralDyadic HankelSpectralMoments

theorem space_nontrivial {c : ℝ → ℝ} (hc : HankelPositive c) (h0 : c 0=1) :
    Nontrivial (Space c hc) := by
  have hn : ‖feature c hc 0‖^2=1 := by
    rw [norm_sq_eq_re_inner (𝕜:=ℂ),feature_inner]
    change c (0+0)=1
    simpa only [zero_add] using h0
  refine ⟨⟨feature c hc 0,0,?_⟩⟩
  intro he
  rw [he,norm_zero,zero_pow (by norm_num)] at hn
  norm_num at hn

/-- The actual scalar spectral law gives zero mass to λ=0. -/
theorem law_zero_mass {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀t : ℝ,0≤t→|c t|≤1) (h0 : c 0=1)
    (hcont : ContinuousOn c (Ici 0)) :
    law c hc hb {x | (x:ℝ)=0}=0 := by
  letI := space_nontrivial hc h0
  letI := law_probability hc hb h0
  let S : Set (spectrum ℝ (shift c hc 1)) := {x | 0<(x:ℝ)}
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_subtype_coe
  have hlim : ∀ᵐ x : spectrum ℝ (shift c hc 1) ∂law c hc hb,
      Tendsto (fun n => (x:ℝ)^(dyadic n:ℝ)) atTop
        (𝓝 (S.indicator (fun _ => (1:ℝ)) x)) := by
    apply Eventually.of_forall
    intro x
    by_cases hx : (x:ℝ)=0
    · have hxS : x∉S := by dsimp [S]; rw [hx]; simp
      simp only [hx,Set.indicator_of_notMem hxS]
      have he : (fun n => (0:ℝ)^(dyadic n:ℝ))=fun _ => (0:ℝ) := by
        funext n
        exact Real.zero_rpow (ne_of_gt (show 0<(dyadic n:ℝ) from dyadic_pos n))
      rw [he]
      exact tendsto_const_nhds
    · have hxS : x∈S := lt_of_le_of_ne (spectrum_bounds hc hb x).1 (Ne.symm hx)
      rw [Set.indicator_of_mem hxS]
      have hp := (Real.continuousAt_rpow ((x:ℝ),0) (Or.inl hx)).tendsto.comp
        (tendsto_const_nhds.prodMk_nhds dyadic_tendsto_zero)
      simpa only [Real.rpow_zero,Function.comp_def] using hp
  have hdom := tendsto_integral_of_dominated_convergence (μ:=law c hc hb)
    (F:=fun n (x : spectrum ℝ (shift c hc 1)) => (x:ℝ)^(dyadic n:ℝ))
    (bound:=fun _ => (1:ℝ))
    (fun n => ((rpow_continuousOn_spectrum hc hb (dyadic_pos n).le).domRestrict).measurable.aestronglyMeasurable)
    (integrable_const 1)
    (fun n => Eventually.of_forall (spectral_power_bound hc hb _ (dyadic_pos n).le)) hlim
  have hd : Tendsto (fun n => (dyadic n:ℝ)) atTop (𝓝[Ici 0] 0) := by
    exact tendsto_nhdsWithin_iff.mpr ⟨dyadic_tendsto_zero,
      Eventually.of_forall (fun n => (dyadic n).coe_nonneg)⟩
  have hc0 := (hcont.continuousWithinAt (show (0:ℝ)∈Ici (0:ℝ) from by simp)).tendsto.comp hd
  rw [h0] at hc0
  have he : (fun n => ∫ x : spectrum ℝ (shift c hc 1),(x:ℝ)^(dyadic n:ℝ) ∂law c hc hb)=
      fun n => c (dyadic n) := by
    funext n
    simpa only [Nat.cast_one,one_mul] using integral_law_dyadic hc hb n 1
  rw [he] at hdom
  have hmass : law c hc hb S=1 := by
    have hi := tendsto_nhds_unique hdom hc0
    have hI : (∫ x : spectrum ℝ (shift c hc 1),S.indicator (fun _ => (1:ℝ)) x ∂law c hc hb)=
        (law c hc hb).real S := by
      simpa only [smul_eq_mul,mul_one] using (integral_indicator_const (μ:=law c hc hb) (1:ℝ) hS)
    rw [hI] at hi
    exact (ENNReal.toReal_eq_one_iff _).mp hi
  have hcompl : law c hc hb Sᶜ=0 := by
    rw [measure_compl hS (measure_ne_top _ _),measure_univ,hmass,tsub_self]
  apply le_antisymm _ bot_le
  calc
    law c hc hb {x | (x:ℝ)=0}≤law c hc hb Sᶜ := by
      apply measure_mono
      intro x hx
      show ¬0<(x:ℝ)
      rw [hx]
      exact lt_irrefl 0
    _ = 0 := hcompl

end SphericalAging.HankelSpectralNoZero
