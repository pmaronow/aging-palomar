module

public import SphericalAging.ScalarConstraints

public section

/-! Derive the exact integrated uniqueness solution from the preceding
stationary differential equations and physical bounds. Negative-time values
are represented by the continuous nonnegative-ray extension. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace SphericalAging.StationaryProfileUniquenessBridge
open ScalarConstraints StationaryUniqueness

theorem integrated_of_stationary {n : ℕ} {B ell : ℝ} {c r : ℝ → ℝ}
    (H : StationaryInputs n B ell c r)
    (hc : ∀t : ℝ,0≤t → c t≤1) (hr : ∀t : ℝ,0≤t → r t≤1) :
    IntegratedSolution n ell (B*((n:ℝ)+1)) (rayExtension c) (rayExtension r) := by
  refine ⟨(rayExtension_continuous c H.continuous_c).measurable,
    (rayExtension_continuous r H.continuous_r).measurable,?_,?_,?_⟩
  · intro T hT
    refine ⟨1,le_rfl,?_⟩
    intro t ht
    rw [rayExtension_eq c t ht.1,rayExtension_eq r t ht.1,
      abs_of_nonneg (H.correlation_nonnegative t ht.1),
      abs_of_nonneg (H.response_nonnegative t ht.1)]
    exact ⟨hc t ht.1,hr t ht.1⟩
  · intro t ht
    rw [rayExtension_eq c t ht]
    have he : (∫u in (0:ℝ)..t,rayExtension r u)=∫u in (0:ℝ)..t,r u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ht] at hu
      exact rayExtension_eq r u hu.1
    rw [he,stationary_integral_response n B ell c r H t ht]
    ring
  · intro t ht
    rw [rayExtension_eq r t ht]
    have he : (∫v in (0:ℝ)..t,-ell*rayExtension r v+
        B*((n:ℝ)+1)*memory n (rayExtension c) (rayExtension r) v)=
        ∫v in (0:ℝ)..t,-ell*r v+B*((n:ℝ)+1)*causalMemory n c r v := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le ht] at hv
      dsimp only
      rw [rayExtension_eq r v hv.1,memory_eq_interval n _ _ v hv.1]
      change -ell*r v+B*((n:ℝ)+1)*causalMemory n (rayExtension c) (rayExtension r) v=
        -ell*r v+B*((n:ℝ)+1)*causalMemory n c r v
      rw [extended_memory_eq n c r v hv.1]
    rw [he]
    have hir : IntervalIntegrable r volume 0 t :=
      (H.continuous_r.mono (by rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)).intervalIntegrable
    have him : IntervalIntegrable (causalMemory n c r) volume 0 t :=
      ((causalMemory_continuousOn n c r H.continuous_c H.continuous_r).mono
        (by rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)).intervalIntegrable
    rw [intervalIntegral.integral_add (hir.const_mul _) (him.const_mul _),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
      stationary_integral_response n B ell c r H t ht]
    have hh := stationary_integrated_response_equation n B ell c r H t ht
    linarith

theorem stationary_profiles_unique {n : ℕ} {B ell : ℝ} {c r c' r' : ℝ → ℝ}
    (H : StationaryInputs n B ell c r) (H' : StationaryInputs n B ell c' r')
    (hc : ∀t : ℝ,0≤t → c t≤1) (hr : ∀t : ℝ,0≤t → r t≤1)
    (hc' : ∀t : ℝ,0≤t → c' t≤1) (hr' : ∀t : ℝ,0≤t → r' t≤1) :
    ∀t : ℝ,0≤t → c t=c' t ∧ r t=r' t := by
  intro t ht
  have hh := integrated_stationary_unique n ell (B*((n:ℝ)+1))
    (rayExtension c) (rayExtension r) (rayExtension c') (rayExtension r')
    (integrated_of_stationary H hc hr) (integrated_of_stationary H' hc' hr') t ht
  simpa only [rayExtension_eq _ t ht] using hh

end SphericalAging.StationaryProfileUniquenessBridge
