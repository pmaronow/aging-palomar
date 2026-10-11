module

public import SphericalAging.PositiveRenewalCompactLimit

public section

/-! Explicit compact Lipschitz interval approximants for the true
finite-first-moment renewal theorem. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SphericalAging.RenewalIntervalHat
noncomputable section
set_option backward.isDefEq.respectTransparency false

@[expose] def intervalHat (a b ε : ℝ) (t : ℝ) : ℝ :=
  max 0 (min 1 (min ((t-a)/ε) ((b-t)/ε)))

theorem intervalHat_nonnegative (a b ε t : ℝ) : 0 ≤ intervalHat a b ε t := le_max_left _ _

theorem intervalHat_le_one (a b ε t : ℝ) : intervalHat a b ε t≤1 :=
  max_le (by norm_num) (min_le_left _ _)

theorem intervalHat_lipschitz (a b : ℝ) {ε : ℝ} (he : 0<ε) :
    LipschitzWith ⟨1/ε,by positivity⟩ (intervalHat a b ε) := by
  let K : ℝ≥0 := ⟨1/ε,by positivity⟩
  have hleft : LipschitzWith K (fun t : ℝ => (t-a)/ε) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |(x-a)/ε-(y-a)/ε|≤(1/ε)*|x-y|
    rw [←sub_div,show (x-a)-(y-a)=x-y by ring,abs_div,abs_of_pos he]
    exact le_of_eq (by ring)
  have hright : LipschitzWith K (fun t : ℝ => (b-t)/ε) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |(b-x)/ε-(b-y)/ε|≤(1/ε)*|x-y|
    rw [←sub_div,show (b-x)-(b-y)=-(x-y) by ring,abs_div,abs_neg,abs_of_pos he]
    exact le_of_eq (by ring)
  change LipschitzWith K (fun t : ℝ => max 0 (min 1 (min ((t-a)/ε) ((b-t)/ε))))
  simpa only [max_self] using (hleft.min hright).const_min 1 |>.const_max 0

theorem intervalHat_zero {a b ε t : ℝ} (he : 0<ε) (ht : t∉Icc a b) :
    intervalHat a b ε t=0 := by
  apply max_eq_left
  simp only [mem_Icc,not_and_or,not_le] at ht
  rcases ht with hta|hbt
  · exact (min_le_right _ _).trans ((min_le_left _ _).trans ((div_neg_of_neg_of_pos (by linarith) he).le))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans ((div_neg_of_neg_of_pos (by linarith) he).le))

theorem intervalHat_eq_one {a b ε t : ℝ} (he : 0<ε) (ht : t∈Icc (a+ε) (b-ε)) :
    intervalHat a b ε t=1 := by
  have hl : 1≤(t-a)/ε := (le_div_iff₀ he).mpr (by linarith [ht.1])
  have hr : 1≤(b-t)/ε := (le_div_iff₀ he).mpr (by linarith [ht.2])
  unfold intervalHat
  rw [min_eq_left (le_min hl hr)]
  norm_num

theorem intervalHat_support_radius (a b : ℝ) {ε : ℝ} (he : 0<ε) :
    ∀t : ℝ,t∉Icc (-(|a|+|b|+1)) (|a|+|b|+1) → intervalHat a b ε t=0 := by
  intro t ht
  apply intervalHat_zero he
  intro htab
  apply ht
  constructor <;> linarith [le_abs_self a,neg_abs_le a,le_abs_self b,neg_abs_le b,abs_nonneg a,abs_nonneg b,htab.1,htab.2]

theorem intervalHat_integrable (a b : ℝ) {ε : ℝ} (he : 0<ε) : Integrable (intervalHat a b ε) := by
  exact (intervalHat_lipschitz a b he).continuous.integrableOn_Icc.integrable_of_forall_notMem_eq_zero
    (fun t ht => intervalHat_zero he ht)

theorem intervalHat_integral_upper {a b ε : ℝ} (he : 0<ε) (hab : a≤b) :
    (∫t : ℝ,intervalHat a b ε t)≤b-a := by
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => intervalHat_zero he ht)]
  have hb : ∀t : ℝ,‖intervalHat a b ε t‖≤1 := by
    intro t
    rw [Real.norm_eq_abs,abs_of_nonneg (intervalHat_nonnegative a b ε t)]
    exact intervalHat_le_one a b ε t
  have h := norm_setIntegral_le_of_norm_le_const (μ:=volume) (s:=Icc a b)
    (by rw [Real.volume_Icc];exact ENNReal.ofReal_lt_top) (fun t _ => hb t)
  rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (intervalHat_nonnegative a b ε)),
    Real.volume_real_Icc_of_le hab,one_mul] at h
  exact h

theorem intervalHat_integral_lower {a b ε : ℝ} (he : 0<ε) :
    b-a-2*ε≤∫t : ℝ,intervalHat a b ε t := by
  have hi := intervalHat_integrable a b he
  have hnn := intervalHat_nonnegative a b ε
  by_cases hab : a+ε≤b-ε
  · have hmono : (∫t in Icc (a+ε) (b-ε),(1:ℝ))≤∫t in Icc (a+ε) (b-ε),intervalHat a b ε t := by
      apply setIntegral_mono_on (integrable_const (1:ℝ)) hi.integrableOn measurableSet_Icc
      intro t ht
      rw [intervalHat_eq_one he ht]
    have hsub : (∫t in Icc (a+ε) (b-ε),intervalHat a b ε t)≤∫t,intervalHat a b ε t :=
      setIntegral_le_integral hi (Eventually.of_forall hnn)
    rw [integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply MeasurableSet.univ,univ_inter,
      Real.volume_real_Icc_of_le hab] at hmono
    linarith
  · exact (by linarith : b-a-2*ε≤0).trans (integral_nonneg hnn)

end
end SphericalAging.RenewalIntervalHat
