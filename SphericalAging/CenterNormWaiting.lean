module

public import SphericalAging.CenterNormalization

public section

/-! Uniform real waiting-time control of the actual normalization denominators. -/
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology InnerProductSpace
namespace SphericalAging.CenterNormWaiting
open CKSpecification CKPhysicalConsequences CausalCenterAverage CenterAverageReal
open PrefixReflection PrefixRectangleStability CenterNormalization

theorem center_norm_product_waiting {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {c : ℝ → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hA : 0 ≤ c (2*D)) (hA1 : c (2*D) ≤ 1)
    (hQ : TendstoUniformlyOn (fun T => Function.uncurry (futureKernel h T))
      (fun z => c (z.1+z.2)) atTop (square D)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ S : ℝ in atTop, ∀ s t : ℝ, S+D ≤ s → S+D ≤ t →
      |‖localCenter h (t-D) D‖*‖localCenter h (s-D) D‖-c (2*D)| ≤ ε := by
  let k := Real.sqrt (c (2*D))
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  have hk1 : k ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hA1
  have hk2 : k^2 = c (2*D) := Real.sq_sqrt hA
  have hn := center_real_norm_limit h hD hQ
  have he := (tendsto_order.1 ((hn.sub_const k).abs)).2
    (ε/2) (by dsimp only [k]; simp only [sub_self,abs_zero]; positivity)
  obtain ⟨U,hU⟩ := eventually_atTop.mp he
  filter_upwards [eventually_ge_atTop (max U 0)] with S hS
  intro s t hs ht
  have hS0 : 0 ≤ S := (le_max_right U 0).trans hS
  have hns := hU (s-D) (by linarith [le_max_left U 0])
  have hnt := hU (t-D) (by linarith [le_max_left U 0])
  have hs0 : 0 ≤ s := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hs1 : ‖localCenter h (s-D) D‖ ≤ 1 := by
    apply prefixVector_norm_le_one h (physical_bounds_of_equations h)
    simpa only [sub_add_cancel] using hs0
  have ht1 : ‖localCenter h (t-D) D‖ ≤ 1 := by
    apply prefixVector_norm_le_one h (physical_bounds_of_equations h)
    simpa only [sub_add_cancel] using ht0
  let a := ‖localCenter h (t-D) D‖
  let b := ‖localCenter h (s-D) D‖
  have hb0 : 0 ≤ b := norm_nonneg _
  have heq : a*b-c (2*D) = (a-k)*b+k*(b-k) := by rw [←hk2]; ring
  change |a*b-c (2*D)| ≤ ε
  rw [heq]
  calc
    _ ≤ |(a-k)*b|+|k*(b-k)| := abs_add_le _ _
    _ = |a-k| *b+k*|b-k| := by rw [abs_mul,abs_mul,abs_of_nonneg hb0,abs_of_nonneg hk0]
    _ ≤ |a-k|+|b-k| := by
      exact add_le_add (by simpa using mul_le_mul_of_nonneg_left hs1 (abs_nonneg (a-k)))
        (by simpa using mul_le_mul_of_nonneg_right hk1 (abs_nonneg (b-k)))
    _ ≤ ε := by dsimp only [a,b] at *; linarith

/-- Positive limiting norm gives genuine nonzero centers and unit normalized
centers for all sufficiently late terminal times. -/
theorem normalized_centers_eventually_unit {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {c : ℝ → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hA : 0 < c (2*D))
    (hQ : TendstoUniformlyOn (fun T => Function.uncurry (futureKernel h T))
      (fun z => c (z.1+z.2)) atTop (square D)) :
    ∀ᶠ S : ℝ in atTop, ∀ s : ℝ, S+D ≤ s →
      0 < ‖localCenter h (s-D) D‖ ∧ ‖normalizedCenter h s D‖ = 1 := by
  have he := (center_real_norm_limit h hD hQ).eventually (lt_mem_nhds (Real.sqrt_pos.mpr hA))
  obtain ⟨U,hU⟩ := eventually_atTop.mp he
  filter_upwards [eventually_ge_atTop U] with S hS
  intro s hs
  have hn := hU (s-D) (by linarith)
  exact ⟨hn,normalizedCenter_norm h hn⟩

end SphericalAging.CenterNormWaiting
