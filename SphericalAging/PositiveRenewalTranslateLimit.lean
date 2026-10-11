module

public import SphericalAging.PositiveRenewalCompactKernel
public import SphericalAging.BoundedLipschitzCompactness
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

/-! Actual subsequential harmonic profiles of compactly supported Lipschitz
renewal convolutions at positive infinity. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SphericalAging.PositiveRenewalTranslateLimit
noncomputable section
set_option backward.isDefEq.respectTransparency false
open PositiveRenewalCompactKernel BoundedLipschitzCompactness AbsorptionCutoff.Renewal

/-- Actual bounded Lipschitz renewal convolutions have actual harmonic
translation limits. Compactness and dominated convergence are proved steps;
no constant-profile or convergence conclusion is assumed. -/
theorem compact_kernel_harmonic_translate_subsequence
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hp : ∀ᵐ y ∂μ,0<y)
    {H : ℝ → ℝ} {K : ℝ≥0} (hL : LipschitzWith K H) {R B : ℝ}
    (hs : ∀t : ℝ,t∉Icc (-R) R → H t=0) (hb : ∀t : ℝ,‖H t‖≤B)
    (c : ℕ → ℝ) (hc : Tendsto c atTop atTop) :
    ∃G : ℝ → ℝ,UniformContinuous G ∧
      (∀t : ℝ,‖G t‖≤B*(renewalMeasure μ (Icc 0 (2*R))).toReal) ∧
      (∀x : ℝ,G x=∫y,G (x-y) ∂μ) ∧
      ∃φ : ℕ → ℕ,StrictMono φ ∧ ∀s : Set ℝ,IsCompact s →
        TendstoUniformlyOn (fun n t => renewalConvolution μ H (c (φ n)+t)) G atTop s := by
  let F := renewalConvolution μ H
  let C := (renewalMeasure μ (Icc 0 (2*R))).toReal
  let M := B*C
  let K' : ℝ≥0 := K*⟨2*C,by positivity⟩
  have hFL : LipschitzWith K' F := compact_kernel_lipschitz hp hL hs hb
  have hFb : ∀t : ℝ,‖F t‖≤M := compact_kernel_uniform_bound hp hs hb
  have htrans (n : ℕ) : LipschitzWith K' (fun t : ℝ => F (c n+t)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm,add_sub_add_left_eq_sub] using hFL.dist_le_mul (c n+x) (c n+y)
  have htransB (n : ℕ) (t : ℝ) : F (c n+t)∈Icc (-M) M := by
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hFb (c n+t))
  obtain ⟨G,hGL,hGb,φ,hφ,hconv⟩ := bounded_lipschitz_subsequence
    (fun n t => F (c n+t)) htrans htransB
  have hpoint (t : ℝ) : Tendsto (fun n : ℕ => F (c (φ n)+t)) atTop (𝓝 (G t)) :=
    (hconv {t} isCompact_singleton).tendsto_at (mem_singleton t)
  refine ⟨G,hGL.uniformContinuous,?_,?_,φ,hφ,hconv⟩
  · intro t
    rw [Real.norm_eq_abs]
    exact abs_le.mpr (hGb t)
  · intro x
    have hI : Tendsto (fun n : ℕ => ∫y,F (c (φ n)+x-y) ∂μ)
        atTop (𝓝 (∫y,G (x-y) ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => M)
      · intro n
        exact (hFL.continuous.comp ((continuous_const.add continuous_const).sub continuous_id)).aestronglyMeasurable
      · exact integrable_const M
      · intro n
        exact Eventually.of_forall (fun y => hFb (c (φ n)+x-y))
      · exact Eventually.of_forall (fun y => by
          simpa only [add_sub_assoc] using hpoint (x-y))
    have hHzero : Tendsto (fun n : ℕ => H (c (φ n)+x)) atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      have hcenter : Tendsto (fun n : ℕ => c (φ n)+x) atTop atTop :=
        tendsto_atTop_add_const_right atTop x (hc.comp hφ.tendsto_atTop)
      filter_upwards [hcenter.eventually_gt_atTop R] with n hn
      exact (hs _ (fun ht => not_le_of_gt hn ht.2)).symm
    have hright : Tendsto (fun n : ℕ => H (c (φ n)+x)+∫y,F (c (φ n)+x-y) ∂μ)
        atTop (𝓝 (∫y,G (x-y) ∂μ)) := by simpa only [zero_add] using hHzero.add hI
    apply tendsto_nhds_unique (hpoint x)
    apply hright.congr'
    exact Eventually.of_forall (fun n =>
      (compact_kernel_renewal_equation hp hL.continuous.measurable hs hb (c (φ n)+x)).symm)

end
end SphericalAging.PositiveRenewalTranslateLimit
