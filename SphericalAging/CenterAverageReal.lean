module

public import SphericalAging.CenterAverageDecay

public section

/-! The fixed-age center-average limit along the entire real waiting-time ray.
The extension is proved by the sequential criterion, using the actual preceding
uniform kernel limits. -/
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology InnerProductSpace
namespace SphericalAging.CenterAverageReal
open CKSpecification CausalCenterAverage CenterAverageLimit PrefixReflection PrefixRectangleStability

/-- The actual center-average squared error has its source limit as real waiting
time tends to infinity, rather than only along one chosen sequence. -/
theorem center_average_real_limit {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {c : ℝ → ℝ} (hc : ContinuousOn c (Ici 0))
    {D : ℝ} (hD : 0 ≤ D)
    (hC : TendstoUniformlyOn (fun T (z : ℝ×ℝ) => d.C (T+z.1) (T+z.2))
      (fun z => c |z.1-z.2|) atTop (square D))
    (hQ : TendstoUniformlyOn (fun T => Function.uncurry (futureKernel h T))
      (fun z => c (z.1+z.2)) atTop (square D)) :
    Tendsto (fun T : ℝ => ‖localCenter h T D-localAverage h T D‖^2) atTop
      (nhds (errorLimit c D)) := by
  apply tendsto_iff_seq_tendsto.mpr
  intro T hT
  let S : ℕ → ℝ := fun n => max 0 (T n)
  have hS : Tendsto S atTop atTop := tendsto_atTop_mono (fun n => le_max_right 0 (T n)) hT
  have hl := center_average_limit h (T := S) (fun n => le_max_left 0 (T n)) hc hD
    (hC.seq_tendstoUniformlyOn S hS) (hQ.seq_tendstoUniformlyOn S hS)
  apply hl.congr'
  filter_upwards [hT.eventually (eventually_ge_atTop (0 : ℝ))] with n hn
  change ‖localCenter h (max 0 (T n)) D-localAverage h (max 0 (T n)) D‖^2 = _
  rw [max_eq_right hn]
  rfl

/-- Consequently the actual norm error converges to the square root of the
source error, uniformly over all sufficiently late waiting times. -/
theorem center_average_real_norm_limit {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {c : ℝ → ℝ} (hc : ContinuousOn c (Ici 0))
    {D : ℝ} (hD : 0 ≤ D)
    (hC : TendstoUniformlyOn (fun T (z : ℝ×ℝ) => d.C (T+z.1) (T+z.2))
      (fun z => c |z.1-z.2|) atTop (square D))
    (hQ : TendstoUniformlyOn (fun T => Function.uncurry (futureKernel h T))
      (fun z => c (z.1+z.2)) atTop (square D)) :
    Tendsto (fun T : ℝ => ‖localCenter h T D-localAverage h T D‖) atTop
      (nhds (Real.sqrt (errorLimit c D))) := by
  simpa only [Real.sqrt_sq (norm_nonneg _)] using
    (center_average_real_limit h hc hD hC hQ).sqrt

/-- The actual center norm along the full real ray follows by reading the
reflected Gram kernel on the diagonal. -/
theorem center_real_norm_limit {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {c : ℝ → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hQ : TendstoUniformlyOn (fun T => Function.uncurry (futureKernel h T))
      (fun z => c (z.1+z.2)) atTop (square D)) :
    Tendsto (fun T : ℝ => ‖localCenter h T D‖) atTop (nhds (Real.sqrt (c (2*D)))) := by
  have hl := hQ.tendsto_at (x := (D,D)) ⟨⟨hD,le_rfl⟩,⟨hD,le_rfl⟩⟩
  have hsq : Tendsto (fun T : ℝ => ‖localCenter h T D‖^2) atTop (nhds (c (2*D))) := by
    convert hl using 1
    · funext T
      exact (real_inner_self_eq_norm_sq (localCenter h T D)).symm
    · congr 1
      ring
  simpa only [Real.sqrt_sq (norm_nonneg _)] using hsq.sqrt

end SphericalAging.CenterAverageReal
