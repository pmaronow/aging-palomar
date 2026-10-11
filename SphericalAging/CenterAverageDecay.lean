module

public import SphericalAging.CenterAverageLimit
public import SphericalAging.CenterAverageScaling

public section

/-! Vanishing smoothing error of actual causal centers. -/
noncomputable section
open scoped Topology InnerProductSpace
open Set Filter MeasureTheory
namespace SphericalAging.CenterAverageDecay
open CenterAverageLimit CenterAverageScaling

/-- Genuine affine scaling of both compact integrals in the error formula. -/
theorem errorLimit_scaled (c : ℝ→ℝ) (D : ℝ) (hD : D≠0) :
    errorLimit c D=scaledError c D := by
  have hw : (∫ τ in (0:ℝ)..D,(D-τ)*c τ)=
      D^2*(∫ u in (0:ℝ)..1,(1-u)*c (D*u)) := by
    have hs := intervalIntegral.smul_integral_comp_mul_left
      (fun τ=>(D-τ)*c τ) (a:=0) (b:=1) D
    simp only [mul_zero,mul_one,smul_eq_mul] at hs
    rw [←hs]
    have he : (∫ u in (0:ℝ)..1,(D-D*u)*c (D*u))=
        D*(∫ u in (0:ℝ)..1,(1-u)*c (D*u)) := by
      rw [←intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      ring
    rw [he]
    ring
  have hr : (∫ τ in D..2*D,c τ)=D*(∫ u in (1:ℝ)..2,c (D*u)) := by
    have hs := intervalIntegral.smul_integral_comp_mul_left c (a:=1) (b:=2) D
    simpa only [mul_one,smul_eq_mul,mul_comm D 2] using hs.symm
  unfold errorLimit scaledError
  rw [hw,hr]
  field_simp [hD]

/-- The stationary center-average error tends to zero from only genuine
ray continuity, the physical bound, and the profile's plateau limit. -/
theorem errorLimit_tendsto {c : ℝ→ℝ} {q : ℝ}
    (hc : ContinuousOn c (Ici 0)) (hb : ∀ t,0≤t→|c t|≤1)
    (hlim : Tendsto c atTop (𝓝 q)) : Tendsto (errorLimit c) atTop (𝓝 0) := by
  apply (scaledError_tendsto hc hb hlim).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with D hD
  exact (errorLimit_scaled c D hD.ne').symm

open CKSpecification CausalCenterAverage PrefixReflection PrefixRectangleStability

/-- Complete source center-average lemma, for actual CK tree centers and
actual Bochner averages. The finite-age squared error has its displayed limit,
is nonnegative, and then vanishes as the age tends to infinity. -/
theorem causal_centers_approximated_by_local_averages {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℕ→ℝ} (hT : ∀ n,0≤T n)
    {c : ℝ→ℝ} {q : ℝ} (hc : ContinuousOn c (Ici 0))
    (hb : ∀ t,0≤t→|c t|≤1) (hlim : Tendsto c atTop (𝓝 q))
    (hC : ∀ D : ℝ,0≤D→TendstoUniformlyOn
      (fun n (z : ℝ×ℝ)=>d.C (T n+z.1) (T n+z.2)) (fun z=>c |z.1-z.2|) atTop (square D))
    (hQ : ∀ D : ℝ,0≤D→TendstoUniformlyOn
      (fun n=>Function.uncurry (futureKernel h (T n))) (fun z=>c (z.1+z.2)) atTop (square D)) :
    Tendsto (errorLimit c) atTop (𝓝 0) ∧
    (∀ D : ℝ,0<D→0≤errorLimit c D ∧
      Tendsto (fun n=>‖localCenter h (T n) D-localAverage h (T n) D‖^2)
        atTop (𝓝 (errorLimit c D))) :=
  ⟨errorLimit_tendsto hc hb hlim,fun D hD=>
    ⟨errorLimit_nonneg h hT hc hD.le (hC D hD.le) (hQ D hD.le),
      center_average_limit h hT hc hD.le (hC D hD.le) (hQ D hD.le)⟩⟩

end SphericalAging.CenterAverageDecay
