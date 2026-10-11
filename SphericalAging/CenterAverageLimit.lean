module

public import SphericalAging.CausalCenterAverage
public import SphericalAging.CompactAverageLimits

public section

/-! The actual fixed-age center-average error limit from translated CK kernels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped InnerProductSpace Topology NNReal
open Set Filter MeasureTheory
namespace SphericalAging.CenterAverageLimit
open CKSpecification CKPhysicalConsequences CausalTree CausalTreeRealization PrefixReflection
open GreenCovariance CKKernelBounds BackwardResponse WindowAverages CausalCenterAverage
open StationaryPrefixConsequences PrefixRectangleStability CompactAverageLimits

@[expose] def errorLimit (c : ℝ→ℝ) (D : ℝ) : ℝ :=
  c (2*D)+2/D^2*(∫ τ in (0:ℝ)..D,(D-τ)*c τ)-2/D*(∫ τ in D..2*D,c τ)

@[expose] def correlationRow (d : CKData) (T u v : ℝ) : ℝ := clampedCorrelation d (T+u) (T+v)

@[expose] def reflectedRow {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) (T D a : ℝ) : ℝ :=
  prefixKernel h T (max 0 (T+D)) (max 0 (T+a))

theorem correlationRow_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℝ) : Continuous (Function.uncurry (correlationRow d T)) :=
  (clampedCorrelation_continuous h).comp
    ((continuous_const.add continuous_fst).prodMk (continuous_const.add continuous_snd))

theorem correlationRow_abs_le_one {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T u v : ℝ) : |correlationRow d T u v|≤1 := by
  rw [correlationRow,abs_of_nonneg (clampedCorrelation_nonnegative (physical_bounds_of_equations h) _ _)]
  exact ((physical_bounds_of_equations h).1 _ _ (le_max_left _ _) (le_max_left _ _)).2

theorem reflectedRow_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T D : ℝ) : Continuous (reflectedRow h T D) :=
  by
    change Continuous (fun a : ℝ=>
      (fun z : ℝ×ℝ=>prefixKernel h T (max 0 z.1) (max 0 z.2)) (T+D,T+a))
    exact (prefixKernel_clamped_continuous h (physical_bounds_of_equations h) T).comp
      (continuous_const.prodMk (continuous_const.add continuous_id))

theorem reflectedRow_abs_le_one {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T D a : ℝ) : |reflectedRow h T D a|≤1 :=
  prefixKernel_abs_le_one h (physical_bounds_of_equations h) T (le_max_left _ _) (le_max_left _ _)

theorem localAverage_norm_sq_clamped {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T D : ℝ} (hT : 0≤T) (hD : 0≤D) :
    ‖localAverage h T D‖^2=(D⁻¹)^2*(∫ u in (0:ℝ)..D,∫ v in (0:ℝ)..D,correlationRow d T u v) := by
  rw [localAverage_norm_sq h hT hD]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hD] at hu
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hD] at hv
  dsimp only [correlationRow]
  rw [clampedCorrelation_eq (add_nonneg hT hu.1) (add_nonneg hT hv.1)]

theorem localCenter_average_inner_clamped {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T D : ℝ} (hT : 0≤T) (hD : 0≤D) :
    inner ℝ (localCenter h T D) (localAverage h T D)=D⁻¹*(∫ a in (0:ℝ)..D,reflectedRow h T D a) := by
  rw [localCenter_average_inner h hT hD]
  congr 1
  apply intervalIntegral.integral_congr
  intro a ha
  rw [uIcc_of_le hD] at ha
  dsimp only [reflectedRow,futureKernel]
  rw [max_eq_right (add_nonneg hT hD),max_eq_right (add_nonneg hT ha.1)]

/-- Full fixed-age limit of the actual center-average squared distance. -/
theorem center_average_limit {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℕ→ℝ} (hT : ∀ n,0≤T n)
    {c : ℝ→ℝ} (hc : ContinuousOn c (Ici 0)) {D : ℝ} (hD : 0≤D)
    (hC : TendstoUniformlyOn (fun n (z : ℝ×ℝ)=>d.C (T n+z.1) (T n+z.2))
      (fun z=>c |z.1-z.2|) atTop (square D))
    (hQ : TendstoUniformlyOn (fun n=>Function.uncurry (futureKernel h (T n)))
      (fun z=>c (z.1+z.2)) atTop (square D)) :
    Tendsto (fun n=>‖localCenter h (T n) D-localAverage h (T n) D‖^2) atTop (𝓝 (errorLimit c D)) := by
  have hI : Tendsto (fun n=>∫ u in (0:ℝ)..D,∫ v in (0:ℝ)..D,correlationRow d (T n) u v) atTop
      (𝓝 (∫ u in (0:ℝ)..D,∫ v in (0:ℝ)..D,c |u-v|)) := by
    apply double_integral_tendsto (fun n=>correlationRow_continuous h (T n)) hD
      (fun n u v=>correlationRow_abs_le_one h (T n) u v)
    intro u hu v hv
    have hl := hC.tendsto_at (x:=(u,v)) ⟨hu,hv⟩
    have heq : (fun n=>correlationRow d (T n) u v)=(fun n=>d.C (T n+u) (T n+v)) := by
      funext n
      exact clampedCorrelation_eq (add_nonneg (hT n) hu.1) (add_nonneg (hT n) hv.1)
    rw [heq]
    exact hl
  have hJ : Tendsto (fun n=>∫ a in (0:ℝ)..D,reflectedRow h (T n) D a) atTop
      (𝓝 (∫ a in (0:ℝ)..D,c (D+a))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _=>(1:ℝ))
    · exact Eventually.of_forall (fun n=>(reflectedRow_continuous h (T n) D).aestronglyMeasurable)
    · exact Eventually.of_forall (fun n=>ae_of_all _ (fun a _=>by
        simpa only [Real.norm_eq_abs] using reflectedRow_abs_le_one h (T n) D a))
    · exact intervalIntegrable_const
    · apply ae_of_all
      intro a ha
      rw [uIoc_of_le hD] at ha
      have hl := hQ.tendsto_at (x:=(D,a)) ⟨⟨hD,le_rfl⟩,⟨ha.1.le,ha.2⟩⟩
      have heq : (fun n=>reflectedRow h (T n) D a)=(fun n=>futureKernel h (T n) D a) := by
        funext n
        dsimp only [reflectedRow,futureKernel]
        rw [max_eq_right (add_nonneg (hT n) hD),max_eq_right (add_nonneg (hT n) ha.1.le)]
      rw [heq]
      exact hl
  have hnorm := prefix_norm_of_uniform_reflection h hD hQ
  change Tendsto (fun n=>‖localCenter h (T n) D‖^2) atTop (𝓝 (c (2*D))) at hnorm
  have havg : Tendsto (fun n=>‖localAverage h (T n) D‖^2) atTop
      (𝓝 ((D⁻¹)^2*(∫ u in (0:ℝ)..D,∫ v in (0:ℝ)..D,c |u-v|))) := by
    convert hI.const_mul ((D⁻¹)^2) using 1
    funext n
    exact localAverage_norm_sq_clamped h (hT n) hD
  have hcross : Tendsto (fun n=>inner ℝ (localCenter h (T n) D) (localAverage h (T n) D)) atTop
      (𝓝 (D⁻¹*(∫ a in (0:ℝ)..D,c (D+a)))) := by
    convert hJ.const_mul D⁻¹ using 1
    funext n
    exact localCenter_average_inner_clamped h (hT n) hD
  have hc0 : Continuous (fun x=>c (max 0 x)) :=
    hc.comp_continuous (continuous_const.max continuous_id) (fun x=>le_max_left 0 x)
  have hlag : (∫ u in (0:ℝ)..D,∫ v in (0:ℝ)..D,c |u-v|)=2*(∫ τ in (0:ℝ)..D,(D-τ)*c τ) := by
    have hs := square_abs_lag (fun x=>c (max 0 x)) hc0 hD
    have hmax (x : ℝ) : max 0 |x|=|x| := max_eq_right (abs_nonneg x)
    simp only [hmax] at hs
    rw [hs]
    congr 1
    apply intervalIntegral.integral_congr
    intro τ hτ
    rw [uIcc_of_le hD] at hτ
    dsimp only
    rw [max_eq_right hτ.1]
  have hshift : (∫ a in (0:ℝ)..D,c (D+a))=(∫ τ in D..2*D,c τ) := by
    simpa only [add_zero,show D+D=2*D from by ring] using
      intervalIntegral.integral_comp_add_left c D (a:=0) (b:=D)
  have hl := (hnorm.add havg).sub (hcross.const_mul 2)
  convert hl using 1
  · funext n
    rw [norm_sub_sq_real]
    ring
  · rw [hlag,hshift]
    unfold errorLimit
    simp only [div_eq_mul_inv,inv_pow]
    ring

theorem errorLimit_nonneg {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℕ→ℝ} (hT : ∀ n,0≤T n)
    {c : ℝ→ℝ} (hc : ContinuousOn c (Ici 0)) {D : ℝ} (hD : 0≤D)
    (hC : TendstoUniformlyOn (fun n (z : ℝ×ℝ)=>d.C (T n+z.1) (T n+z.2))
      (fun z=>c |z.1-z.2|) atTop (square D))
    (hQ : TendstoUniformlyOn (fun n=>Function.uncurry (futureKernel h (T n)))
      (fun z=>c (z.1+z.2)) atTop (square D)) : 0≤errorLimit c D :=
  ge_of_tendsto (center_average_limit h hT hc hD hC hQ) (Eventually.of_forall (fun _=>sq_nonneg _))

end SphericalAging.CenterAverageLimit
