module

public import SphericalAging.SphereGaussianVariance

public section

/-! Exact product-law variance decomposition and tensorization for
bounded measurable observables. All conditional means, second moments,
and Fubini exchanges are derived from the actual product measures. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace SphericalAging.ProductVarianceDecomposition
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

 lemma bounded_memLp {f : A → ℝ} (hf : StronglyMeasurable f) {M : ℝ}
    (hb : ∀ x,|f x|≤M) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable M (.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))

 lemma integral_abs_le {f : A → ℝ} (hf : StronglyMeasurable f) {M : ℝ}
    (hb : ∀ x,|f x|≤M) : |∫ x,f x ∂μ|≤M := by
  have hi : Integrable f μ := (bounded_memLp (μ := μ) hf hb).integrable (by norm_num)
  have hh := (norm_integral_le_integral_norm f).trans (integral_mono hi.norm (integrable_const M) hb)
  simpa only [Real.norm_eq_abs,integral_const,probReal_univ,one_smul] using hh

 theorem variance_product_eq {f : A × B → ℝ} (hf : StronglyMeasurable f) {M : ℝ}
    (hb : ∀ q,|f q|≤M) :
    Integrable (fun x => variance (fun y => f (x,y)) ν) μ ∧
      variance f (μ.prod ν)=(∫ x,variance (fun y => f (x,y)) ν ∂μ)+
        variance (fun x => ∫ y,f (x,y) ∂ν) μ := by
  have h2 : MemLp f 2 (μ.prod ν) := bounded_memLp hf hb
  have hx (x : A) : MemLp (fun y => f (x,y)) 2 ν := bounded_memLp
    (hf.comp_measurable (measurable_const.prodMk measurable_id)) (fun y => hb (x,y))
  have hmean : StronglyMeasurable (fun x => ∫ y,f (x,y) ∂ν) := StronglyMeasurable.integral_prod_right (f := fun x y => f (x,y)) hf
  have hmean2 : MemLp (fun x => ∫ y,f (x,y) ∂ν) 2 μ := bounded_memLp hmean
    (fun x => integral_abs_le (hf.comp_measurable (measurable_const.prodMk measurable_id)) (fun y => hb (x,y)))
  have he : (fun x => variance (fun y => f (x,y)) ν)=
      fun x => (∫ y,(f (x,y))^2 ∂ν)-(∫ y,f (x,y) ∂ν)^2 := funext (fun x => variance_eq_sub (hx x))
  have hi : Integrable (fun x => variance (fun y => f (x,y)) ν) μ := by
    rw [he]
    exact h2.integrable_sq.integral_prod_left.sub hmean2.integrable_sq
  refine ⟨hi,?_⟩
  rw [variance_eq_sub h2,variance_eq_sub hmean2,he,
    integral_sub h2.integrable_sq.integral_prod_left hmean2.integrable_sq]
  simp only [Pi.pow_apply]
  rw [integral_prod _ h2.integrable_sq,integral_prod _ (h2.integrable (by norm_num))]
  ring

 theorem variance_mean_le_mean_variance {f : A × B → ℝ} (hf : StronglyMeasurable f)
    {M : ℝ} (hb : ∀ q,|f q|≤M) :
    variance (fun x => ∫ y,f (x,y) ∂ν) μ≤∫ y,variance (fun x => f (x,y)) μ ∂ν := by
  let h : B → ℝ := fun y => ∫ x,f (x,y) ∂μ
  let g : A → ℝ := fun x => ∫ y,f (x,y) ∂ν
  let c : A × B → ℝ := fun q => f q-h q.2
  have h2 : MemLp f 2 (μ.prod ν) := bounded_memLp hf hb
  have hh : StronglyMeasurable h := StronglyMeasurable.integral_prod_left (f := fun x y => f (x,y)) hf
  have hhb (y : B) : |h y|≤M := integral_abs_le
    (hf.comp_measurable (measurable_id.prodMk measurable_const)) (fun x => hb (x,y))
  have hg : StronglyMeasurable g := StronglyMeasurable.integral_prod_right (f := fun x y => f (x,y)) hf
  have hgb (x : A) : |g x|≤M := integral_abs_le
    (hf.comp_measurable (measurable_const.prodMk measurable_id)) (fun y => hb (x,y))
  have hg2 : MemLp g 2 μ := bounded_memLp hg hgb
  have hc : StronglyMeasurable c := hf.sub hh.comp_snd
  have hcb (q : A × B) : |c q|≤2*M := (abs_sub (f q) (h q.2)).trans (by linarith [hb q,hhb q.2])
  have hc2 : MemLp c 2 (μ.prod ν) := bounded_memLp hc hcb
  have hcx (x : A) : MemLp (fun y => c (x,y)) 2 ν := bounded_memLp
    (hc.comp_measurable (measurable_const.prodMk measurable_id)) (fun y => hcb (x,y))
  have hmean : (∫ y,h y ∂ν)=∫ x,g x ∂μ := (integral_integral_swap (f := fun x y => f (x,y)) (h2.integrable (by norm_num))).symm
  have hp (x : A) : (g x-(∫ z,g z ∂μ))^2≤∫ y,(c (x,y))^2 ∂ν := by
    have hhcs := PredictableDriftTime.integral_sq_le_measure_mul_integral_sq ν (fun y => c (x,y)) (hcx x)
    have he : (∫ y,c (x,y) ∂ν)=g x-(∫ z,g z ∂μ) := by
      change (∫ y,f (x,y)-h y ∂ν)=_
      have hxi : Integrable (fun y => f (x,y)) ν := (bounded_memLp (μ := ν)
        (hf.comp_measurable (measurable_const.prodMk measurable_id)) (fun y => hb (x,y))).integrable (by norm_num)
      have hhi : Integrable h ν := (bounded_memLp (μ := ν) hh hhb).integrable (by norm_num)
      rw [integral_sub hxi hhi,hmean]
    simpa only [he,probReal_univ,one_mul] using hhcs
  have he (y : B) : (∫ x,(c (x,y))^2 ∂μ)=variance (fun x => f (x,y)) μ := by
    have hfy : StronglyMeasurable (fun x => f (x,y)) := hf.comp_measurable (measurable_id.prodMk measurable_const)
    rw [variance_eq_integral hfy.measurable.aemeasurable]
  rw [variance_eq_integral hg.measurable.aemeasurable]
  refine (integral_mono (hg2.sub (memLp_const _)).integrable_sq hc2.integrable_sq.integral_prod_left hp).trans_eq ?_
  rw [integral_integral_swap hc2.integrable_sq]
  exact integral_congr_ae (.of_forall he)

 theorem variance_product_le_sum {f : A × B → ℝ} (hf : StronglyMeasurable f) {M : ℝ}
    (hb : ∀ q,|f q|≤M) :
    variance f (μ.prod ν)≤(∫ x,variance (fun y => f (x,y)) ν ∂μ)+
      (∫ y,variance (fun x => f (x,y)) μ ∂ν) := by
  rw [(variance_product_eq hf hb).2]
  exact add_le_add le_rfl (variance_mean_le_mean_variance hf hb)

end SphericalAging.ProductVarianceDecomposition
