module

public import SphericalAging.ProductVarianceDecomposition

public section

/-! Exact product-law variance decomposition for genuine L² observables,
including the unbounded physical Brownian pairing. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace SphericalAging.ProductL2VarianceDecomposition
open PredictableDriftTime
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {f : A×B→ℝ}

theorem fiber_memLp_two (h2 : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ,MemLp (fun y => f (x,y)) 2 ν := by
  filter_upwards [h2.aestronglyMeasurable.prodMk_left,h2.integrable_sq.prod_right_ae] with x hm hi
  exact (memLp_two_iff_integrable_sq hm).mpr hi

theorem mean_memLp_two (h2 : MemLp f 2 (μ.prod ν)) :
    MemLp (fun x => ∫ y,f (x,y) ∂ν) 2 μ := by
  have hm := h2.aestronglyMeasurable.integral_prod_right'
  apply (memLp_two_iff_integrable_sq hm).mpr
  have hs : AEStronglyMeasurable (fun x => (∫ y,f (x,y) ∂ν)^2) μ := hm.pow 2
  apply h2.integrable_sq.integral_prod_left.mono' hs
  filter_upwards [fiber_memLp_two h2] with x hx
  have hi := integral_sq_le_measure_mul_integral_sq ν (fun y => f (x,y)) hx
  simpa only [Real.norm_of_nonneg (sq_nonneg _),probReal_univ,one_mul] using hi

theorem variance_product_eq (h2 : MemLp f 2 (μ.prod ν)) :
    Integrable (fun x => variance (fun y => f (x,y)) ν) μ ∧
      variance f (μ.prod ν)=(∫ x,variance (fun y => f (x,y)) ν ∂μ)+
        variance (fun x => ∫ y,f (x,y) ∂ν) μ := by
  have hmean2 := mean_memLp_two h2
  have he : (fun x => variance (fun y => f (x,y)) ν)=ᵐ[μ]
      fun x => (∫ y,(f (x,y))^2 ∂ν)-(∫ y,f (x,y) ∂ν)^2 :=
    (fiber_memLp_two h2).mono (fun x hx => variance_eq_sub hx)
  have hi : Integrable (fun x => variance (fun y => f (x,y)) ν) μ :=
    (h2.integrable_sq.integral_prod_left.sub hmean2.integrable_sq).congr he.symm
  refine ⟨hi,?_⟩
  rw [variance_eq_sub h2,variance_eq_sub hmean2,integral_congr_ae he,
    integral_sub h2.integrable_sq.integral_prod_left hmean2.integrable_sq]
  simp only [Pi.pow_apply]
  rw [integral_prod _ h2.integrable_sq,integral_prod _ (h2.integrable (by norm_num))]
  ring

end SphericalAging.ProductL2VarianceDecomposition
