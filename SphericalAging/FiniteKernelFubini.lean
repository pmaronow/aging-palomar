module

public import SphericalAging.ActualResponseCoefficientIntegral

public section

/-! Finite coefficient and branch sums commute with actual four-factor
kernel integrals. All conditional integrability is derived from joint
integrability, including the sphere-before-disorder order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.FiniteKernelFubini
open MeasureTheory
open scoped BigOperators
variable {I B S J X W : Type*} [Fintype I] [Fintype B]
  [MeasurableSpace S] [MeasurableSpace J] [MeasurableSpace X] [MeasurableSpace W]
  {ν : Measure S} {μJ : Measure J} {μX : Measure X} {μW : Measure W}
  [SFinite ν] [SFinite μJ] [SFinite μX] [SFinite μW]

theorem conditional_disorder_integrable_ae {f : S×((J×X)×W)→ℝ}
    (hf : Integrable f (ν.prod ((μJ.prod μX).prod μW))) :
    ∀ᵐx ∂μX,Integrable (fun j => ∫s,∫w,f (s,((j,x),w)) ∂μW ∂ν) μJ := by
  have ha := (measurePreserving_prodAssoc ν (μJ.prod μX) μW).integrable_comp_of_integrable hf
  exact ha.integral_prod_left.integral_prod_right.swap.prod_right_ae

theorem finite_kernel_fubini (a : ℝ) (f : I→B→S×((J×X)×W)→ℝ)
    (hf : ∀i b,Integrable (f i b) (ν.prod ((μJ.prod μX).prod μW))) :
    (∫x,∑i : I,∫j,a*∑b : B,∫s,∫w,f i b (s,((j,x),w)) ∂μW ∂ν ∂μJ ∂μX)=
      a*∑b : B,∫q,∑i : I,f i b q ∂ν.prod ((μJ.prod μX).prod μW) := by
  let g := fun i b x => ∫j,∫s,∫w,f i b (s,((j,x),w)) ∂μW ∂ν ∂μJ
  have hX (i : I) (b : B) : Integrable (g i b) μX :=
    (ActualResponseCoefficientIntegral.integral_time_disorder_initial_brownian (hf i b)).1
  have hEq (i : I) (b : B) : (∫x,g i b x ∂μX)=
      ∫q,f i b q ∂ν.prod ((μJ.prod μX).prod μW) :=
    (ActualResponseCoefficientIntegral.integral_time_disorder_initial_brownian (hf i b)).2.symm
  have hJ := ae_all_iff.mpr (fun i : I => ae_all_iff.mpr (fun b : B =>
    conditional_disorder_integrable_ae (hf i b)))
  have he : (∫x,∑i : I,∫j,a*∑b : B,∫s,∫w,f i b (s,((j,x),w)) ∂μW ∂ν ∂μJ ∂μX)=
      ∫x,∑i : I,a*∑b : B,g i b x ∂μX := by
    apply integral_congr_ae
    filter_upwards [hJ] with x hx
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul,integral_finsetSum Finset.univ (fun b _ => hx i b)]
  rw [he,integral_finsetSum Finset.univ (fun i _ =>
    (integrable_finsetSum Finset.univ (fun b _ => hX i b)).const_mul a)]
  have hi (i : I) : (∫x,a*∑b : B,g i b x ∂μX)=
      a*∑b : B,∫q,f i b q ∂ν.prod ((μJ.prod μX).prod μW) := by
    rw [integral_const_mul,integral_finsetSum Finset.univ (fun b _ => hX i b)]
    simp_rw [hEq]
  simp_rw [hi]
  rw [←Finset.mul_sum,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  exact (integral_finsetSum Finset.univ (fun i _ => hf i b)).symm

end SphericalAging.FiniteKernelFubini
