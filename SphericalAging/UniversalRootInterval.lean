module

public import SphericalAging.LpTensorSurjectivity
public import SphericalAging.HilbertSchmidtTensor
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

public section

/-! The concrete interval Hilbert space used by the universal threshold root. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
namespace SphericalAging.UniversalRootInterval
open CausalTree CausalTree.HilbertDatum

@[expose] def unitMeasure : Measure ℝ := volume.restrict (Ioc 0 1)
instance : IsFiniteMeasure unitMeasure := by
  unfold unitMeasure
  infer_instance

@[expose] abbrev IntervalL2 := Lp ℝ 2 unitMeasure
@[expose] abbrev KernelL2 := Lp ℝ 2 (unitMeasure.prod unitMeasure)

@[expose, reducible] def intervalDatum : HilbertDatum := ⟨IntervalL2, inferInstance, inferInstance, inferInstance⟩

@[expose] def one : IntervalL2 := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top _ _) (1 : ℝ)

theorem one_coe : (one : ℝ → ℝ) =ᵐ[unitMeasure] (fun _ => 1) := by
  simpa [one] using (indicatorConstLp_coeFn (p := 2) (μ := unitMeasure)
    (hs := MeasurableSet.univ) (hμs := measure_ne_top _ _) (c := (1 : ℝ)))

theorem unitMeasure_real_univ : unitMeasure.real univ = 1 := by
  simp [unitMeasure, measureReal_def, Measure.restrict_apply MeasurableSet.univ]

theorem one_norm : ‖one‖ = 1 := by
  have hh : inner ℝ one one = 1 := by
    rw [L2.inner_def]
    calc
      _ = ∫ _ : ℝ, (1 : ℝ) ∂unitMeasure := by
        apply integral_congr_ae
        filter_upwards [one_coe] with x hx
        simp [hx]
      _ = 1 := by simp [unitMeasure_real_univ]
  rw [real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg one]

@[expose] def kernelEquiv : (tensor intervalDatum intervalDatum).Carrier ≃ₗᵢ[ℝ] KernelL2 :=
  LpTensorSurjectivity.completedEquiv

@[expose] def tensorOfKernel (k : KernelL2) : HilbertSchmidtTensor.HilbertSchmidt intervalDatum intervalDatum :=
  kernelEquiv.symm k

@[expose] def operatorOfKernel (k : KernelL2) : IntervalL2 →L[ℝ] IntervalL2 :=
  HilbertSchmidtTensor.operator intervalDatum intervalDatum (tensorOfKernel k)

theorem tensorOfKernel_norm (k : KernelL2) : ‖tensorOfKernel k‖ = ‖k‖ :=
  kernelEquiv.symm.norm_map k

theorem operatorOfKernel_injective : Function.Injective operatorOfKernel := by
  intro k l h
  apply kernelEquiv.symm.injective
  exact HilbertSchmidtTensor.operator_injective _ _ h

theorem operatorOfKernel_pairing (k : KernelL2) (f g : IntervalL2) :
    inner ℝ f (operatorOfKernel k g) = inner ℝ (LpProductTensor.product f g) k := by
  change inner ℝ f (HilbertSchmidtTensor.operator intervalDatum intervalDatum (tensorOfKernel k) g) = _
  rw [HilbertSchmidtTensor.operator_pairing intervalDatum intervalDatum (tensorOfKernel k) f g]
  have hp : kernelEquiv (pure intervalDatum intervalDatum f g) =
      LpProductTensor.product f g := LpProductTensor.completedIsometry_tmul f g
  rw [← hp, ← kernelEquiv.inner_map_map]
  simp [tensorOfKernel]

end SphericalAging.UniversalRootInterval
