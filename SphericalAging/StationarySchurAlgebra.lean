module

public import SphericalAging.DirichletKernel
public import SphericalAging.StationaryCutoffBalance
public import Mathlib.MeasureTheory.Integral.Prod

public section

/-! Genuine symmetric-kernel square identity with all integrability proved. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationarySchurAlgebra
noncomputable section

/-- The weighted Schur square identity is derived from genuine product
integrals. Cross integrability follows from the square majorant; no
Cauchy--Schwarz identity or energy identity is a premise. -/
theorem symmetric_kernel_square_identity (μ : Measure ℝ) [SFinite μ]
    (K : ℝ×ℝ → ℝ) (f : ℝ → ℝ)
    (hK : AEStronglyMeasurable K (μ.prod μ)) (hf : AEStronglyMeasurable f μ)
    (hn : ∀ᵐ z ∂μ.prod μ,0≤K z) (hs : ∀ x y : ℝ,K (x,y)=K (y,x))
    (hd : Integrable (fun z : ℝ×ℝ => K z*f z.1^2) (μ.prod μ)) :
    Integrable (fun z : ℝ×ℝ => K z*f z.1*f z.2) (μ.prod μ) ∧
      Integrable (fun z : ℝ×ℝ => K z*(f z.1-f z.2)^2) (μ.prod μ) ∧
      (∫ z : ℝ×ℝ,K z*(f z.1-f z.2)^2 ∂μ.prod μ)/2=
        (∫ z : ℝ×ℝ,K z*f z.1^2 ∂μ.prod μ)-(∫ z : ℝ×ℝ,K z*f z.1*f z.2 ∂μ.prod μ) := by
  have hd2 : Integrable (fun z : ℝ×ℝ => K z*f z.2^2) (μ.prod μ) := by
    apply hd.swap.congr
    exact Eventually.of_forall (fun z => by change K (z.2,z.1)*f z.2^2=K z*f z.2^2; rw [← hs z.1 z.2])
  have hcross : Integrable (fun z : ℝ×ℝ => K z*f z.1*f z.2) (μ.prod μ) := by
    apply (hd.add hd2).mono' ((hK.mul hf.comp_fst).mul hf.comp_snd)
    filter_upwards [hn] with z hz
    have habs : |f z.1*f z.2|≤f z.1^2+f z.2^2 := by
      rw [abs_le]
      constructor <;> nlinarith only [sq_nonneg (f z.1-f z.2),sq_nonneg (f z.1+f z.2),sq_nonneg (f z.1),sq_nonneg (f z.2)]
    have hm := mul_le_mul_of_nonneg_left habs hz
    change ‖K z*f z.1*f z.2‖≤K z*f z.1^2+K z*f z.2^2
    rw [Real.norm_eq_abs,show K z*f z.1*f z.2=K z*(f z.1*f z.2) by ring,abs_mul,abs_of_nonneg hz]
    nlinarith only [hm]
  have hexp (z : ℝ×ℝ) : K z*(f z.1-f z.2)^2=K z*f z.1^2+K z*f z.2^2-2*(K z*f z.1*f z.2) := by ring
  have henergy : Integrable (fun z : ℝ×ℝ => K z*(f z.1-f z.2)^2) (μ.prod μ) := by
    apply ((hd.add hd2).sub (hcross.const_mul 2)).congr
    exact Eventually.of_forall (fun z => (hexp z).symm)
  have hswap : (∫ z : ℝ×ℝ,K z*f z.2^2 ∂μ.prod μ)=(∫ z : ℝ×ℝ,K z*f z.1^2 ∂μ.prod μ) := by
    calc
      _ = ∫ z : ℝ×ℝ,K z.swap*f z.2^2 ∂μ.prod μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => by change K (z.1,z.2)*f z.2^2=K (z.2,z.1)*f z.2^2; rw [hs z.1 z.2])
      _ = ∫ z : ℝ×ℝ,(fun w : ℝ×ℝ => K w*f w.1^2) z.swap ∂μ.prod μ := rfl
      _ = _ := integral_prod_swap (μ:=μ) (ν:=μ) (fun w : ℝ×ℝ => K w*f w.1^2)
  refine ⟨hcross,henergy,?_⟩
  simp_rw [hexp]
  have hl := integral_sub (hd.add hd2) (hcross.const_mul 2)
  change (∫ z : ℝ×ℝ,K z*f z.1^2+K z*f z.2^2-2*(K z*f z.1*f z.2) ∂μ.prod μ)=
    (∫ z : ℝ×ℝ,K z*f z.1^2+K z*f z.2^2 ∂μ.prod μ)-(∫ z : ℝ×ℝ,2*(K z*f z.1*f z.2) ∂μ.prod μ) at hl
  rw [hl,integral_add hd hd2,integral_const_mul,hswap]
  ring

end
end SphericalAging.StationarySchurAlgebra
