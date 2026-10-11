module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Integral.Prod

public section

/-! Literal function representatives of Bochner integrals in L², proved
by bounded-set testing and genuine Fubini. -/
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace
namespace SphericalAging.L2BochnerKernelIntegral
set_option maxHeartbeats 400000

/-- A genuinely integrable joint kernel represents the Bochner L² integral
whenever its slices represent the L² curve. No integral equality is assumed. -/
theorem integral_coe_ae {A Y : Type*} [MeasurableSpace A] [MeasurableSpace Y]
    {μ : Measure A} {η : Measure Y} [SFinite μ] [SigmaFinite η]
    {F : A→Lp ℝ 2 η} {k : A×Y→ℝ}
    (hF : Integrable F μ) (hk : Integrable k (μ.prod η))
    (hrep : ∀ᵐa ∂μ,(F a : Y→ℝ)=ᵐ[η](fun y=>k (a,y))) :
    (∫a,F a ∂μ : Lp ℝ 2 η)=ᵐ[η](fun y=>∫a,k (a,y) ∂μ) := by
  have hright : Integrable (fun y=>∫a,k (a,y) ∂μ) η := hk.integral_prod_right
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s _ hμs=>integrableOn_Lp_of_measure_ne_top _ (by norm_num) hμs.ne)
    (fun _ _ _=>hright.integrableOn)
  intro s hs hμs
  let e : Lp ℝ 2 η := indicatorConstLp 2 hs hμs.ne (1:ℝ)
  have he (f : Lp ℝ 2 η) : inner ℝ e f=∫y in s,f y ∂η :=
    L2.inner_indicatorConstLp_one hs hμs.ne f
  have hi : Integrable k (μ.prod (η.restrict s)) :=
    hk.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  calc
    _ = inner ℝ e (∫a,F a ∂μ) := (he _).symm
    _ = ∫a,inner ℝ e (F a) ∂μ := by rw [←integral_inner hF]
    _ = ∫a,∫y in s,k (a,y) ∂η ∂μ := by
      apply integral_congr_ae
      filter_upwards [hrep] with a ha
      rw [he]
      exact integral_congr_ae (ae_restrict_of_ae ha)
    _ = _ := integral_integral_swap hi

end SphericalAging.L2BochnerKernelIntegral
