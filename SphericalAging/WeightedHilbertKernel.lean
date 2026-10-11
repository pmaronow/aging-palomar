module

public import SphericalAging.ScalarHilbertKernel
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

public section

/-! Positive semidefiniteness of actual weighted covariance double integrals.
The weights and power kernels are realized by genuine Bochner-integrable
Hilbert vectors. -/

noncomputable section
open scoped InnerProductSpace
open MeasureTheory

namespace SphericalAging.WeightedHilbertKernel
open ScalarHilbertKernel

@[expose] abbrev PowerSpace (K : PositiveKernel ℝ) (n : ℕ) :=
  (CausalTree.HilbertDatum.finiteTensor n (fun _ => datum K)).Carrier

@[expose] def weightedFeature (K : PositiveKernel ℝ) (n : ℕ) (r : ℝ → ℝ → ℝ) (t : ℝ) :
    PowerSpace K n := ∫ u in (0 : ℝ)..t, r t u • powerFeature K n u

theorem weightedFeature_integrable (K : PositiveKernel ℝ)
    (hK : Continuous (Function.uncurry K.value)) (n : ℕ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t a b : ℝ) :
    IntervalIntegrable (fun u => r t u • powerFeature K n u) volume a b :=
  ((hr.comp (continuous_const.prodMk continuous_id)).smul
    (powerFeature_continuous K hK n)).intervalIntegrable a b

theorem inner_intervalIntegral {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (c : E) {f : ℝ → E} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    inner ℝ c (∫ u in a..b, f u) = ∫ u in a..b, inner ℝ c (f u) :=
  ((innerSL ℝ c).intervalIntegral_comp_comm hf).symm

theorem intervalIntegral_inner {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (c : E) {f : ℝ → E} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    inner ℝ (∫ u in a..b, f u) c = ∫ u in a..b, inner ℝ (f u) c := by
  rw [real_inner_comm, inner_intervalIntegral c hf]
  apply intervalIntegral.integral_congr
  intro u _
  exact real_inner_comm _ _

theorem weightedFeature_inner (K : PositiveKernel ℝ)
    (hK : Continuous (Function.uncurry K.value)) (n : ℕ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t s : ℝ) :
    inner ℝ (weightedFeature K n r t) (weightedFeature K n r s) =
      ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s,
        r t u*r s v*K.value u v ^ n := by
  rw [weightedFeature, intervalIntegral_inner _ (weightedFeature_integrable K hK n r hr t 0 t)]
  apply intervalIntegral.integral_congr
  intro u _
  change inner ℝ (r t u • powerFeature K n u) (weightedFeature K n r s) =
    ∫ v in (0 : ℝ)..s, r t u*r s v*K.value u v ^ n
  rw [weightedFeature, inner_intervalIntegral _ (weightedFeature_integrable K hK n r hr s 0 s)]
  apply intervalIntegral.integral_congr
  intro v _
  change inner ℝ (r t u • powerFeature K n u) (r s v • powerFeature K n v) =
    r t u*r s v*K.value u v ^ n
  rw [real_inner_smul_left, real_inner_smul_right, powerFeature_inner]
  ring

/-- The actual covariance double integral is a Gram kernel, including all
finite-dimensional positivity inequalities. -/
@[expose] def weightedKernel (K : PositiveKernel ℝ) (n : ℕ) (r : ℝ → ℝ → ℝ) : PositiveKernel ℝ :=
  gramKernel (weightedFeature K n r)

@[simp] theorem weightedKernel_value (K : PositiveKernel ℝ)
    (hK : Continuous (Function.uncurry K.value)) (n : ℕ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t s : ℝ) :
    (weightedKernel K n r).value t s =
      ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s,
        r t u*r s v*K.value u v ^ n :=
  weightedFeature_inner K hK n r hr t s

theorem weightedFeature_norm_sq (K : PositiveKernel ℝ)
    (hK : Continuous (Function.uncurry K.value)) (n : ℕ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t : ℝ) :
    ‖weightedFeature K n r t‖ ^ 2 =
      ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..t,
        r t u*r t v*K.value u v ^ n := by
  rw [← real_inner_self_eq_norm_sq, weightedFeature_inner K hK n r hr]

theorem powerFeature_inner_weightedFeature (K : PositiveKernel ℝ)
    (hK : Continuous (Function.uncurry K.value)) (n : ℕ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t : ℝ) :
    inner ℝ (powerFeature K n t) (weightedFeature K n r t) =
      ∫ u in (0 : ℝ)..t, r t u*K.value t u ^ n := by
  rw [weightedFeature, inner_intervalIntegral _ (weightedFeature_integrable K hK n r hr t 0 t)]
  apply intervalIntegral.integral_congr
  intro u _
  change inner ℝ (powerFeature K n t) (r t u • powerFeature K n u) =
    r t u*K.value t u ^ n
  rw [real_inner_smul_right, powerFeature_inner]

theorem weighted_mass_square_le (K : PositiveKernel ℝ)
    (hK : Continuous (Function.uncurry K.value)) (n : ℕ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t : ℝ) (hunit : K.value t t = 1) :
    (∫ u in (0 : ℝ)..t, r t u*K.value t u ^ n) ^ 2 ≤
      ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..t,
        r t u*r t v*K.value u v ^ n := by
  have hh := real_inner_mul_inner_self_le (powerFeature K n t) (weightedFeature K n r t)
  rw [powerFeature_inner, hunit, one_pow, one_mul,
    real_inner_self_eq_norm_sq, weightedFeature_norm_sq K hK n r hr,
    powerFeature_inner_weightedFeature K hK n r hr] at hh
  simpa only [pow_two] using hh

end SphericalAging.WeightedHilbertKernel
