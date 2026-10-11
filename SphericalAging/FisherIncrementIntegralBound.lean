module

public import SphericalAging.CKFisherRows
public import SphericalAging.FisherLimitLocalBounds

public section

/-! The exact integral of the square root of the constructed Fisher clock
controls increments. The bound follows from genuine local absolute
continuity and the almost-everywhere derivative estimate. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace SphericalAging.FisherIncrementIntegralBound
open Set Filter MeasureTheory CKUniformLateEstimates FisherIncrementRegularity
open CKFisherRows FisherLimitLocalBounds
open scoped Topology

theorem increment_integral_sqrt_bound {a f : ℝ→ℝ} {B : ℝ}
    (hc : IncrementControl a f B) (hi : IntegrableOn a (Ioi 0))
    (han : ∀s,0≤a s) (hB : 0≤B)
    (hb : ∀T : ℝ,0≤T → ∃M : ℝ,0≤M ∧ ∀s∈Icc 0 T,a s≤M)
    (ham : StronglyMeasurable a) (hac : ∀s,ContinuousWithinAt a (Ici s) s)
    {u v : ℝ} (hu : 0≤u) (huv : u≤v) :
    |f v-f u|≤B*(∫s in u..v,Real.sqrt (a s)) := by
  have hreg := ae_derivative_bound_of_increment_control hc hi hB hb ham hac
  have hAC : AbsolutelyContinuousOnInterval f u v := by
    apply (hreg.1 v (hu.trans huv)).mono
    rw [uIcc_of_le huv,uIcc_of_le (hu.trans huv)]
    exact fun s hs => ⟨hu.trans hs.1,hs.2⟩
  have hAE : ∀ᵐ s ∂volume,s∈Ioi 0 → (deriv f s)^2≤B^2*a s := by
    rw [← ae_restrict_iff' measurableSet_Ioi]
    exact hreg.2.mono fun s hs => hs.2
  have hI := (sqrt_intervalIntegrable han hi ham hu huv).const_mul B
  have hh := intervalIntegral.norm_integral_le_of_norm_le huv (f:=deriv f) (g:=fun s => B*Real.sqrt (a s))
    (by
      filter_upwards [hAE] with s hs hsu
      have hd := hs (hu.trans_lt hsu.1)
      have hsq : (B*Real.sqrt (a s))^2=B^2*a s := by
        rw [mul_pow,Real.sq_sqrt (han s)]
      rw [Real.norm_eq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hB (Real.sqrt_nonneg _))).mp
        (by rw [sq_abs,hsq];exact hd)) hI
  rw [hAC.integral_deriv_eq_sub,intervalIntegral.integral_const_mul,Real.norm_eq_abs] at hh
  exact hh

theorem waiting_integral_sqrt_bound {d : CKSpecification.CKData} {a : ℝ→ℝ}
    {B : ℝ→ℝ} (hw : WaitingControl d a B) (hi : IntegrableOn a (Ioi 0))
    (han : ∀s,0≤a s) (hB : ∀L,0≤L → 0≤B L)
    (hb : ∀T : ℝ,0≤T → ∃M : ℝ,0≤M ∧ ∀s∈Icc 0 T,a s≤M)
    (ham : StronglyMeasurable a) (hac : ∀s,ContinuousWithinAt a (Ici s) s)
    {L τ u v : ℝ} (hL : 0≤L) (hτ : 0≤τ) (hτL : τ≤L) (hu : 0≤u) (huv : u≤v) :
    |d.C (v+τ) v-d.C (u+τ) u|≤B L*(∫s in u..v,Real.sqrt (a s)) :=
  increment_integral_sqrt_bound (hw L hL τ hτ hτL) hi han (hB L hL) hb ham hac hu huv

end SphericalAging.FisherIncrementIntegralBound
