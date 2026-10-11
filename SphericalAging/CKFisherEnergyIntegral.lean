module

public import SphericalAging.CKFisherLocalRegularity
public import SphericalAging.FisherIncrementIntegralBound

public section

/-! The exact energy increment bound by the integral of the square root
of the actual Fisher majorant, completing the local energy clauses of
source 5.3 from its genuine current-derived squared increment estimate. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace SphericalAging.CKFisherEnergyIntegral
open Set Filter MeasureTheory CKSpecification StrongBackwardDefect
open CKUniformLateEstimates FisherLimitLocalBounds FisherIncrementIntegralBound
open scoped Topology

theorem energy_integral_sqrt_bound {p : ℕ} {β : ℝ} {d : CKData}
    {a : ℝ→ℝ} (ha : FisherMajorant p β d a) (han : ∀s,0≤a s)
    (hac : ∀s,ContinuousWithinAt a (Ici s) s) {K A : ℝ} (hK : 0≤K) (hA : 0≤A)
    (hclock : Antitone (fun s => Real.exp (-K*s)*a s))
    (he : IncrementControl a (energy p β d) ((p:ℝ)*A))
    {u v : ℝ} (hu : 0≤u) (huv : u≤v) :
    |energy p β d v-energy p β d u|≤(p:ℝ)*A*(∫s in u..v,Real.sqrt (a s)) := by
  have hlocal := locally_bounded_on_ray hK han (hclock.antitoneOn (Ici 0))
  have hb : ∀T : ℝ,0≤T → ∃M : ℝ,0≤M ∧ ∀s∈Icc 0 T,a s≤M := by
    intro T hT
    obtain ⟨M,hM,hh⟩ := hlocal T hT
    exact ⟨M,hM,fun s hs => (le_abs_self _).trans (hh s hs)⟩
  exact increment_integral_sqrt_bound he ha.integrable han (mul_nonneg (Nat.cast_nonneg p) hA)
    hb (SphereCKFisherMajorant.stronglyMeasurable_of_exponential_clock hclock) hac hu huv

theorem source5_3 {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    {a : ℝ→ℝ} (ha : FisherMajorant p β d a) (han : ∀s,0≤a s)
    (hac : ∀s,ContinuousWithinAt a (Ici s) s) {K A : ℝ} (hK : 0≤K) (hA : 0≤A)
    (hclock : Antitone (fun s => Real.exp (-K*s)*a s))
    (he : IncrementControl a (energy p β d) ((p:ℝ)*A)) :
    CKFisherLocalRegularity.LocalConclusions p β d a K A ∧
      ∀u v : ℝ,0≤u → u≤v →
        |energy p β d v-energy p β d u|≤(p:ℝ)*A*(∫s in u..v,Real.sqrt (a s)) :=
  ⟨CKFisherLocalRegularity.source5_3 h ha han hac hK hA hclock he,
    fun _ _ hu huv => energy_integral_sqrt_bound ha han hac hK hA hclock he hu huv⟩

end SphericalAging.CKFisherEnergyIntegral
