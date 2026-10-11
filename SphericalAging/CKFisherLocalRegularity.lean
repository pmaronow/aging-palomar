module

public import SphericalAging.CKFisherRows
public import SphericalAging.FisherLimitLocalBounds

public section

/-! All local analytic clauses of source 5.3, obtained from the constructed
Fisher clock, true CK rows, and the preceding energy current increment bound. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace SphericalAging.CKFisherLocalRegularity
open Set Filter MeasureTheory CKSpecification StrongBackwardDefect EarlierCovariance
open CKUniformLateEstimates FisherIncrementRegularity CKFisherRows FisherLimitLocalBounds
open scoped Topology

structure LocalConclusions (p : ℕ) (β : ℝ) (d : CKData) (a : ℝ→ℝ) (K A : ℝ) : Prop where
  locally_bounded : ∀T : ℝ,0≤T → ∃M : ℝ,0≤M ∧ ∀s∈Icc 0 T,|a s|≤M
  right_continuous : ∀s,ContinuousWithinAt a (Ici s) s
  moving_clock : ∀ε t : ℝ,0<ε → ε≤t → a t≤windowFactor K ε*(∫u in (t-ε)..t,a u)
  row_absolute_continuity : ∀t : ℝ,0≤t → AbsolutelyContinuousOnInterval (fun s => d.C t s) 0 t
  row_integral_bound : ∀u v t : ℝ,0≤u → u≤v → v≤t →
    |d.C t v-d.C t u-(∫s in u..v,d.R t s)|≤∫s in u..v,Real.sqrt (a s)
  backward_derivative_bound : ∀t s : ℝ,0<s → s<t → |backwardDefect p β d t s|≤Real.sqrt (a s)
  energy_absolute_continuity : ∀T : ℝ,0≤T → AbsolutelyContinuousOnInterval (energy p β d) 0 T
  energy_derivative_bound : ∀ᵐ s ∂volume.restrict (Ioi 0),
    DifferentiableAt ℝ (energy p β d) s ∧ (deriv (energy p β d) s)^2≤(p:ℝ)^2*A^2*a s

theorem source5_3 {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    {a : ℝ→ℝ} (ha : FisherMajorant p β d a) (han : ∀s,0≤a s)
    (hac : ∀s,ContinuousWithinAt a (Ici s) s) {K A : ℝ} (hK : 0≤K) (hA : 0≤A)
    (hclock : Antitone (fun s => Real.exp (-K*s)*a s))
    (he : IncrementControl a (energy p β d) ((p:ℝ)*A)) :
    LocalConclusions p β d a K A := by
  have hlocal := locally_bounded_on_ray hK han (hclock.antitoneOn (Ici 0))
  have ham := SphereCKFisherMajorant.stronglyMeasurable_of_exponential_clock hclock
  have hlocal' : ∀T : ℝ,0≤T → ∃M : ℝ,0≤M ∧ ∀s∈Icc 0 T,a s≤M := by
    intro T hT
    obtain ⟨M,hM,hb⟩ := hlocal T hT
    exact ⟨M,hM,fun s hs => (le_abs_self _).trans (hb s hs)⟩
  have henergy := ae_derivative_bound_of_increment_control he ha.integrable
    (mul_nonneg (Nat.cast_nonneg p) hA) hlocal' ham hac
  refine ⟨hlocal,hac,fun _ _ hε hεt => moving_window_bound hK hε hεt ha.integrable
    (hclock.antitoneOn (Ici 0)),fun _ ht => row_absolutelyContinuous h ht,
    fun _ _ _ hu huv hvt => row_integral_sqrt_bound h ha han ham hu huv hvt,?_,henergy.1,?_⟩
  · intro t s hs hst
    exact (Real.le_sqrt (abs_nonneg _) (han s)).mpr (by
      simpa only [sq_abs] using ha.dominates t s hs hst)
  · simpa only [mul_pow,mul_assoc] using henergy.2

end SphericalAging.CKFisherLocalRegularity
