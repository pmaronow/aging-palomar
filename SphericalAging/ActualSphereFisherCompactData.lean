module

public import SphericalAging.ActualSphereGoodFisherClock
public import SphericalAging.SphereFisherCompactData
public import SphericalAging.ActualSphereBadFisherLimit

public section

/-! All functional Fisher compactness inputs constructed from the actual
uniform-initial spherical diffusion. The resulting Helly theorem concerns
the literal full annealed Fisher information. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.ActualSphereFisherCompactData
open MeasureTheory Set Filter FiniteModel SphereRotationGeometry SphereGoodEventFisherClock
open ActualSphereFisherClock ActualSphereGoodFisherClock ActualSphereGibbsDensity
open SphereAnnealedFisherBudget SphereTruncatedFisherBudget SphereBadEventFisherMass
open ActualSphereAnnealedFisherBudget ActualSphereRestrictedFisherBudget ActualSphereBadFisherLimit
open SphereFisherCompactData
open scoped NNReal Topology
variable {N p : ℕ}

@[expose] def actualFisherCompactData (hN : 2≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) : FisherCompactData N p β where
  full := full β R hR
  good := good β R hR
  bad := bad β R hR
  clock := fun t => Real.exp (-ceilingRate p β (cutoff p)*max t 0)*good (N:=N) (p:=p) β R hR (max t 0)
  full_nonneg := by
    intro t
    unfold full annealedFisher
    exact div_nonneg (integral_nonneg (fun J => actual_fisher_nonneg (by omega) (by omega) β R hR hNR J t))
      (Nat.cast_nonneg N)
  good_nonneg := actual_restricted_fisher_nonneg (by omega) (by omega) β R hR hNR _
  bad_nonneg := actual_restricted_fisher_nonneg (by omega) (by omega) β R hR hNR _
  full_eq_good_add_bad := fun {t} ht => actual_full_eq_good_add_bad_of_integrable β R hR t
    (actual_forwardDensity_fisher_disorder_integrable (by omega) hp β R hR hNR ht)
  full_integrable := (actual_annealed_fisher_time_budget (by omega) (by omega) β R hR hNR).1
  good_integrable := (actual_good_time_budget (by omega) (by omega) β R hR hNR).1
  good_mass := (actual_good_time_budget (by omega) (by omega) β R hR hNR).2
  bad_integrable := (actual_bad_fisher_mass_bound hN (by omega) β R hR hNR).1
  bad_mass := (actual_bad_fisher_mass_bound hN (by omega) β R hR hNR).2.2
  clock_antitone := by
    intro s t hst
    exact actual_goodFisher_clock_antitoneOn (by omega) hp β R hR hNR (cutoff p)
      (show max s 0 ∈ Ici 0 from le_max_right s 0)
      (show max t 0 ∈ Ici 0 from le_max_right t 0) (max_le_max hst le_rfl)
  clock_bounds := fun t => actual_goodFisher_clock_uniform_bound (by omega) hp β R hR hNR (cutoff p)
    (le_max_right t 0)
  good_eq_exp_clock := by
    intro t ht
    rw [max_eq_left ht,←mul_assoc,←Real.exp_add]
    simp

/-- Full-model Fisher subsequence for any diverging dimensions and actual
cutoff radii. No density, equation, clock, budget or extraction premise. -/
theorem actual_Fisher_subsequence (p : ℕ) (hp : 2≤p) (β : ℝ≥0)
    (dim : ℕ→ℕ) (hN : ∀n,2≤dim n) (hdim : Tendsto dim atTop atTop)
    (R : ℕ→ℝ≥0) (hR : ∀n,0<(R n:ℝ)) (hNR : ∀n,(dim n:ℝ)<(R n:ℝ)^2) :
    ∃ (φ : ℕ→ℕ) (aF : ℝ→ℝ),StrictMono φ ∧
      (∀t,0≤aF t) ∧ (∀t,aF t≤Real.exp (ceilingRate p β (cutoff p)*t)*((β:ℝ)^2*(p:ℝ))) ∧
      (∀t,ContinuousWithinAt aF (Ici t) t) ∧
      Antitone (fun t => Real.exp (-ceilingRate p β (cutoff p)*t)*aF t) ∧
      IntegrableOn aF (Ioi 0) ∧ (∫t in Ioi 0,aF t)≤(β:ℝ)^2/2 ∧
      (∀T : ℝ,Tendsto (fun n => ∫t in Ioc 0 T,
        |full (N:=dim (φ n)) (p:=p) β (R (φ n)) (hR (φ n)) t-aF t|) atTop (𝓝 0)) :=
  compact_Fisher_subsequence hp β.coe_nonneg dim hdim
    (fun n => actualFisherCompactData (hN n) hp β (R n) (hR n) (hNR n))

end SphericalAging.ActualSphereFisherCompactData
