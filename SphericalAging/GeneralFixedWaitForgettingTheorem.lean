module

public import SphericalAging.ActualForkForgettingSequence
public import SphericalAging.GeneralForgettingRealRay
public import SphericalAging.GeneralThresholdInputTheorem

public section

/-! Complete local proof of Proposition 10.8 and its source8.1 consequences.
The inputs are precisely preceding physical finite-fork10.4, finite-dimensional
actual overlap3.3, and the admissible-algorithm waiting-state orthogonality
estimate. Actual fork algorithms and errors, energy saturation, deficit convergence
and the real-ray CK forgetting conclusion are proved, not assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace SphericalAging.GeneralFixedWaitForgettingTheorem
open MeasureTheory ProbabilityTheory Filter Set FiniteModel CKSpecification
  ProfileCenterEnergy ForkParameterBounds PhysicalForkWaitingTransfer
  ActualForkForgettingSequence
open scoped NNReal Topology

theorem fixed_wait_NNReal {p : ℕ} {β ell e q : ℝ} {c r : ℝ→ℝ}
    (hp : 3≤p) (hβ : 0<β) {d : CKData} (h : CKEquations p β d)
    (H : Profile c r q) (hq : 0<q) (hq1 : q<1)
    (hell : ell=PlateauAlgebra.multiplier p β q) (he : e=(ell-1)/((p:ℝ)*β))
    (hr : ∀u,0<u→0≤r u) (hm : β^2*PlateauAlgebra.marginalityPolynomial p q=1)
    {dim : ℕ→ℕ} (hDim : ∀n,1≤dim n) (F : PhysicalForkStanding.Forks dim p β e c r)
    (s : ℝ≥0)
    (hBridge : ∀u : ℝ≥0,s≤u→Tendsto (fun n => expectedOverlap (dim n) p β u s) atTop
      (𝓝 (d.C u s)))
    (hWaiting : WaitingAlgorithmOrthogonality.Input dim p β s) :
    Tendsto (fun t : ℝ => d.C t s) atTop (𝓝 0) := by
  have hf : Tendsto (fun t : ℝ => d.C (max t s) s) atTop (𝓝 0) := by
    apply GeneralForgettingRealRay.real_ray_forgetting_of_sequences
    · intro t
      exact ((CKPhysicalConsequences.physical_bounds_of_equations h).1 _ _
        (s.coe_nonneg.trans (le_max_right _ _)) s.coe_nonneg).1
    · intro t htpos ht
      have hmax : Tendsto (fun n => max (t n) s) atTop atTop :=
        tendsto_atTop_mono (fun n => le_max_left _ _) ht
      exact source10_10_sequence hp hβ h H hq hq1 hell he hr hm hDim F s
        (fun n => max (t n) s) hmax hBridge hWaiting
  apply hf.congr'
  filter_upwards [eventually_ge_atTop (s:ℝ)] with t ht
  rw [max_eq_left ht]

theorem source10_10 {p : ℕ} {β ell e q : ℝ} {c r : ℝ→ℝ}
    (hp : 3≤p) (hβ : 0<β) {d : CKData} (h : CKEquations p β d)
    (H : Profile c r q) (hq : 0<q) (hq1 : q<1)
    (hell : ell=PlateauAlgebra.multiplier p β q) (he : e=(ell-1)/((p:ℝ)*β))
    (hr : ∀u,0<u→0≤r u) (hm : β^2*PlateauAlgebra.marginalityPolynomial p q=1)
    {dim : ℕ→ℕ} (hDim : ∀n,1≤dim n) (F : PhysicalForkStanding.Forks dim p β e c r)
    (hBridge : ∀s u : ℝ≥0,s≤u→Tendsto (fun n => expectedOverlap (dim n) p β u s) atTop
      (𝓝 (d.C u s)))
    (hWaiting : ∀s : ℝ≥0,WaitingAlgorithmOrthogonality.Input dim p β s) :
    ∀s : ℝ,0≤s→Tendsto (fun t : ℝ => d.C t s) atTop (𝓝 0) := by
  intro s hs
  exact fixed_wait_NNReal hp hβ h H hq hq1 hell he hr hm hDim F ⟨s,hs⟩
    (hBridge ⟨s,hs⟩) (hWaiting ⟨s,hs⟩)

theorem source8_1_from_actual_forks {p : ℕ} {β ell e q : ℝ} {c r : ℝ→ℝ}
    (hp : 3≤p) (hβ : 0<β) {d : CKData} (h : CKEquations p β d)
    (H : Profile c r q) (hq : 0<q) (hq1 : q<1)
    (hell : ell=PlateauAlgebra.multiplier p β q) (he : e=(ell-1)/((p:ℝ)*β))
    (hr : ∀u,0<u→0≤r u) (hm : β^2*PlateauAlgebra.marginalityPolynomial p q=1)
    {dim : ℕ→ℕ} (hDim : ∀n,1≤dim n) (F : PhysicalForkStanding.Forks dim p β e c r)
    (hBridge : ∀s u : ℝ≥0,s≤u→Tendsto (fun n => expectedOverlap (dim n) p β u s) atTop
      (𝓝 (d.C u s)))
    (hWaiting : ∀s : ℝ≥0,WaitingAlgorithmOrthogonality.Input dim p β s) :
    (∀L : ℝ,0≤L→prefixEnergy p β e c r L≤ExternalFieldElementaryPenalty.thresholdEnergy p*
      (c (2*L))^((p:ℝ)/2)) ∧
    (∀S : ℝ,0≤S→Tendsto (GeneralThresholdInputTheorem.waitingSup d S) atTop (𝓝 0)) := by
  apply GeneralThresholdInputTheorem.source8_1_from_finite_forks_and_fixed_wait h H hq hr
  · intro K hK L hL
    exact F.ceiling K hK ⟨L,hL⟩
  · exact source10_10 hp hβ h H hq hq1 hell he hr hm hDim F hBridge hWaiting

end SphericalAging.GeneralFixedWaitForgettingTheorem
