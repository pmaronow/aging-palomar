module

public import SphericalAging.SphereEulerStrongApproximation

public section

/-! Genuine raw one-step frozen-coefficient Euler error for the actual
sphere process. At fixed dimension and landscape it is O(h²), uniformly
in the physical initial state. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ActualSphereOneStepEulerError
open FiniteModel HardSphereDynamics ActualSphereTransition
open SphereEulerPredictable SphereEulerInterpolationAlgebra SphereEulerPhysicalComparison
open SphereEulerPhysicalError SphereEulerLocalMoment HamiltonianPicardDependence GlobalHamiltonianParameter
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def oneStepCeiling (β : ℝ≥0) (J : Disorder N p) (S : ℝ≥0) : ℝ :=
  (2*(S : ℝ)*(driftCap β J : ℝ)^2+4*(N : ℝ))*
    (4*(S : ℝ)*(driftRate β J : ℝ)^2+32/(N : ℝ))*
      Real.exp ((4*(S : ℝ)*(driftRate β J : ℝ)^2+32/(N : ℝ))*S)

theorem actual_oneStep_euler_error (hN : 0<N) (hp : 2≤p) (D₀ : BrownianDriver N P F)
    (β S h : ℝ≥0) (hhS : h≤S) (J : Disorder N p)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (x : State N) (hx : OnSphere x) :
    (∫ ω,‖jointProcess (NullAugmentation.driver D₀) β R hR (J,x) h ω-
      node (NullAugmentation.driver D₀) β h J x 1 ω‖^2 ∂P)≤oneStepCeiling β J S*(h : ℝ)^2 := by
  let hb := drift_family_lipschitz (β : ℝ) R hR (‖J‖₊+1) ⟨J,by simp⟩
  let hs := noise_family_lipschitz N R hR
  have hg : grid h 1=h := by simp only [grid,Nat.cast_one,mul_one]
  have he : (fun ω => jointProcess (NullAugmentation.driver D₀) β R hR (J,x) h ω)=ᵐ[P]
      hardProcess D₀ β h J R hR hb hs x 1 h := by
    filter_upwards [jointProcess_ae (NullAugmentation.driver D₀) β R hR (J,x),
      GlobalSDE.process_eq_horizon (NullAugmentation.driver D₀) hb hs x (grid h 1)] with ω hactual hhor
    exact (hactual h).trans (hhor h (by rw [hg]))
  have hn : (fun ω => node (NullAugmentation.driver D₀) β h J x 1 ω)=
      fun ω => interpolant (NullAugmentation.driver D₀) β h J x 1 h ω := by
    funext ω
    have hnode := (interpolant_grid (NullAugmentation.driver D₀) β h J x (by rfl : 1≤1) ω).symm
    rw [hg] at hnode
    exact hnode
  have hEq : (∫ ω,‖jointProcess (NullAugmentation.driver D₀) β R hR (J,x) h ω-
      node (NullAugmentation.driver D₀) β h J x 1 ω‖^2 ∂P)=
      ∫ ω,‖hardProcess D₀ β h J R hR hb hs x 1 h ω-
        interpolant (NullAugmentation.driver D₀) β h J x 1 h ω‖^2 ∂P := by
    apply integral_congr_ae
    filter_upwards [he] with ω hω
    rw [hω,congrFun hn ω]
  rw [hEq]
  have hh := physical_euler_secondMoment hN hp D₀ β h J R hR hb hs x 1 hNR hx h (by rw [hg])
  rw [hg] at hh
  have hloc : (localCeiling β h J 1 : ℝ)=(2*(h : ℝ)*(driftCap β J : ℝ)^2+4*(N : ℝ))*(h : ℝ) := by
    unfold localCeiling
    change (2*(grid h 1 : ℝ)*(driftCap β J : ℝ)^2+4*(N : ℝ))*(h : ℝ)=_
    rw [hg]
  rw [hloc] at hh
  refine hh.trans ?_
  have hr : (2*(h : ℝ)*(driftCap β J : ℝ)^2+4*(N : ℝ))*
      (4*(h : ℝ)*(driftRate β J : ℝ)^2+32/(N : ℝ))*
        Real.exp ((4*(h : ℝ)*(driftRate β J : ℝ)^2+32/(N : ℝ))*h)≤oneStepCeiling β J S := by
    unfold oneStepCeiling
    have hhS' : (h : ℝ)≤S := by exact_mod_cast hhS
    gcongr
  have hh' := mul_le_mul_of_nonneg_right hr (sq_nonneg (h : ℝ))
  convert hh' using 1 <;> ring

end SphericalAging.ActualSphereOneStepEulerError
