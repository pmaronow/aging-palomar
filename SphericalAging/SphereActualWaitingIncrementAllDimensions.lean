module

public import SphericalAging.SphereSharpWaitingRealization
public import SphericalAging.SphereSharpMeanGradient

public section

/-! Literal finite waiting increments with the sharp actual SDE mean
rate. The positive forward density and smooth backward mean realization
are preceding analytic inputs; no derivative or increment estimate is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.SphereActualWaitingIncrementAllDimensions
open FiniteModel HardSphereDynamics SphereOnSphereCurrent SphereWaitingIncrement
open ActualSphereTransition ActualSphereMeanDerivative SphereSharpMeanDerivative
open SphereSharpWaitingRealization SphereFisherHelly SphereQuenchedFDT
set_option maxHeartbeats 1800000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem waiting_mean_derivative_bound (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (M : SphereBackwardMean N p β)
    (J : Disorder N p) {τ : ℝ} (hτ : 0≤τ)
    (heq : ∀x,OnSphere x → M.m J τ x=mean (NullAugmentation.driver D₀) β R hR J τ.toNNReal x)
    (x v : State N) (hx : OnSphere x) :
    ‖fderiv ℝ (M.m J τ) x (projection x v)‖≤
      Real.exp ((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J*τ)*‖v‖ := by
  have hn : 0<N := by omega
  let t := τ.toNNReal
  let T : ℝ≥0 := t+1
  have ht : t≤T := by dsimp [T];simp
  have hT : 0<T := by dsimp [T];positivity
  have hv := projection_tangent (Nat.ne_of_gt hn) x v hx
  have hd := (mean_hasFDerivAt D₀ β J R hR x T t ht hT).differentiableAt
  have hm := (mean_row_contDiff M J τ).differentiable (by norm_num) x
  rw [tangent_derivative_eq_of_sphere_agreement hn hx hv hm hd heq]
  simpa only [t,Real.coe_toNNReal _ hτ] using
    SphereSharpMeanGradient.actual_mean_tangent_derivative_bound hN hp D₀ β R hR hNR J x v hx t

theorem waiting_increment_square_bound_of_actual_mean (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (E : FisherDensity N p β) (M : SphereBackwardMean N p β)
    (J : Disorder N p) {τ u v : ℝ} (hτ : 0≤τ) (hu : 0≤u) (huv : u≤v)
    (heq : ∀x,OnSphere x → M.m J τ x=mean (NullAugmentation.driver D₀) β R hR J τ.toNNReal x) :
    (quenchedCorrelation (E.ρ J) (M.m J) (v+τ) v-
      quenchedCorrelation (E.ρ J) (M.m J) (u+τ) u)^2≤
        (1+Real.exp ((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J*τ))^2*(v-u)*
          (∫ w in u..v,SphereRotationGeometry.fisherInformation β J (E.ρ J w)/(N:ℝ)) := by
  have hn : 0<N := by omega
  exact waiting_increment_square_bound hn E M J hτ (Real.exp_nonneg _) hu huv
    (fun x hx v => waiting_mean_derivative_bound hN hp D₀ β R hR hNR M J hτ heq x v hx)

end SphericalAging.SphereActualWaitingIncrementAllDimensions
