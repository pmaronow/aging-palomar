module

public import SphericalAging.ActualSphereWeightedFutureIncrement

public section

/-! Brownian-past-weighted actual physical fourth increments, derived
from the genuine waiting-time restart and independent future law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualSphereWeightedPhysicalIncrement
open FiniteModel HardSphereDynamics ActualSphereTransition ActualSphereMarkovRestart
open BrownianVectorMoments ActualSphereInitialFourthIncrement ActualSphereWeightedFutureIncrement
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem actual_weighted_fourth (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p) (S r h : ℝ≥0) (hhS : h≤S)
    {Z0 : VectorBrownian.Space N→State N} (X : ℝ≥0→VectorBrownian.Space N→State N)
    (hX : ∀ T,AnnealedSDECore.IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X T)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ u,OnSphere (X u ω)) :
    Integrable (fun ω => (1+‖brownianVector r ω‖^2)*‖X (r+h) ω-X r ω‖^4) (VectorBrownian.law N) ∧
    (∫ ω,(1+‖brownianVector r ω‖^2)*‖X (r+h) ω-X r ω‖^4 ∂VectorBrownian.law N)≤
      smallFourthCeiling β J S*(h : ℝ)^2*(1+(N : ℝ)*r) := by
  have hh := weighted_future_fourth hN β R hR hNR J S r h hhS (X r)
    ((hX 0).2.1 r).measurable (hSphere.mono (fun _ hh => hh r))
  have he := actual_future_eq_joint (Nat.ne_of_gt hN) β R hR hNR J X hX hSphere r h
  have hv : (fun ω => (1+‖brownianVector r ω‖^2)*‖X (r+h) ω-X r ω‖^4)=ᵐ[VectorBrownian.law N]
      fun ω => (1+‖brownianVector r ω‖^2)*
        ‖jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,X r ω) h (BrownianFuturePath.future r ω)-X r ω‖^4 := by
    filter_upwards [he] with ω hω
    rw [hω]
  exact ⟨hh.1.congr hv.symm,(integral_congr_ae hv).trans_le hh.2⟩

end SphericalAging.ActualSphereWeightedPhysicalIncrement
