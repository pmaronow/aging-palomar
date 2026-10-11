module

public import SphericalAging.ActualSphereBrownianPairing
public import SphericalAging.WienerTrunkWeight

public section

/-! The normalized Brownian primitive for the actual fixed-disorder sphere
process, identified with its genuine backward mean tangent trace. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualQuenchedBrownianPairing
open HardSphereDynamics ActualSphereTransition ActualSphereMarkovRestart
open ActualSphereBrownianPairing
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- The genuine expected backward mean tangent trace along the actual
fixed-disorder process, normalized by its physical dimension. -/
@[expose] def backwardMeanKernel (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : FiniteModel.Disorder N p) (x : State N) (T r : ℝ≥0) : ℝ :=
  (∫ ω,∑ j : Fin N,⟪basisVector j,fderiv ℝ (mean
    (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (T-r))
    (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) r ω)
    (projection (jointProcess (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR (J,x) r ω) (basisVector j))⟫_ℝ ∂VectorBrownian.law N)/(N : ℝ)

/-- Actual time-integrability of the normalized backward trace kernel. -/
theorem backwardMeanKernel_integrable (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (x : State N) (hx : OnSphere x) (T s : ℝ≥0) :
    IntegrableOn (backwardMeanKernel β R hR J x T)
      (Ioc (0 : ℝ≥0) (min T s)) nonnegativeLebesgueMeasure := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let X := jointProcess D β R hR (J,x)
  have hX := jointProcess_physical hN (VectorBrownian.driver N) β R hR hNR J x hx T
  have hsphere := jointProcess_onSphere hN (VectorBrownian.driver N) β R hR hNR J x hx
  have hi (j : Fin N) := projected_kernel_time_integrable hN β R hR hNR J X T s
    (basisVector j) j hX hsphere
  have hg (r : ℝ≥0) (j : Fin N) := projected_kernel_integrable β R hR hNR J X
    hX.2.1 hsphere (T-r) r (basisVector j) j
  have hsum := (integrable_finsetSum Finset.univ (fun j _ => hi j)).div_const (N : ℝ)
  apply hsum.congr
  exact .of_forall (fun r => by
    dsimp only [backwardMeanKernel]
    congr 1
    exact (integral_finsetSum _ (fun j _ => hg r j)).symm)

/-- The literal quenched finite-N Brownian primitive equals the integral
of the true backward mean tangent trace. Every strong-SDE and spatial
regularity input is proved from the actual constructed process. -/
theorem quenched_pairing (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (x : State N) (hx : OnSphere x) (T s : ℝ≥0) (hs : s≤T) :
    (∫ r in Ioc (0 : ℝ≥0) s,backwardMeanKernel β R hR J x T r
      ∂nonnegativeLebesgueMeasure)=
    (∫ ω,⟪jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) T ω,
      WithLp.toLp 2 (fun j => VectorBrownian.coordinate j s ω)⟫_ℝ ∂VectorBrownian.law N)/
        (Real.sqrt 2*(N : ℝ)) := by
  have he := brownian_trace_pairing hN β R hR hNR J x
    (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x)) T s
    (jointProcess_physical hN (VectorBrownian.driver N) β R hR hNR J x hx T)
    (jointProcess_onSphere hN (VectorBrownian.driver N) β R hR hNR J x hx)
  rw [min_eq_right hs] at he
  simp only [backwardMeanKernel,integral_div]
  rw [he]
  have hn : (N : ℝ)≠0 := Nat.cast_ne_zero.mpr hN
  have hsq : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2)).ne'
  field_simp

/-- The same exact primitive in the source's real interval notation. -/
theorem quenched_pairing_interval (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (x : State N) (hx : OnSphere x) (T s : ℝ≥0) (hs : s≤T) :
    (∫ r in (0 : ℝ)..(s : ℝ),backwardMeanKernel β R hR J x T r.toNNReal)=
    (∫ ω,⟪jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) T ω,
      WithLp.toLp 2 (fun j => VectorBrownian.coordinate j s ω)⟫_ℝ ∂VectorBrownian.law N)/
        (Real.sqrt 2*(N : ℝ)) := by
  have he := WienerTrunkWeight.nnreal_interval_integral s
    (fun r : ℝ => backwardMeanKernel β R hR J x T r.toNNReal)
  simp only [Real.toNNReal_coe] at he
  rw [← he]
  exact quenched_pairing hN β R hR hNR J x hx T s hs

end SphericalAging.ActualQuenchedBrownianPairing
