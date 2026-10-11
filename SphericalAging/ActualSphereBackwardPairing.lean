module

public import SphericalAging.PredictablePrefixPairing
public import SphericalAging.ActualSphereLinearRegularity

public section

/-! Exact pairing of the actual backward innovation with an actual
Brownian coordinate, derived from the constructed full-filtration Itô integral. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualSphereBackwardPairing
open HardSphereDynamics LocalSDE VectorIto AnnealedSDECore MultivariateTaylor
open ActualSphereTransition ActualSphereBackwardIto PhysicalC2Ito
open PredictablePrefixPairing ActualSphereBackwardVariance
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- Genuine cross-Itô pairing, retaining a random initial conditional mean.
Both the true kernel and its integrability follow from the constructed integrand. -/
theorem backward_transition_pairing (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    {Z0 : VectorBrownian.Space N → State N}
    (X : ℝ≥0 → VectorBrownian.Space N → State N) (T s : ℝ≥0) (j : Fin N)
    (hX : IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i k z => noiseColumn z k i) Z0 X T)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ t,OnSphere (X t ω))
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (hreg : SpatialC2Transition β R hR J f) :
    (∫ ω,(f (X T ω)-transition (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J T f (Z0 ω))*VectorBrownian.coordinate j s ω ∂VectorBrownian.law N)=
    ∫ r in Ioc (0 : ℝ≥0) (min T s),∫ ω,
      fderiv ℝ (transition (NullAugmentation.driver (VectorBrownian.driver N))
        β R hR J (T-r) f) (X r ω) (noiseColumn (X r ω) j)
          ∂VectorBrownian.law N ∂nonnegativeLebesgueMeasure := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let P₀ := VectorBrownian.law N
  let F₀ := NullAugmentation.augment (VectorBrownian.filtration N) P₀
  let g (k : Fin N) (r : ℝ≥0) (ω : VectorBrownian.Space N) :=
    fderiv ℝ (transition D β R hR J (T-r) f) (X r ω) (noiseColumn (X r ω) k)
  obtain ⟨V,hV,he⟩ := backward_transition_ito hN β R hR hNR J X T hX hSphere hf hreg
  let U (k : Fin N) : PredictableProcessL2 F₀ P₀ := ∑ i,V i k
  have hU (k : Fin N) : (U k : TimeProcessL2 P₀)=ᵐ[nonnegativeLebesgueMeasure.prod P₀]
      FourPapersCommon.continuousAdaptedTimeCut (g k) T := by
    have hcoe := Lp.coeFn_fun_finsetSum Finset.univ (fun i => (V i k : TimeProcessL2 P₀))
    have hrows := ae_all_iff.mpr (fun i : Fin N => hV i k)
    filter_upwards [hcoe,hrows] with q hq hv
    have hq' : (U k : TimeProcessL2 P₀) q=∑ i : Fin N,(V i k : TimeProcessL2 P₀) q := by
      simpa only [U,Submodule.coe_sum] using hq
    rw [hq']
    simp only [hv,FourPapersCommon.continuousAdaptedTimeCut]
    split_ifs with hr
    · exact (derivative_coordinates _ _ _).symm
    · simp
  have hsum : ∀ᵐ ω ∂P₀,(vectorIto D U : VectorBrownian.Space N → ℝ) ω=
      ∑ i : Fin N,(vectorIto D (V i) : VectorBrownian.Space N → ℝ) ω := by
    rw [show vectorIto D U=∑ i : Fin N,vectorIto D (V i) from vectorIto_sum_rows D V]
    exact Lp.coeFn_fun_finsetSum Finset.univ _
  have hinnov : (fun ω => f (X T ω)-transition D β R hR J T f (Z0 ω))=ᵐ[P₀]
      (vectorIto D U : VectorBrownian.Space N → ℝ) := by
    filter_upwards [he,hsum] with ω heω hsω
    linarith
  calc
    _ = ∫ ω,(vectorIto D U : VectorBrownian.Space N → ℝ) ω*D.coordinate j s ω ∂P₀ :=
      integral_congr_ae (hinnov.mono (fun ω h => congrArg (fun z : ℝ => z*D.coordinate j s ω) h))
    _ = _ := vectorIto_coordinate_timeCut D U j (g j) T s (hU j)

/-- The linear backward kernel is the derivative of the actual mean, with
its genuine physical noise column. All spatial regularity is proved. -/
theorem linear_innovation_pairing (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    {Z0 : VectorBrownian.Space N → State N}
    (X : ℝ≥0 → VectorBrownian.Space N → State N) (T s : ℝ≥0) (a : State N) (j : Fin N)
    (hX : IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i k z => noiseColumn z k i) Z0 X T)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ t,OnSphere (X t ω)) :
    (∫ ω,(⟪a,X T ω⟫_ℝ-⟪a,ActualSphereTransition.mean
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J T (Z0 ω)⟫_ℝ)*
        VectorBrownian.coordinate j s ω ∂VectorBrownian.law N)=
    ∫ r in Ioc (0 : ℝ≥0) (min T s),∫ ω,
      ⟪a,fderiv ℝ (ActualSphereTransition.mean
        (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (T-r))
        (X r ω) (noiseColumn (X r ω) j)⟫_ℝ
          ∂VectorBrownian.law N ∂nonnegativeLebesgueMeasure := by
  have he := backward_transition_pairing hN β R hR hNR J X T s j hX hSphere
    (f := fun y => ⟪a,y⟫_ℝ) (innerSL ℝ a).contDiff (ActualSphereLinearRegularity.linear_spatialC2Transition β R hR J a)
  simpa only [ActualSphereLinearTransition.transition_inner_eq_mean,
    ActualSphereLinearTransition.fderiv_transition_inner] using he

end SphericalAging.ActualSphereBackwardPairing
