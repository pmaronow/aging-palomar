module

public import SphericalAging.AnnealedBrownianHamiltonianStein
public import SphericalAging.ActualBrownianResponseCoefficientPairing
public import SphericalAging.ActualAnnealedMixedResponseContraction

public section

/-! Exact actual annealed Hamiltonian-gradient/Brownian causal memory.
Every time, disorder, normalized sphere and Wiener exchange is justified
by proved actual operator and Brownian L² moment bounds. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualAnnealedBrownianResponseContraction
open HardSphereDynamics FiniteModel GaussianIntegrationByParts
  AnnealedBrownianHamiltonianStein ActualBrownianResponseCoefficientIntegral
  ActualBrownianResponseCoefficientPairing IndependentMixedCoefficientDerivative IndependentMixedCoefficientDuhamel
  ActualAnnealedMixedResponseContraction ActualResponseCoefficientIntegral ActualDisorderGammaVariance
  HamiltonianDisorderTerminalDerivative TwoTimeResponseParameter TwoTimeResponseTimeParameter
  ResponseMatrixEnergyContraction ActualFiniteHorizonTraceReplacement AnnealedResponseTimeMatrix
  AnnealedResponseMatrixContraction AnnealedTwoTimeResponseMoments
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

 theorem actual_brownian_gradient_eq_integrated_contractions (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (T s t : ℝ≥0) (hs : s≤T) (ht : t≤T)
    (U : WaitingTime t×Sample N p → (State N →L[ℝ] State N)) (hU : StronglyMeasurable U)
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[VectorBrownian.law N]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR
        r (t+1) (t-r) q hx)) :
    (∫ q : Sample N p,
      inner ℝ (hamiltonianGradient q.1.1 (AnnealedHamiltonianEnergyStein.process (VectorBrownian.driver N) β R hR t q))
        (BrownianVectorMoments.brownianVector s q.2)
        ∂(AnnealedModelLaw.parameterLaw N p).prod (VectorBrownian.law N))=
      (β : ℝ)*(∫ q,∑ I : TensorIndex N p,brownianHessianField β R hR t s U I q
        ∂(waitingMeasure t).prod ((parameterLaw N p).prod (VectorBrownian.law N))) := by
  let f := brownianHessianField β R hR t s U
  have hfi (I : TensorIndex N p) := brownianHessianField_integrable hN hp β R hR hNR t s U hU hUs I
  have hfβ (I : TensorIndex N p) := (hfi I).const_mul (β : ℝ)
  have hn (I : TensorIndex N p) := integral_time_disorder_initial_brownian (hfβ I)
  have he : (∫ q : Sample N p,
      inner ℝ (hamiltonianGradient q.1.1 (AnnealedHamiltonianEnergyStein.process (VectorBrownian.driver N) β R hR t q))
        (BrownianVectorMoments.brownianVector s q.2) ∂(AnnealedModelLaw.parameterLaw N p).prod (VectorBrownian.law N))=
      ∫ x : State N,∑ I : TensorIndex N p,∫ J : Disorder N p,∫ r : WaitingTime t,∫ ω,
        (β : ℝ)*f I (r,((J,x),ω)) ∂VectorBrownian.law N ∂waitingMeasure t ∂disorderLaw N p ∂SphereInitialLaw.sphereLaw N := by
    rw [actual_brownian_gradient_pairing_stein hN (by omega : 0<p) β R hR hNR T s t hs ht]
    apply integral_congr_ae
    filter_upwards [SphereInitialLaw.sphereLaw_support hN] with x hx
    have hx' := (onSphere_iff_norm_sq x).mpr hx
    apply Finset.sum_congr rfl
    intro I _
    apply integral_congr_ae
    exact .of_forall (fun J => by
      dsimp only
      have hB : (∫ ω,inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I))
        (stateClass (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J x T t ω)
        (stateResponse (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J x T t (Pi.single I 1) ω))
        (BrownianVectorMoments.brownianVector s ω) ∂VectorBrownian.law N)=
          coefficientResponseObservable (VectorBrownian.driver N) β R hR x T t I (brownianClass s) J := by
        unfold coefficientResponseObservable
        apply integral_congr_ae
        filter_upwards [brownianClass_ae s] with ω hω
        rw [hω]
      rw [hB,(independent_derivative_matrix_duhamel (Nat.ne_of_gt hN) (VectorBrownian.driver N)
        β J R hR hNR x hx' T t ht I (brownianClass s)).2,← waiting_integral t]
      apply integral_congr_ae
      exact .of_forall (fun r => (brownianHessianField_pairing hN β R hR hNR T t s ht U hUs I r (J,x) hx').symm.trans
        (integral_const_mul (β : ℝ) (fun ω => f I (r,((J,x),ω)))).symm))
  rw [he]
  rw [integral_finsetSum Finset.univ (fun I _ => (hn I).1)]
  simp_rw [← (hn _).2,integral_const_mul]
  rw [← Finset.mul_sum]
  simp only [parameterLaw] at hfi ⊢
  rw [← integral_finsetSum Finset.univ (fun I _ => hfi I)]

end SphericalAging.ActualAnnealedBrownianResponseContraction
