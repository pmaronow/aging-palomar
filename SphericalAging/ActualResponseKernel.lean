module

public import SphericalAging.ActualQuenchedBrownianPairing
public import SphericalAging.TwoTimeResponseTimeParameter

public section

/-! Genuine fixed-terminal response kernels, with simultaneous waiting-time
and parameter measurability and the exact literal finite-N diagonal. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualResponseKernel
open HardSphereDynamics ActualSphereTransition ActualSphereMeanDerivative
open TwoTimeResponseParameter TwoTimeResponseTimeParameter TwoTimeResponseTrace
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- Expected normalized trace of the actual fixed-terminal projected
response, using genuine L² response columns. -/
@[expose] def quenchedResponse (hN : N≠0) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0) (s : WaitingTime H)
    (q : FiniteModel.Disorder N p × State N) : ℝ :=
  (∑ j : Fin N,⟪basisVector j,expectationOperator
    (fixedTerminalColumn hN (VectorBrownian.driver N) β R hR hNR H (basisVector j) s q)⟫_ℝ)/(N : ℝ)

/-- Actual annealed response under the literal independent disorder and
uniform sphere initial-state law. -/
@[expose] def annealedResponse (hN : N≠0) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0) (s : WaitingTime H) : ℝ :=
  ∫ q,quenchedResponse hN β R hR hNR H s q ∂AnnealedModelLaw.parameterLaw N p

/-- This kernel is exactly the normalized trace of the physical projected
matrix, on every actual sphere initial-state section. -/
theorem quenchedResponse_eq_normalizedTrace (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0) (s : WaitingTime H)
    (q : FiniteModel.Disorder N p × State N) (hx : OnSphere q.2) :
    quenchedResponse hN β R hR hNR H s q=
      normalizedTrace (physicalMatrix hN (VectorBrownian.driver N) β R hR hNR s (H+1) (H-s) q hx) := by
  let M := physicalMatrix hN (VectorBrownian.driver N) β R hR hNR s (H+1) (H-s) q hx
  have hc (j : Fin N) : fixedTerminalColumn hN (VectorBrownian.driver N) β R hR hNR H
      (basisVector j) s q=M (basisVector j) := by
    simp only [fixedTerminalColumn,dif_pos hx,M]
  have hi (j : Fin N) : Integrable
      (fun ω => ⟪basisVector j,(M (basisVector j)) ω⟫_ℝ) (VectorBrownian.law N) :=
    ((Lp.memLp (M (basisVector j))).continuousLinearMap_comp (innerSL ℝ (basisVector j))).integrable (by norm_num)
  simp only [quenchedResponse,hc,expectationOperator_apply,normalizedTrace,integral_div]
  congr 1
  rw [integral_finsetSum _ (fun j _ => hi j)]
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [innerSL_apply_apply] using
    ((innerSL ℝ (basisVector j)).integral_comp_comm ((Lp.memLp (M (basisVector j))).integrable (by norm_num))).symm

/-- Joint waiting-time, disorder and initial-state measurability follows
from the true restarted-flow derivative; no measurable matrix is postulated. -/
theorem quenchedResponse_joint_stronglyMeasurable (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0) :
    StronglyMeasurable (Function.uncurry (quenchedResponse (p := p) hN β R hR hNR H)) := by
  have hh := Finset.stronglyMeasurable_sum Finset.univ (fun j _ =>
    (innerSL ℝ (basisVector j)).continuous.comp_stronglyMeasurable
      (expectationOperator.continuous.comp_stronglyMeasurable
        (fixedTerminalColumn_joint_stronglyMeasurable (p := p) hN (VectorBrownian.driver N)
          β R hR hNR H (basisVector j))))
  have hdiv := (continuous_id.div_const (N : ℝ)).comp_stronglyMeasurable hh
  convert hdiv using 1
  funext z
  simp only [quenchedResponse,Function.uncurry,Finset.sum_apply,innerSL_apply_apply,id_eq]

theorem annealedResponse_stronglyMeasurable (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0) :
    StronglyMeasurable (annealedResponse (p := p) hN β R hR hNR H) :=
  (quenchedResponse_joint_stronglyMeasurable hN β R hR hNR H).integral_prod_right'

section GenericDiagonal
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
/-- Every true physical matrix has its literal finite-N projection
trace on the diagonal. -/
theorem physicalMatrix_diagonal (hN : N≠0) (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (s T : ℝ≥0)
    (q : FiniteModel.Disorder N p × State N) (hx : OnSphere q.2) :
    normalizedTrace (physicalMatrix hN D₀ β R hR hNR s T 0 q hx)=kappa N := by
  let hsol := globalProcess_physicalSolution hN D₀ β R hR hNR q.1 q.2 hx (s+T)
  let hall := globalProcess_onSphere hN D₀ β R hR hNR q.1 q.2 hx
  let X := HamiltonianJointProcess.globalProcess (NullAugmentation.driver D₀) β R hR q
  change normalizedTrace (TwoTimeResponseMatrix.terminalResponse hN
    (NullAugmentation.driver D₀) X hsol.choose hsol.choose_spec.choose
    β q.1 R hR (HamiltonianPicardDependence.drift_family_lipschitz β R hR (‖q.1‖₊+1) ⟨q.1,by simp⟩)
    (HamiltonianPicardDependence.noise_family_lipschitz N R hR) s T (hall.mono (fun _ h => h s)) 0)=_
  exact response_diagonal hN (NullAugmentation.driver D₀) X
    hsol.choose hsol.choose_spec.choose β q.1 R hR hNR
    (HamiltonianPicardDependence.drift_family_lipschitz β R hR (‖q.1‖₊+1) ⟨q.1,by simp⟩)
    (HamiltonianPicardDependence.noise_family_lipschitz N R hR) s T
    (hall.mono (fun _ h => h s)) (hall.mono (fun _ h t _ => h t))

end GenericDiagonal

/-- The actual quenched response diagonal is (N−1)/N. -/
theorem quenchedResponse_diagonal (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0)
    (q : FiniteModel.Disorder N p × State N) (hx : OnSphere q.2) :
    quenchedResponse hN β R hR hNR H ⟨H,⟨zero_le,le_rfl⟩⟩ q=kappa N := by
  let s : WaitingTime H := ⟨H,⟨zero_le,le_rfl⟩⟩
  have hz : H-(s : ℝ≥0)=0 := tsub_self H
  calc
    _ = normalizedTrace (physicalMatrix hN (VectorBrownian.driver N) β R hR hNR
        s (H+1) (H-s) q hx) := quenchedResponse_eq_normalizedTrace hN β R hR hNR H s q hx
    _ = normalizedTrace (physicalMatrix hN (VectorBrownian.driver N) β R hR hNR
        H (H+1) 0 q hx) := congrArg (fun t : ℝ≥0 => normalizedTrace
          (physicalMatrix hN (VectorBrownian.driver N) β R hR hNR H (H+1) t q hx)) hz
    _ = _ := physicalMatrix_diagonal hN (VectorBrownian.driver N) β R hR hNR H (H+1) q hx

/-- The exact source 3.4 finite-N diagonal survives actual annealing. -/
theorem annealedResponse_diagonal (hN : 0<N) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0) :
    annealedResponse (p := p) (Nat.ne_of_gt hN) β R hR hNR H ⟨H,⟨zero_le,le_rfl⟩⟩=kappa N := by
  have he : quenchedResponse (p := p) (Nat.ne_of_gt hN) β R hR hNR H ⟨H,⟨zero_le,le_rfl⟩⟩
      =ᵐ[AnnealedModelLaw.parameterLaw N p] fun _ => kappa N := by
    filter_upwards [AnnealedModelLaw.parameter_initial_onSphere hN p] with q hq
    exact quenchedResponse_diagonal (Nat.ne_of_gt hN) β R hR hNR H q hq
  rw [annealedResponse,integral_congr_ae he]
  simp

end SphericalAging.ActualResponseKernel
