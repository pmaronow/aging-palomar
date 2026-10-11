module

public import SphericalAging.PhysicalForkResponseDriverTransfer

public section

/-! Genuine integrability and full-product Fubini for weighted physical
fork traces, followed by their actual canonical response identification. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.PhysicalForkWeightedResponseTransfer
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open HardSphereDynamics FiniteModel TwoTimeResponseParameter TwoTimeResponseTimeParameter
open AnnealedTwoTimeResponseMoments ResponseMatrixEnergyContraction PhysicalForkDrivers
open ActualAnnealedEnergyReplacement ActualResponseTimeOperatorIntegrability
open ActualFiniteHorizonTraceReplacement PhysicalForkResponseDriverTransfer ActualResponseKernel
open scoped NNReal ENNReal InnerProductSpace
variable {N p K : ℕ}

theorem integrated_bounded_weighted_response (hN : 0<N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (trunk H : ℝ≥0) (b : Fin K)
    (U : WaitingTime H×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ]State N)
    (hU : StronglyMeasurable U)
    (hUs : ∀r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω)))=ᵐ[pathSeedLaw N K]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) (driver (N:=N) trunk b)
        β R hR hNR r (H+1) (H-r) q hx))
    (w : WaitingTime H→ℝ) (hw : StronglyMeasurable w)
    (C : ℝ) (hC : 0≤C) (hwb : ∀r,|w r|≤C) :
    Integrable (fun q => w q.1*EnergyCovarianceContraction.normalizedTrace (U q))
      ((waitingMeasure H).prod ((parameterLaw N p).prod (pathSeedLaw N K))) ∧
    (∫q,w q.1*EnergyCovarianceContraction.normalizedTrace (U q)
      ∂(waitingMeasure H).prod ((parameterLaw N p).prod (pathSeedLaw N K)))=
        ∫r,w r*annealedResponse (p:=p) (Nat.ne_of_gt hN) β R hR hNR H r ∂waitingMeasure H := by
  have ht := normalizedTrace_continuous.comp_stronglyMeasurable hU
  have hi : Integrable (fun q => EnergyCovarianceContraction.normalizedTrace (U q))
      ((waitingMeasure H).prod ((parameterLaw N p).prod (pathSeedLaw N K))) :=
    (actual_matrix_operator_integrable hN hp (driver (N:=N) trunk b) β R hR hNR H U hU hUs).mono'
      ht.aestronglyMeasurable (.of_forall fun q => by
        rw [Real.norm_eq_abs]
        exact EnergyCovarianceContraction.normalizedTrace_abs_le hN _)
  have hwi : Integrable (fun q => w q.1*EnergyCovarianceContraction.normalizedTrace (U q))
      ((waitingMeasure H).prod ((parameterLaw N p).prod (pathSeedLaw N K))) :=
    (hi.norm.const_mul C).mono' ((hw.comp_fst).mul ht).aestronglyMeasurable (.of_forall fun q => by
      rw [Real.norm_eq_abs,abs_mul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hwb q.1) (abs_nonneg _))
  refine ⟨hwi,?_⟩
  rw [integral_prod _ hwi]
  simp_rw [integral_const_mul]
  exact weighted_response_primitive hN hp β R hR hNR trunk H b U hU hUs w

/-- Unit-bounded weights include every nonnegative correlation power in
the finite-fork energy calculation. -/
theorem integrated_weighted_response (hN : 0<N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (trunk H : ℝ≥0) (b : Fin K)
    (U : WaitingTime H×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ]State N)
    (hU : StronglyMeasurable U)
    (hUs : ∀r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω)))=ᵐ[pathSeedLaw N K]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) (driver (N:=N) trunk b)
        β R hR hNR r (H+1) (H-r) q hx))
    (w : WaitingTime H→ℝ) (hw : StronglyMeasurable w) (hwb : ∀r,|w r|≤1) :
    Integrable (fun q => w q.1*EnergyCovarianceContraction.normalizedTrace (U q))
      ((waitingMeasure H).prod ((parameterLaw N p).prod (pathSeedLaw N K))) ∧
    (∫q,w q.1*EnergyCovarianceContraction.normalizedTrace (U q)
      ∂(waitingMeasure H).prod ((parameterLaw N p).prod (pathSeedLaw N K)))=
        ∫r,w r*annealedResponse (p:=p) (Nat.ne_of_gt hN) β R hR hNR H r ∂waitingMeasure H :=
  integrated_bounded_weighted_response hN hp β R hR hNR trunk H b U hU hUs w hw 1 zero_le_one hwb

end SphericalAging.PhysicalForkWeightedResponseTransfer
