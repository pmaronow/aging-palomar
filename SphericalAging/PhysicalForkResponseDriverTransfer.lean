module

public import SphericalAging.TwoTimeResponseDriverPullback
public import SphericalAging.PhysicalForkDrivers
public import SphericalAging.ActualResponseKernel
public import SphericalAging.ActualAnnealedEnergyReplacement

public section

/-! The true response of each whole-path fork driver has the canonical
actual annealed response expectation. All projected flow derivatives and
sample-trace laws are derived from actual SDE uniqueness and L² pullback. -/
noncomputable section
set_option maxHeartbeats 1900000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.PhysicalForkResponseDriverTransfer
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open HardSphereDynamics FiniteModel GlobalSDEDriverPullback TwoTimeResponseDriverPullback
open TwoTimeResponseParameter TwoTimeResponseTimeParameter ActualResponseKernel
open AnnealedTwoTimeResponseMoments ResponseMatrixEnergyContraction ActualAnnealedEnergyReplacement
open ActualFiniteHorizonTraceReplacement PhysicalForkDrivers
open scoped NNReal ENNReal InnerProductSpace
variable {N p K : ℕ}

/-- Literal quenched expectation of the actual fork response. -/
theorem physical_expected_sampleTrace (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (trunk H : ℝ≥0)
    (b : Fin K) (r : WaitingTime H) (q : Disorder N p×State N) (hx : OnSphere q.2) :
    (∫ω,sampleTrace (physicalMatrix hN (driver (N:=N) trunk b)
      β R hR hNR r (H+1) (H-r) q hx) ω ∂pathSeedLaw N K)=
      quenchedResponse hN β R hR hNR H r q := by
  exact (physical_expected_sampleTrace_pullback (branchPath_measurePreserving trunk b)
    hN β R hR hNR r (H+1) (H-r)
    ((tsub_le_self).trans (le_add_of_nonneg_right zero_le)) (by positivity) q hx).trans
      (quenchedResponse_eq_normalizedTrace hN β R hR hNR H r q hx).symm

/-- Any genuine jointly measurable physical matrix representative under
a measure-preserving Wiener sampler has the actual canonical response
expectation. The preceding representation is supplied by the physical
response construction, not an expected-trace hypothesis. -/
theorem sampled_expected_trace_eq_annealedResponse
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ψ : Ω→VectorBrownian.Space N}
    (hψ : MeasurePreserving ψ P (VectorBrownian.law N))
    (hN : 0<N) (hp : 2≤p) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (H : ℝ≥0)
    (U : WaitingTime H×((Disorder N p×State N)×Ω)→State N→L[ℝ]State N)
    (hU : StronglyMeasurable U)
    (hUs : ∀r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω)))=ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN)
        (BrownianDriverPullback.driver (VectorBrownian.driver N) hψ)
        β R hR hNR r (H+1) (H-r) q hx)) (r : WaitingTime H) :
    (∫q,EnergyCovarianceContraction.normalizedTrace (U (r,q))
      ∂(parameterLaw N p).prod P)=
        annealedResponse (p:=p) (Nat.ne_of_gt hN) β R hR hNR H r := by
  have hi := ((actual_trace_fourthMoments hN hp
    (BrownianDriverPullback.driver (VectorBrownian.driver N) hψ)
    β R hR hNR H U hU hUs r).1).integrable (by norm_num : (1:ℝ≥0∞)≤4)
  rw [integral_prod _ hi,annealedResponse]
  apply integral_congr_ae
  filter_upwards [parameterLaw_onSphere (p:=p) hN] with q hq
  calc
    _=∫ω,sampleTrace (physicalMatrix (Nat.ne_of_gt hN)
        (BrownianDriverPullback.driver (VectorBrownian.driver N) hψ)
        β R hR hNR r (H+1) (H-r) q hq) ω ∂P := by
      apply integral_congr_ae
      filter_upwards [hUs r q hq] with ω hω
      rw [hω]
      exact (sampleTrace_eq _ ω).symm
    _=∫ω,sampleTrace (physicalMatrix (Nat.ne_of_gt hN) (VectorBrownian.driver N)
        β R hR hNR r (H+1) (H-r) q hq) ω ∂VectorBrownian.law N :=
      physical_expected_sampleTrace_pullback hψ (Nat.ne_of_gt hN) β R hR hNR
        r (H+1) (H-r) ((tsub_le_self).trans (le_add_of_nonneg_right zero_le))
        (by positivity) q hq
    _=quenchedResponse (Nat.ne_of_gt hN) β R hR hNR H r q :=
      (quenchedResponse_eq_normalizedTrace (Nat.ne_of_gt hN) β R hR hNR H r q hq).symm

/-- The complete fork-driver law discharges the response expectation
bridge for every branch and every waiting time, including the diagonal. -/
theorem expected_trace_eq_annealedResponse (hN : 0<N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (trunk H : ℝ≥0) (b : Fin K)
    (U : WaitingTime H×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ]State N)
    (hU : StronglyMeasurable U)
    (hUs : ∀r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω)))=ᵐ[pathSeedLaw N K]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) (driver (N:=N) trunk b)
        β R hR hNR r (H+1) (H-r) q hx)) (r : WaitingTime H) :
    (∫q,EnergyCovarianceContraction.normalizedTrace (U (r,q))
      ∂(parameterLaw N p).prod (pathSeedLaw N K))=
        annealedResponse (p:=p) (Nat.ne_of_gt hN) β R hR hNR H r :=
  sampled_expected_trace_eq_annealedResponse (branchPath_measurePreserving trunk b)
    hN hp β R hR hNR H U hU hUs r

/-- Every deterministic weighted response primitive agrees literally
with the canonical actual-model primitive under the genuine fork law. -/
theorem weighted_response_primitive (hN : 0<N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (trunk H : ℝ≥0) (b : Fin K)
    (U : WaitingTime H×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ]State N)
    (hU : StronglyMeasurable U)
    (hUs : ∀r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω)))=ᵐ[pathSeedLaw N K]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) (driver (N:=N) trunk b)
        β R hR hNR r (H+1) (H-r) q hx)) (w : WaitingTime H→ℝ) :
    (∫r,w r*(∫q,EnergyCovarianceContraction.normalizedTrace (U (r,q))
      ∂(parameterLaw N p).prod (pathSeedLaw N K)) ∂waitingMeasure H)=
      ∫r,w r*annealedResponse (p:=p) (Nat.ne_of_gt hN) β R hR hNR H r ∂waitingMeasure H := by
  congr 1
  funext r
  rw [expected_trace_eq_annealedResponse hN hp β R hR hNR trunk H b U hU hUs r]

end SphericalAging.PhysicalForkResponseDriverTransfer
