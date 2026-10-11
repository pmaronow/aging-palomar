module

public import SphericalAging.AnnealedResponseMatrixContraction
public import SphericalAging.ResponseTraceReplacement

public section

/-! Actual annealed overlap replacement against the signed normalized
two-time response trace. Its moment is derived from the genuine physical
columns under disorder × sphere initial-state × Brownian law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.AnnealedResponseTraceReplacement
open HardSphereDynamics FiniteModel FiniteCorrelationIto EnergyCovarianceContraction
open TwoTimeResponseParameter ResponseMatrixEnergyContraction
open AnnealedTwoTimeResponseMoments AnnealedResponseMatrixContraction
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem exists_actual_weighted_trace_replacement (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (s T t : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    ∃ U : (Disorder N p × State N) × Ω → (State N →L[ℝ] State N),StronglyMeasurable U ∧
      (∀ q (hx : OnSphere q.2),(fun ω => U (q,ω)) =ᵐ[P]
        sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s T t q hx)) ∧
      (∀ (n : ℕ) (b : ℝ),|b|≤1 →
        let a := fun q => overlap (trajectory (NullAugmentation.driver D₀) β R hR (s+t) q)
          (trajectory (NullAugmentation.driver D₀) β R hR s q)
        Integrable (fun q => |((a q)^n-b^n)*normalizedTrace (U q)|) ((parameterLaw N p).prod P) ∧
        (∫ q,|((a q)^n-b^n)*normalizedTrace (U q)| ∂(parameterLaw N p).prod P)≤
          (n : ℝ)*Real.sqrt (∫ q,(a q-b)^2 ∂(parameterLaw N p).prod P)*
            Real.sqrt (1+annealedFourthConstant p β t)) := by
  obtain ⟨U,hU,hUs,htrace,htraceB,_⟩ := exists_actual_annealed_matrix hN hp D₀ β R hR hNR s T t ht hT
  refine ⟨U,hU,hUs,?_⟩
  intro n b hb
  dsimp only
  have ha : AEStronglyMeasurable (fun q => overlap
      (trajectory (NullAugmentation.driver D₀) β R hR (s+t) q)
      (trajectory (NullAugmentation.driver D₀) β R hR s q)) ((parameterLaw N p).prod P) := by
    simpa only [overlap,div_eq_mul_inv] using
      (((trajectory_stronglyMeasurable (NullAugmentation.driver D₀) β R hR (s+t)).inner
        (trajectory_stronglyMeasurable (NullAugmentation.driver D₀) β R hR s)).mul_const
          (N : ℝ)⁻¹).aestronglyMeasurable
  have hab : ∀ᵐ q ∂(parameterLaw N p).prod P,|overlap
      (trajectory (NullAugmentation.driver D₀) β R hR (s+t) q)
      (trajectory (NullAugmentation.driver D₀) β R hR s q)|≤1 := by
    filter_upwards [trajectory_onSphere hN D₀ β R hR hNR (s+t),trajectory_onSphere hN D₀ β R hR hNR s] with q hx hy
    exact overlap_abs_le_one hN hx hy
  exact ResponseTraceReplacement.weighted_trace_replacement n ha hab hb htrace htraceB

end SphericalAging.AnnealedResponseTraceReplacement
