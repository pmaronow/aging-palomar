module

public import SphericalAging.ActualBrownianResponseTraceContraction

public section

/-! The true compact-horizon Brownian Hessian rank error has an explicit
O(N^(-1/2)) mean integral ceiling, with its dimension limit proved. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualBrownianResponseRankLimit
open HardSphereDynamics FiniteModel ActualBrownianResponseCoefficientIntegral
  ActualBrownianResponseTraceContraction ActualFiniteHorizonTraceReplacement
  AnnealedResponseMatrixContraction AnnealedTwoTimeResponseMoments TwoTimeResponseParameter
  TwoTimeResponseTimeParameter ResponseMatrixEnergyContraction
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def brownianRankCeiling (p : ℕ) (β H S : ℝ≥0) (N : ℕ) : ℝ :=
  ((p : ℝ)*((p : ℝ)-1)^2*(H : ℝ)*Real.sqrt (1+annealedFourthConstant p β H)*Real.sqrt (S : ℝ)/Real.sqrt 2)/Real.sqrt N

 theorem actual_brownian_rank_error_integrable_ceiling (hN : 0<N) (hp : 3≤p)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H S : ℝ≥0)
    (U : WaitingTime H×Sample N p → (State N →L[ℝ] State N)) (hU : StronglyMeasurable U)
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[VectorBrownian.law N]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR
        r (H+1) (H-r) q hx)) :
    Integrable (brownianRankError β R hR H S U)
      ((waitingMeasure H).prod ((parameterLaw N p).prod (VectorBrownian.law N))) ∧
      (∫ q,|brownianRankError β R hR H S U q|
        ∂(waitingMeasure H).prod ((parameterLaw N p).prod (VectorBrownian.law N)))≤brownianRankCeiling p β H S N := by
  have hh := actual_brownian_rank_error_integrable_le hN hp β R hR hNR H S U hU hUs
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  have hr : 0<Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn
  rw [Real.sqrt_mul hn.le,Real.sqrt_mul hn.le]
  unfold brownianRankCeiling
  field_simp
  rw [Real.sq_sqrt hn.le]

 theorem brownianRankCeiling_tendsto_zero (p : ℕ) (β H S : ℝ≥0) :
    Tendsto (fun n : ℕ => brownianRankCeiling p β H S (n+3)) atTop (𝓝 0) := by
  have hc : Tendsto (fun n : ℕ => ((n+3 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_add_atTop_iff_nat 3).mpr tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun n : ℕ => Real.sqrt ((n+3 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hc
  exact tendsto_const_nhds.div_atTop hh

end SphericalAging.ActualBrownianResponseRankLimit
