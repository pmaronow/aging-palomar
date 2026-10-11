module

public import SphericalAging.ActualForkPastTraceCancellation

public section

/-! The entire common-past energy subtraction tends to zero in the
dimension limit. Its response and overlap estimates are genuine actual
model estimates, and require no late-time memory bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SphericalAging.ActualForkPastEnergyBound
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel
  HardSphereDynamics PhysicalForkDrivers ActualForkTraceFormula ActualForkEnergySubtraction
  ActualForkPastTraceCancellation ActualResponseFieldCongruence
  ActualFiniteHorizonTraceReplacement AnnealedHamiltonianEnergyStein
  AnnealedResponseMatrixContraction TwoTimeResponseTimeParameter ActualCompactJointOverlapVariance
open scoped NNReal ENNReal BigOperators InnerProductSpace Topology
variable {N p K : ℕ}

@[expose] def pastSubtractionField (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K)
    (U : WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N)
    (q : WaitingTime t×((Disorder N p×State N)×PathSeed N K)) : ℝ :=
  if (q.1:ℝ≥0)≤trunk then subtractionField β t trunk b U q else 0

theorem actual_past_integrated_trace_bound (hN : 3≤N) (hp : 2≤p) (hK : 0<K)
    (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K)
    (U : WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N)
    (hU : StronglyMeasurable U) (hUs : RepresentsPhysicalMatrix (by omega : 0<N) β t trunk b U) :
    Integrable (pastSubtractionField β t trunk b U) (integratedLaw N p K t) ∧
    (∫q,|pastSubtractionField β t trunk b U q| ∂integratedLaw N p K t)≤
      (t:ℝ)*((p-1:ℕ):ℝ)*Real.sqrt (4*jointVarianceCeiling p β (t+1)/(N:ℝ))*
        Real.sqrt (1+annealedFourthConstant p β t) := by
  have hn : 0<N := by omega
  have hs := (actual_energy_trace_formula_for hn hp (driver (N:=N) (K:=K) trunk b)
    β (N+1) (modelRadius_pos N) (modelRadius_sq N) t U hU hUs).1
  have hm := meanTraceField_integrable hn hp hK β t trunk b U hU hUs
  have hd : Integrable (subtractionField β t trunk b U) (integratedLaw N p K t) := by
    convert hs.sub hm using 1
    · funext q
      simp only [Pi.sub_apply,subtractionField,singleTraceField,meanTraceField,sub_mul]
    · rfl
  have hset : MeasurableSet {q : WaitingTime t×((Disorder N p×State N)×PathSeed N K) |
      (q.1:ℝ≥0)≤trunk} := measurableSet_le (measurable_subtype_coe.comp measurable_fst) measurable_const
  have hi : Integrable (pastSubtractionField β t trunk b U) (integratedLaw N p K t) := hd.indicator hset
  let B := ((p-1:ℕ):ℝ)*Real.sqrt (4*jointVarianceCeiling p β (t+1)/(N:ℝ))*
    Real.sqrt (1+annealedFourthConstant p β t)
  have hc (s : WaitingTime t) :
      (∫q,|pastSubtractionField β t trunk b U (s,q)|
        ∂(AnnealedModelLaw.parameterLaw N p).prod (pathSeedLaw N K))≤B := by
    by_cases hs : (s:ℝ≥0)≤trunk
    · simp only [pastSubtractionField,if_pos hs]
      exact actual_past_trace_abs_bound hN hp hK β t trunk b U hU hUs s hs
    · simp only [pastSubtractionField,if_neg hs,abs_zero,integral_zero]
      dsimp only [B]
      positivity
  refine ⟨hi,?_⟩
  have hin : Integrable (fun q => |pastSubtractionField β t trunk b U q|) (integratedLaw N p K t) :=
    by simpa only [Real.norm_eq_abs] using hi.norm
  unfold integratedLaw at hin ⊢
  rw [integral_prod _ hin]
  exact (integral_mono_ae hin.integral_prod_left (integrable_const B) (.of_forall hc)).trans_eq (by
    rw [integral_const,waitingMeasure_real_univ]
    simp only [smul_eq_mul,B]
    ring)

theorem actual_common_past_dimension_limit (hp : 2≤p) (hK : 0<K)
    (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K)
    (U : ∀n : ℕ,WaitingTime t×((Disorder (n+3) p×State (n+3))×PathSeed (n+3) K)→
      State (n+3)→L[ℝ] State (n+3))
    (hU : ∀n,StronglyMeasurable (U n))
    (hUs : ∀n,RepresentsPhysicalMatrix (by omega : 0<n+3) β t trunk b (U n)) :
    Tendsto (fun n : ℕ => ∫q,|pastSubtractionField β t trunk b (U n) q|
      ∂integratedLaw (n+3) p K t) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _)
    (fun n => (actual_past_integrated_trace_bound (by omega : 3≤n+3) hp hK
      β t trunk b (U n) (hU n) (hUs n)).2)
  have hh := ((tendsto_add_atTop_iff_nat 3).mpr
    (tendsto_const_div_atTop_nhds_zero_nat (4*jointVarianceCeiling p β (t+1)))).sqrt
  simpa only [Real.sqrt_zero,mul_zero,zero_mul] using
    (hh.const_mul ((t:ℝ)*((p-1:ℕ):ℝ))).mul_const (Real.sqrt (1+annealedFourthConstant p β t))

end SphericalAging.ActualForkPastEnergyBound
