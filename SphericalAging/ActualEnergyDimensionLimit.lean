module

public import SphericalAging.ActualAnnealedEnergyReplacement
public import Mathlib.Analysis.SpecificLimits.Basic

public section

/-! Actual-model energy dimension limit from the explicitly preceding
overlap concentration and primitive correlation/response convergence.
The finite-N energy identity, error estimate and response field are
constructed here, rather than supplied as conclusions. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualEnergyDimensionLimit
open HardSphereDynamics FiniteModel EnergyCovarianceContraction
open TwoTimeResponseParameter TwoTimeResponseTimeParameter ResponseMatrixEnergyContraction
open AnnealedTwoTimeResponseMoments AnnealedResponseMatrixContraction AnnealedResponseTimeMatrix
open ActualFiniteHorizonTraceReplacement ActualAnnealedEnergyReplacement
open AnnealedHamiltonianEnergyStein
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

@[expose] def modelMatrix {p : ℕ} (hp : 2≤p) (β H : ℝ≥0) (n : ℕ) :
    WaitingTime H × ((Disorder (n+1) p × State (n+1)) × VectorBrownian.Space (n+1)) →
      (State (n+1) →L[ℝ] State (n+1)) :=
  (exists_actual_fixedTerminal_matrix (by omega : 0<n+1) hp (VectorBrownian.driver (n+1)) β (((n+1 : ℕ) : ℝ≥0)+1)
    (modelRadius_pos (n+1)) (modelRadius_sq (n+1)) H).choose

lemma modelMatrix_spec {p : ℕ} (hp : 2≤p) (β H : ℝ≥0) (n : ℕ) :
    StronglyMeasurable (modelMatrix hp β H n) ∧
      (∀ s q (hx : OnSphere q.2),(fun ω => modelMatrix hp β H n (s,(q,ω))) =ᵐ[VectorBrownian.law (n+1)]
        sampleMatrix (physicalMatrix (by omega : n+1≠0) (VectorBrownian.driver (n+1)) β (((n+1 : ℕ) : ℝ≥0)+1)
          (modelRadius_pos (n+1)) (modelRadius_sq (n+1)) s (H+1) (H-s) q hx)) := by
  exact ⟨(exists_actual_fixedTerminal_matrix (by omega : 0<n+1) hp (VectorBrownian.driver (n+1)) β (((n+1 : ℕ) : ℝ≥0)+1)
    (modelRadius_pos (n+1)) (modelRadius_sq (n+1)) H).choose_spec.1,
    (exists_actual_fixedTerminal_matrix (by omega : 0<n+1) hp (VectorBrownian.driver (n+1)) β (((n+1 : ℕ) : ℝ≥0)+1)
    (modelRadius_pos (n+1)) (modelRadius_sq (n+1)) H).choose_spec.2.1⟩

@[expose] def modelCorrelation (p : ℕ) (β H : ℝ≥0) (n : ℕ) : WaitingTime H → ℝ :=
  actualCorrelation (p := p) (NullAugmentation.driver (VectorBrownian.driver (n+1))) β (((n+1 : ℕ) : ℝ≥0)+1)
    (modelRadius_pos (n+1)) H

@[expose] def modelResponse {p : ℕ} (hp : 2≤p) (β H : ℝ≥0) (n : ℕ) (s : WaitingTime H) : ℝ :=
  ∫ q,normalizedTrace (modelMatrix hp β H n (s,q)) ∂(parameterLaw (n+1) p).prod (VectorBrownian.law (n+1))

@[expose] def modelEnergy (p : ℕ) (β H : ℝ≥0) (n : ℕ) : ℝ :=
  (∫ q,Hamiltonian (n+1) p q.1.1 (modelProcess (n+1) p β H q) ∂AnnealedModelLaw.law (n+1) p)/((n+1 : ℕ) : ℝ)

@[expose] def modelPrimitive {p : ℕ} (hp : 2≤p) (β H : ℝ≥0) (n : ℕ) : ℝ :=
  ∫ s,(modelCorrelation p β H n s)^(p-1)*modelResponse hp β H n s ∂waitingMeasure H

lemma modelResponse_stronglyMeasurable {p : ℕ} (hp : 2≤p) (β H : ℝ≥0) (n : ℕ) :
    StronglyMeasurable (modelResponse hp β H n) :=
  (normalizedTrace_continuous.comp_stronglyMeasurable (modelMatrix_spec hp β H n).1).integral_prod_right'

lemma modelResponse_abs_le {p : ℕ} (hp : 2≤p) (β H : ℝ≥0) (n : ℕ) (s : WaitingTime H) :
    |modelResponse hp β H n s|≤Real.sqrt (1+annealedFourthConstant p β H) := by
  have hm := actual_trace_fourthMoments (by omega : 0<n+1) hp (VectorBrownian.driver (n+1)) β (((n+1 : ℕ) : ℝ≥0)+1)
    (modelRadius_pos (n+1)) (modelRadius_sq (n+1)) H (modelMatrix hp β H n)
    (modelMatrix_spec hp β H n).1 (modelMatrix_spec hp β H n).2 s
  have htwo := ResponseTraceReplacement.fourthMoment_to_secondMoment hm.1 hm.2
  exact abs_integral_le_integral_abs.trans
    ((ResponseMatrixEnergyContraction.integral_abs_le_sqrt_secondMoment htwo.1).trans (Real.sqrt_le_sqrt htwo.2))

lemma actual_expectedTrace_independent {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (hN : 0<N) (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0)
    (U V : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U) (hV : StronglyMeasurable V)
    (hUs : ∀ s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx))
    (hVs : ∀ s q (hx : OnSphere q.2),(fun ω => V (s,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx))
    (s : WaitingTime H) :
    (∫ q,normalizedTrace (U (s,q)) ∂(parameterLaw N p).prod P)=
      ∫ q,normalizedTrace (V (s,q)) ∂(parameterLaw N p).prod P := by
  have hu : StronglyMeasurable (fun q => U (s,q)) := hU.comp_measurable (measurable_const.prodMk measurable_id)
  have hv : StronglyMeasurable (fun q => V (s,q)) := hV.comp_measurable (measurable_const.prodMk measurable_id)
  apply integral_congr_ae
  have he : (fun q => U (s,q))=ᵐ[(parameterLaw N p).prod P] (fun q => V (s,q)) := by
    apply (Measure.ae_prod_iff_ae_ae (hu.measurableSet_eq_fun hv)).mpr
    filter_upwards [parameterLaw_onSphere (p := p) hN] with q hq
    exact (hUs s q hq).trans (hVs s q hq).symm
  exact he.mono (fun q hq => congrArg normalizedTrace hq)

theorem actual_model_finite_energy_error {p : ℕ} (hp : 2≤p) (β H : ℝ≥0)
    (n : ℕ) (ε : ℝ) (hε : 0≤ε)
    (hvariance : ∀ s,(∫ q,(overlapField (NullAugmentation.driver (VectorBrownian.driver (n+1))) β (((n+1 : ℕ) : ℝ≥0)+1)
        (modelRadius_pos (n+1)) H (s,q)-modelCorrelation p β H n s)^2
      ∂(parameterLaw (n+1) p).prod (VectorBrownian.law (n+1)))≤ε^2) :
    StronglyMeasurable (modelResponse hp β H n) ∧
      Integrable (fun s => (modelCorrelation p β H n s)^(p-1)*modelResponse hp β H n s) (waitingMeasure H) ∧
      |modelEnergy p β H n-(β : ℝ)*(p : ℝ)*modelPrimitive hp β H n|≤
        (β : ℝ)*(H : ℝ)*(Real.sqrt (((p : ℝ)^2*((p : ℝ)-1)^2/((n+1 : ℕ) : ℝ))*(1+annealedFourthConstant p β H))+
          (p : ℝ)*((p-1 : ℕ) : ℝ)*ε*Real.sqrt (1+annealedFourthConstant p β H)) := by
  obtain ⟨U,hU,hUs,hr,hi,herr⟩ := exists_actual_energy_correlation_response (by omega : 0<n+1) hp
    (VectorBrownian.driver (n+1)) β (((n+1 : ℕ) : ℝ≥0)+1) (modelRadius_pos (n+1)) (modelRadius_sq (n+1)) H ε hε hvariance
  have hs : (fun s => ∫ q,normalizedTrace (U (s,q)) ∂(parameterLaw (n+1) p).prod (VectorBrownian.law (n+1)))=
      modelResponse hp β H n := by
    funext s
    exact actual_expectedTrace_independent (by omega : 0<n+1) (VectorBrownian.driver (n+1)) β (((n+1 : ℕ) : ℝ≥0)+1)
      (modelRadius_pos (n+1)) (modelRadius_sq (n+1)) H U (modelMatrix hp β H n) hU (modelMatrix_spec hp β H n).1
      hUs (modelMatrix_spec hp β H n).2 s
  rw [hs] at hr
  have hh (s : WaitingTime H) : (∫ q,normalizedTrace (U (s,q)) ∂(parameterLaw (n+1) p).prod (VectorBrownian.law (n+1)))=
      modelResponse hp β H n s := congrFun hs s
  simp_rw [hh] at hi herr
  exact ⟨hr,hi,herr⟩

/-- Dimension-limit source energy formula for the actual model. The two
inputs are explicitly the preceding overlap variance decay and primitive
correlation/response convergence; the energy convergence is derived. -/
theorem actual_model_energy_limit {p : ℕ} (hp : 2≤p) (β H : ℝ≥0)
    (ε : ℕ → ℝ) (hε : ∀ n,0≤ε n) (hεlim : Tendsto ε atTop (nhds 0))
    (hvariance : ∀ n s,(∫ q,(overlapField (NullAugmentation.driver (VectorBrownian.driver (n+1))) β (((n+1 : ℕ) : ℝ≥0)+1)
        (modelRadius_pos (n+1)) H (s,q)-modelCorrelation p β H n s)^2
      ∂(parameterLaw (n+1) p).prod (VectorBrownian.law (n+1)))≤(ε n)^2)
    (L : ℝ) (hprimitive : Tendsto (modelPrimitive hp β H) atTop (nhds L)) :
    Tendsto (modelEnergy p β H) atTop (nhds ((β : ℝ)*(p : ℝ)*L)) := by
  let K := (p : ℝ)^2*((p : ℝ)-1)^2*(1+annealedFourthConstant p β H)
  have hsmall : Tendsto (fun n : ℕ => K/((n+1 : ℕ) : ℝ)) atTop (nhds 0) := by
    convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul K using 1 <;> simp [Nat.cast_add,Nat.cast_one]
    funext n
    ring
  have hsqrt := hsmall.sqrt
  have hB : Tendsto (fun n => (β : ℝ)*(H : ℝ)*(Real.sqrt (K/((n+1 : ℕ) : ℝ))+
      (p : ℝ)*((p-1 : ℕ) : ℝ)*ε n*Real.sqrt (1+annealedFourthConstant p β H))) atTop (nhds 0) := by
    convert (hsqrt.add ((hεlim.const_mul ((p : ℝ)*((p-1 : ℕ) : ℝ))).mul_const
      (Real.sqrt (1+annealedFourthConstant p β H)))).const_mul ((β : ℝ)*(H : ℝ)) using 1 <;> simp
  have hbound : ∀ n,|modelEnergy p β H n-(β : ℝ)*(p : ℝ)*modelPrimitive hp β H n|≤
      (β : ℝ)*(H : ℝ)*(Real.sqrt (K/((n+1 : ℕ) : ℝ))+
        (p : ℝ)*((p-1 : ℕ) : ℝ)*ε n*Real.sqrt (1+annealedFourthConstant p β H)) := by
    intro n
    convert (actual_model_finite_energy_error hp β H n (ε n) (hε n) (hvariance n)).2.2 using 1
    simp only [K]
    ring_nf
  have hdiff : Tendsto (fun n => modelEnergy p β H n-(β : ℝ)*(p : ℝ)*modelPrimitive hp β H n) atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact squeeze_zero' (.of_forall (fun _ => abs_nonneg _)) (.of_forall hbound) hB
  have hh := hdiff.add (hprimitive.const_mul ((β : ℝ)*(p : ℝ)))
  simpa only [sub_add_cancel,zero_add] using hh

/-- Pointwise convergence of the actual C/R primitives on a fixed
finite horizon implies the primitive integral limit by actual response
moments and dominated convergence. No energy-limit premise is used. -/
theorem actual_model_energy_limit_of_pointwise_CR {p : ℕ} (hp : 2≤p) (β H : ℝ≥0)
    (ε : ℕ → ℝ) (hε : ∀ n,0≤ε n) (hεlim : Tendsto ε atTop (nhds 0))
    (hvariance : ∀ n s,(∫ q,(overlapField (NullAugmentation.driver (VectorBrownian.driver (n+1))) β (((n+1 : ℕ) : ℝ≥0)+1)
        (modelRadius_pos (n+1)) H (s,q)-modelCorrelation p β H n s)^2
      ∂(parameterLaw (n+1) p).prod (VectorBrownian.law (n+1)))≤(ε n)^2)
    (C R : WaitingTime H → ℝ)
    (hC : ∀ s,Tendsto (fun n => modelCorrelation p β H n s) atTop (nhds (C s)))
    (hR : ∀ s,Tendsto (fun n => modelResponse hp β H n s) atTop (nhds (R s))) :
    Tendsto (modelEnergy p β H) atTop
      (nhds ((β : ℝ)*(p : ℝ)*(∫ s,(C s)^(p-1)*R s ∂waitingMeasure H))) := by
  apply actual_model_energy_limit hp β H ε hε hεlim hvariance
  apply tendsto_integral_of_dominated_convergence (fun _ : WaitingTime H => Real.sqrt (1+annealedFourthConstant p β H))
  · intro n
    exact ((actualCorrelation_stronglyMeasurable (p := p) (NullAugmentation.driver (VectorBrownian.driver (n+1))) β
      (((n+1 : ℕ) : ℝ≥0)+1) (modelRadius_pos (n+1)) H).pow (p-1)).mul (modelResponse_stronglyMeasurable hp β H n) |>.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact .of_forall (fun s => by
      rw [Real.norm_eq_abs,abs_mul,abs_pow]
      exact (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _)
        (actualCorrelation_abs_le_one (by omega : 0<n+1) (VectorBrownian.driver (n+1)) β (((n+1 : ℕ) : ℝ≥0)+1)
          (modelRadius_pos (n+1)) (modelRadius_sq (n+1)) H s))).trans (modelResponse_abs_le hp β H n s))
  · exact .of_forall (fun s => ((hC s).pow (p-1)).mul (hR s))

end SphericalAging.ActualEnergyDimensionLimit
