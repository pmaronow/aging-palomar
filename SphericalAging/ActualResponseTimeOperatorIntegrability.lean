module

public import SphericalAging.ActualFiniteHorizonTraceReplacement

public section

/-! Finite-N integrability of the genuine joint physical response sample
operator. It follows from actual column L⁴ moments; no dimension-uniform
sample operator norm bound is asserted or assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualResponseTimeOperatorIntegrability
open HardSphereDynamics FiniteModel TwoTimeResponseParameter TwoTimeResponseTimeParameter
open ResponseMatrixEnergyContraction AnnealedTwoTimeResponseMoments
open AnnealedResponseTimeMoments AnnealedResponseTimeMatrix ActualFiniteHorizonTraceReplacement
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma norm_operator_le_sum_basis (U : State N →L[ℝ] State N) :
    ‖U‖≤∑ i : Fin N,‖U (basisVector i)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound U (by positivity)
  intro v
  conv_lhs => rw [← LocalSDE.state_sum_basis v,map_sum]
  simp only [map_smul]
  calc
    _ ≤ ∑ i : Fin N,‖v i • U (basisVector i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin N,‖v‖*‖U (basisVector i)‖ := Finset.sum_le_sum (fun i _ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v i) (norm_nonneg _))
    _ = _ := by rw [← Finset.mul_sum];ring

private lemma joint_column_integrable {H : ℝ≥0}
    {G : WaitingTime H × ((Disorder N p × State N) × Ω) → State N} {C : ℝ}
    (hG : StronglyMeasurable G)
    (hm : ∀ s,MemLp (fun q => G (s,q)) 4 ((parameterLaw N p).prod P))
    (hC : ∀ s,(∫ q,‖G (s,q)‖^4 ∂(parameterLaw N p).prod P)≤C) :
    Integrable (fun q => ‖G q‖) ((waitingMeasure H).prod ((parameterLaw N p).prod P)) := by
  have hF : Integrable (fun s => ∫ q,‖G (s,q)‖^4 ∂(parameterLaw N p).prod P) (waitingMeasure H) :=
    (integrable_const C).mono' (hG.norm.pow 4).integral_prod_right'.aestronglyMeasurable
      (.of_forall (fun s => by
        rw [Real.norm_of_nonneg (integral_nonneg (fun _ => by positivity))]
        exact hC s))
  have hi : Integrable (fun q => ‖G q‖^4) ((waitingMeasure H).prod ((parameterLaw N p).prod P)) := by
    apply (integrable_prod_iff (hG.norm.pow 4).aestronglyMeasurable).mpr
    refine ⟨.of_forall (fun s => (hm s).integrable_norm_pow'),?_⟩
    convert hF using 1
    funext s
    exact integral_congr_ae (.of_forall (fun q => Real.norm_of_nonneg (pow_nonneg (norm_nonneg (G (s,q))) 4)))
  have h4 : MemLp G 4 ((waitingMeasure H).prod ((parameterLaw N p).prod P)) := by
    apply (integrable_norm_rpow_iff hG.aestronglyMeasurable
      (by norm_num : (4 : ℝ≥0∞)≠0) (by norm_num : (4 : ℝ≥0∞)≠∞)).mp
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using hi
  exact ((h4.mono_exponent (by norm_num : (1 : ℝ≥0∞)≤4)).integrable le_rfl).norm

theorem actual_matrix_operator_integrable (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U)
    (hUs : ∀ s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx)) :
    Integrable (fun q => ‖U q‖) ((waitingMeasure H).prod ((parameterLaw N p).prod P)) := by
  let ν := (waitingMeasure H).prod ((parameterLaw N p).prod P)
  have hcolumn (i : Fin N) : Integrable (fun q => ‖U q (basisVector i)‖) ν := by
    obtain ⟨G,hG,hGV,hGM⟩ := exists_fixedTerminalColumn_joint_L4 hN hp D₀ β R hR hNR H (basisVector i)
    have hGi := joint_column_integrable hG (fun s => (hGM s).1) (fun s => (hGM s).2)
    have hcol : StronglyMeasurable (fun q => U q (basisVector i)) :=
      (ContinuousLinearMap.apply ℝ (State N) (basisVector i)).continuous.comp_stronglyMeasurable hU
    have he : (fun q => U q (basisVector i))=ᵐ[ν] G := by
      apply (Measure.ae_prod_iff_ae_ae (hcol.measurableSet_eq_fun hG)).mpr
      exact .of_forall (fun s => by
        have hscol : StronglyMeasurable (fun q => U (s,q) (basisVector i)) :=
          hcol.comp_measurable (measurable_const.prodMk measurable_id)
        have hsG : StronglyMeasurable (fun q => G (s,q)) := hG.comp_measurable (measurable_const.prodMk measurable_id)
        apply (Measure.ae_prod_iff_ae_ae (hscol.measurableSet_eq_fun hsG)).mpr
        filter_upwards [parameterLaw_onSphere (p := p) hN] with q hq
        filter_upwards [hUs s q hq,hGV s q] with ω hu hg
        rw [hu,sampleMatrix_basis]
        have heq : fixedTerminalColumn (Nat.ne_of_gt hN) D₀ β R hR hNR H (basisVector i) s q=
            physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hq (basisVector i) := by
          simp only [fixedTerminalColumn,dif_pos hq]
        rw [heq] at hg
        exact hg.symm)
    have he' : (fun q => ‖G q‖)=ᵐ[ν] (fun q => ‖U q (basisVector i)‖) :=
      Filter.EventuallyEq.symm (he.mono (fun q hq => congrArg norm hq))
    exact hGi.congr he'
  have hsum : Integrable (fun q => ∑ i : Fin N,‖U q (basisVector i)‖) ν :=
    integrable_finsetSum Finset.univ (fun i _ => hcolumn i)
  apply hsum.mono' hU.norm.aestronglyMeasurable
  exact .of_forall (fun q => by
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact norm_operator_le_sum_basis (U q))

theorem exists_actual_matrix_operator_integrable (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0) :
    ∃ U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N),StronglyMeasurable U ∧
      (∀ s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω))) =ᵐ[P]
        sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx)) ∧
      Integrable (fun q => ‖U q‖) ((waitingMeasure H).prod ((parameterLaw N p).prod P)) := by
  obtain ⟨U,hU,hUs,_⟩ := exists_actual_fixedTerminal_matrix hN hp D₀ β R hR hNR H
  exact ⟨U,hU,hUs,actual_matrix_operator_integrable hN hp D₀ β R hR hNR H U hU hUs⟩

end SphericalAging.ActualResponseTimeOperatorIntegrability
