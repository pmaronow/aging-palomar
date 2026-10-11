module

public import SphericalAging.ActualEnergyDimensionLimit
public import SphericalAging.WeightedPrimitiveConvergence

public section

/-! Full local fixed-horizon energy identity, conditional only on the
preceding actual hard-sphere overlap concentration and signed response
primitive convergence. The actual finite-N identity, total variation
bound, weighted primitive passage and multiplier clause are derived. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualEnergyUniformBridge
open HardSphereDynamics FiniteModel EnergyCovarianceContraction
open TwoTimeResponseTimeParameter AnnealedTwoTimeResponseMoments AnnealedResponseMatrixContraction
open ActualFiniteHorizonTraceReplacement ActualResponseCoefficientIntegral ActualAnnealedEnergyReplacement
open ActualEnergyDimensionLimit AnnealedHamiltonianEnergyStein AnnealedResponseTimeMoments
open WeightedPrimitiveConvergence FourPapersCommon
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

@[expose] def responseRow {p : ℕ} (hp : 2≤p) (β : ℝ≥0) (n : ℕ) (t u : ℝ) : ℝ := by
  classical
  exact if ht : 0≤t then
    if hu : u∈Icc 0 t then modelResponse hp β ⟨t,ht⟩ n
      ⟨⟨u,hu.1⟩,⟨zero_le,hu.2⟩⟩ else 0 else 0

lemma responseRow_on_clock {p : ℕ} (hp : 2≤p) (β H : ℝ≥0) (n : ℕ) (s : WaitingTime H) :
    responseRow hp β n H s=modelResponse hp β H n s := by
  have hs : (s : ℝ≥0)≤H := s.property.2
  simp only [responseRow,dif_pos H.coe_nonneg,
    dif_pos (show (s : ℝ)∈Icc 0 (H : ℝ) from ⟨s.val.coe_nonneg,hs⟩)]
  rfl

lemma waiting_real_map (H : ℝ≥0) :
    (waitingMeasure H).map (fun s : WaitingTime H => (s : ℝ))=volume.restrict (Ioc 0 (H : ℝ)) := by
  have hs : (waitingMeasure H).map Subtype.val=nonnegativeLebesgueMeasure.restrict (Ioc 0 H) := by
    rw [waitingMeasure,map_comap_subtype_coe measurableSet_Icc,
      Measure.restrict_restrict measurableSet_Icc,inter_eq_right.mpr Ioc_subset_Icc_self]
  have he : (fun s : WaitingTime H => (s : ℝ))=((↑) : ℝ≥0 → ℝ) ∘ Subtype.val := rfl
  rw [he,← Measure.map_map NNReal.continuous_coe.measurable measurable_subtype_coe,hs]
  exact map_nonnegativeLebesgueMeasure_restrict_Ioc H

lemma waiting_real_embedding (H : ℝ≥0) : MeasurableEmbedding (fun s : WaitingTime H => (s : ℝ)) :=
  measurableEmbedding_nnrealCoe_iterated.comp (MeasurableEmbedding.subtype_coe measurableSet_Icc)

lemma waiting_real_integral (H : ℝ≥0) (f : ℝ → ℝ) :
    (∫ s : WaitingTime H,f s ∂waitingMeasure H)=∫ u in (0 : ℝ)..(H : ℝ),f u := by
  rw [intervalIntegral.integral_of_le H.coe_nonneg,← waiting_real_map H]
  exact (waiting_real_embedding H).integral_map f |>.symm

lemma responseRow_integrable {p : ℕ} (hp : 2≤p) (β : ℝ≥0) (n : ℕ) {t : ℝ} (ht : 0≤t) :
    IntervalIntegrable (responseRow hp β n t) volume 0 t := by
  let H := t.toNNReal
  have hc : (H : ℝ)=t := Real.coe_toNNReal _ ht
  have hri : Integrable (modelResponse hp β H n) (waitingMeasure H) :=
    (integrable_const (Real.sqrt (1+annealedFourthConstant p β H))).mono'
      (modelResponse_stronglyMeasurable hp β H n).aestronglyMeasurable
      (.of_forall (fun s => by rw [Real.norm_eq_abs];exact modelResponse_abs_le hp β H n s))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht,IntegrableOn,← hc,← waiting_real_map H]
  apply (waiting_real_embedding H).integrable_map_iff.mpr
  convert hri using 1
  funext s
  exact responseRow_on_clock hp β H n s

lemma responseRow_variation {p : ℕ} (hp : 2≤p) (β T : ℝ≥0) (n : ℕ) {t : ℝ} (ht : t∈Icc 0 (T : ℝ)) :
    (∫ u in (0 : ℝ)..t,|responseRow hp β n t u|)≤(T : ℝ)*Real.sqrt (1+annealedFourthConstant p β T) := by
  let H := t.toNNReal
  have hc : (H : ℝ)=t := Real.coe_toNNReal _ ht.1
  have hHT : H≤T := by exact_mod_cast (show (H : ℝ)≤T by rw [hc];exact ht.2)
  have hsqrt := Real.sqrt_le_sqrt (add_le_add_right (annealedFourthConstant_mono p β hHT) 1)
  have hi : Integrable (fun s : WaitingTime H => |modelResponse hp β H n s|) (waitingMeasure H) :=
    (integrable_const (Real.sqrt (1+annealedFourthConstant p β H))).mono'
      (modelResponse_stronglyMeasurable hp β H n).norm.aestronglyMeasurable
      (.of_forall (fun s => by rw [Real.norm_eq_abs,abs_abs];exact modelResponse_abs_le hp β H n s))
  rw [← hc,← waiting_real_integral]
  have he : (fun s : WaitingTime H => |responseRow hp β n H s|)=fun s => |modelResponse hp β H n s| :=
    funext (fun s => congrArg abs (responseRow_on_clock hp β H n s))
  rw [he]
  calc
    _ ≤ ∫ _ : WaitingTime H,Real.sqrt (1+annealedFourthConstant p β H) ∂waitingMeasure H :=
      integral_mono_ae hi (integrable_const _) (.of_forall (fun s => modelResponse_abs_le hp β H n s))
    _ = (H : ℝ)*Real.sqrt (1+annealedFourthConstant p β H) := by rw [integral_const,waitingMeasure_real_univ];rfl
    _ ≤ _ := mul_le_mul hHT hsqrt (Real.sqrt_nonneg _) T.coe_nonneg

theorem actual_model_CK_weight_error {p : ℕ} (hp : 2≤p) (β H : ℝ≥0) (n : ℕ)
    (d : CKSpecification.CKData) (h : CKSpecification.CKEquations p β d)
    (ε : ℝ) (hε : 0≤ε)
    (hvariance : ∀ s,(∫ q,(overlapField (NullAugmentation.driver (VectorBrownian.driver (n+1))) β
        (((n+1 : ℕ) : ℝ≥0)+1) (modelRadius_pos (n+1)) H (s,q)-d.C H s)^2
      ∂(parameterLaw (n+1) p).prod (VectorBrownian.law (n+1)))≤ε^2) :
    |modelEnergy p β H n-(β : ℝ)*(p : ℝ)*(∫ u in (0 : ℝ)..H,(d.C H u)^(p-1)*responseRow hp β n H u)|≤
      (β : ℝ)*(H : ℝ)*(Real.sqrt (((p : ℝ)^2*((p : ℝ)-1)^2/((n+1 : ℕ) : ℝ))*(1+annealedFourthConstant p β H))+
        (p : ℝ)*((p-1 : ℕ) : ℝ)*ε*Real.sqrt (1+annealedFourthConstant p β H)) := by
  have hb : StronglyMeasurable (fun s : WaitingTime H => d.C H s) := by
    apply Continuous.stronglyMeasurable
    apply continuousOn_univ.mp
    exact h.correlation_continuous.comp
      (continuous_const.prodMk (NNReal.continuous_coe.comp continuous_subtype_val)).continuousOn
      (fun s _ => ⟨H.coe_nonneg,s.val.coe_nonneg⟩)
  have hbb (s : WaitingTime H) : |d.C H s|≤1 := by
    have hh := (CKPhysicalConsequences.physical_bounds_of_equations h).1 H s H.coe_nonneg s.val.coe_nonneg
    rw [abs_of_nonneg hh.1]
    exact hh.2
  obtain ⟨U,hU,hUs,hr,hi,herr⟩ := exists_actual_energy_weight_replacement (by omega : 0<n+1) hp
    (VectorBrownian.driver (n+1)) β (((n+1 : ℕ) : ℝ≥0)+1) (modelRadius_pos (n+1)) (modelRadius_sq (n+1)) H
    (fun s => d.C H s) hb hbb ε hε hvariance
  have hs (s : WaitingTime H) : (∫ q,normalizedTrace (U (s,q)) ∂(parameterLaw (n+1) p).prod (VectorBrownian.law (n+1)))=
      modelResponse hp β H n s :=
    actual_expectedTrace_independent (by omega : 0<n+1) (VectorBrownian.driver (n+1)) β (((n+1 : ℕ) : ℝ≥0)+1)
      (modelRadius_pos (n+1)) (modelRadius_sq (n+1)) H U (modelMatrix hp β H n) hU (modelMatrix_spec hp β H n).1
      hUs (modelMatrix_spec hp β H n).2 s
  simp_rw [hs] at herr
  have he : (∫ s : WaitingTime H,(d.C H s)^(p-1)*modelResponse hp β H n s ∂waitingMeasure H)=
      ∫ u in (0 : ℝ)..H,(d.C H u)^(p-1)*responseRow hp β n H u := by
    rw [← waiting_real_integral]
    apply integral_congr_ae
    exact .of_forall (fun s => congrArg (fun r : ℝ => (d.C H s)^(p-1)*r) (responseRow_on_clock hp β H n s).symm)
  rw [he] at herr
  exact herr

/-- Uniform-on-a-fixed-horizon actual energy identity from the preceding
hard-sphere overlap concentration and signed response primitive limit.
The response rows and their total variation bound are genuine model
objects derived above. -/
theorem actual_model_energy_uniform_limit {p : ℕ} (hp : 2≤p) (β T : ℝ≥0)
    (d : CKSpecification.CKData) (h : CKSpecification.CKEquations p β d)
    (ε : ℕ → ℝ) (hε : ∀ n,0≤ε n) (hεlim : Tendsto ε atTop (nhds 0))
    (hvariance : ∀ n H,H≤T → ∀ s,(∫ q,(overlapField (NullAugmentation.driver (VectorBrownian.driver (n+1))) β
        (((n+1 : ℕ) : ℝ≥0)+1) (modelRadius_pos (n+1)) H (s,q)-d.C H s)^2
      ∂(parameterLaw (n+1) p).prod (VectorBrownian.law (n+1)))≤(ε n)^2)
    (hprimitive : TendstoUniformlyOn
      (fun n (q : ℝ × ℝ) => ∫ u in (0 : ℝ)..q.2,responseRow hp β n q.1 u-d.R q.1 u)
      (fun _ => 0) atTop (compactTriangle T)) :
    TendstoUniformlyOn (fun n t => modelEnergy p β t.toNNReal n)
      (CKSpecification.energy p β d) atTop (Icc 0 (T : ℝ)) := by
  let A := annealedFourthConstant p β T
  let K := (p : ℝ)^2*((p : ℝ)-1)^2*(1+A)
  let B := fun n : ℕ => (β : ℝ)*(T : ℝ)*(Real.sqrt (K/((n+1 : ℕ) : ℝ))+
    (p : ℝ)*((p-1 : ℕ) : ℝ)*ε n*Real.sqrt (1+A))
  have hbound (n : ℕ) (t : ℝ) (ht : t∈Icc 0 (T : ℝ)) :
      |modelEnergy p β t.toNNReal n-(β : ℝ)*(p : ℝ)*(∫ u in (0 : ℝ)..t,(d.C t u)^(p-1)*responseRow hp β n t u)|≤B n := by
    let H := t.toNNReal
    have hc : (H : ℝ)=t := Real.coe_toNNReal _ ht.1
    have hHT : H≤T := by exact_mod_cast (show (H : ℝ)≤T by rw [hc];exact ht.2)
    have hh := actual_model_CK_weight_error hp β H n d h (ε n) (hε n) (hvariance n H hHT)
    have hle : (β : ℝ)*(H : ℝ)*(Real.sqrt (((p : ℝ)^2*((p : ℝ)-1)^2/((n+1 : ℕ) : ℝ))*(1+annealedFourthConstant p β H))+
        (p : ℝ)*((p-1 : ℕ) : ℝ)*ε n*Real.sqrt (1+annealedFourthConstant p β H))≤B n := by
      dsimp only [B,K,A]
      have hC := annealedFourthConstant_mono p β hHT
      have hNr : 0<((n+1 : ℕ) : ℝ) := by positivity
      have hnε := hε n
      rw [div_mul_eq_mul_div]
      gcongr
      all_goals positivity
    rw [hc] at hh hle
    exact hh.trans hle
  have hsmall : Tendsto (fun n : ℕ => K/((n+1 : ℕ) : ℝ)) atTop (nhds 0) := by
    convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul K using 1 <;> simp [Nat.cast_add,Nat.cast_one]
    funext n
    ring
  have hB : Tendsto B atTop (nhds 0) := by
    convert (hsmall.sqrt.add ((hεlim.const_mul ((p : ℝ)*((p-1 : ℕ) : ℝ))).mul_const
      (Real.sqrt (1+A)))).const_mul ((β : ℝ)*(T : ℝ)) using 1 <;> simp [B]
  have hweighted := ck_weighted_response_limit h T.coe_nonneg
    (by positivity : 0≤(T : ℝ)*Real.sqrt (1+A)) (responseRow hp β)
    (fun n t ht => responseRow_integrable hp β n ht.1)
    (fun n t ht => responseRow_variation hp β T n ht) hprimitive
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro δ hδ
  let η := δ/(2*((β : ℝ)*(p : ℝ)+1))
  have hη : 0<η := by dsimp [η];positivity
  filter_upwards [(tendsto_order.1 hB).2 (δ/2) (by positivity),
    (Metric.tendstoUniformlyOn_iff.mp hweighted) η hη] with n hnB hnW
  intro t ht
  have hCcont : ContinuousOn (fun u => (d.C t u)^(p-1)) (Icc 0 t) :=
    (h.correlation_continuous.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu => ⟨ht.1,hu.1⟩)).pow (p-1)
  have hRcont : ContinuousOn (fun u => d.R t u) (Icc 0 t) :=
    h.response_continuous.comp (continuous_const.prodMk continuous_id).continuousOn (fun u hu => ⟨hu.1,hu.2⟩)
  have hwr := (responseRow_integrable hp β n ht.1).continuousOn_mul (by simpa only [uIcc_of_le ht.1] using hCcont)
  have hWR : IntervalIntegrable (fun u => (d.C t u)^(p-1)*d.R t u) volume 0 t :=
    (hCcont.mul hRcont).intervalIntegrable_of_Icc ht.1
  have hid : (β : ℝ)*(p : ℝ)*(∫ u in (0 : ℝ)..t,(d.C t u)^(p-1)*responseRow hp β n t u)-CKSpecification.energy p β d t=
      (β : ℝ)*(p : ℝ)*(∫ u in (0 : ℝ)..t,(d.C t u)^(p-1)*(responseRow hp β n t u-d.R t u)) := by
    rw [CKSpecification.energy,CKSpecification.memoryMass,← mul_sub,← intervalIntegral.integral_sub hwr hWR]
    congr 1
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    ring
  have hwsmall : |∫ u in (0 : ℝ)..t,(d.C t u)^(p-1)*(responseRow hp β n t u-d.R t u)|<η := by
    simpa only [Real.dist_eq,zero_sub,abs_neg,sub_zero] using hnW t ht
  have hcoef : (β : ℝ)*(p : ℝ)*η<δ/2 := by
    have hden : 0<2*((β : ℝ)*(p : ℝ)+1) := by positivity
    dsimp [η]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hfinal : |modelEnergy p β t.toNNReal n-CKSpecification.energy p β d t|<δ := by
    calc
      _ ≤ |modelEnergy p β t.toNNReal n-(β : ℝ)*(p : ℝ)*(∫ u in (0 : ℝ)..t,(d.C t u)^(p-1)*responseRow hp β n t u)|+
          |(β : ℝ)*(p : ℝ)*(∫ u in (0 : ℝ)..t,(d.C t u)^(p-1)*responseRow hp β n t u)-CKSpecification.energy p β d t| := abs_sub_le _ _ _
      _ ≤ B n+(β : ℝ)*(p : ℝ)*η := by
        apply add_le_add (hbound n t ht)
        rw [hid,abs_mul,abs_of_nonneg (by positivity : 0≤(β : ℝ)*(p : ℝ))]
        exact mul_le_mul_of_nonneg_left hwsmall.le (by positivity)
      _ < δ := by linarith
  simpa only [Real.dist_eq,abs_sub_comm] using hfinal

/-- Complete local Proposition 4.1. Its hypotheses identify the actual
preceding finite-N overlap convergence and signed response primitives;
they contain no energy identity or energy convergence conclusion. -/
theorem proposition_4_1 {p : ℕ} (β : ℝ≥0) (d : CKSpecification.CKData)
    (h : CKSpecification.CKEquations p β d)
    (hpreceding : ∀ T : ℝ≥0,∃ ε : ℕ → ℝ,(∀ n,0≤ε n) ∧ Tendsto ε atTop (nhds 0) ∧
      ∀ n H,H≤T → ∀ s,(∫ q,(overlapField (NullAugmentation.driver (VectorBrownian.driver (n+1))) β
        (((n+1 : ℕ) : ℝ≥0)+1) (modelRadius_pos (n+1)) H (s,q)-d.C H s)^2
        ∂(parameterLaw (n+1) p).prod (VectorBrownian.law (n+1)))≤(ε n)^2)
    (hprimitive : ∀ T : ℝ≥0,TendstoUniformlyOn
      (fun n (q : ℝ × ℝ) => ∫ u in (0 : ℝ)..q.2,responseRow (by have := h.spin_ge_three;omega : 2≤p) β n q.1 u-d.R q.1 u)
      (fun _ => 0) atTop (compactTriangle T)) :
    (∀ T : ℝ≥0,TendstoUniformlyOn (fun n t => modelEnergy p β t.toNNReal n)
      (fun t => (β : ℝ)*(p : ℝ)*(∫ u in (0 : ℝ)..t,(d.C t u)^(p-1)*d.R t u)) atTop (Icc 0 (T : ℝ))) ∧
      (∀ t : ℝ,0≤t → d.multiplier t=1+(p : ℝ)*(β : ℝ)*CKSpecification.energy p β d t) := by
  have hp : 2≤p := by have := h.spin_ge_three;omega
  refine ⟨?_,fun t ht => CKSpecification.multiplier_energy_identity h t ht⟩
  intro T
  obtain ⟨ε,hε,hεlim,hvar⟩ := hpreceding T
  exact actual_model_energy_uniform_limit hp β T d h ε hε hεlim hvar (hprimitive T)

lemma actual_overlap_secondMoment_le_twice_abs {p : ℕ} (β H : ℝ≥0) (n : ℕ)
    (b : WaitingTime H → ℝ) (hbb : ∀ s,|b s|≤1) (s : WaitingTime H) :
    (∫ q,(overlapField (NullAugmentation.driver (VectorBrownian.driver (n+1))) β
        (((n+1 : ℕ) : ℝ≥0)+1) (modelRadius_pos (n+1)) H (s,q)-b s)^2
      ∂(parameterLaw (n+1) p).prod (VectorBrownian.law (n+1)))≤
      2*(∫ q,|overlapField (NullAugmentation.driver (VectorBrownian.driver (n+1))) β
        (((n+1 : ℕ) : ℝ≥0)+1) (modelRadius_pos (n+1)) H (s,q)-b s|
      ∂(parameterLaw (n+1) p).prod (VectorBrownian.law (n+1))) := by
  let μ := (parameterLaw (n+1) p).prod (VectorBrownian.law (n+1))
  let a := fun q => overlapField (p := p) (NullAugmentation.driver (VectorBrownian.driver (n+1))) β
    (((n+1 : ℕ) : ℝ≥0)+1) (modelRadius_pos (n+1)) H (s,q)-b s
  have hm : StronglyMeasurable a :=
    ((overlapField_stronglyMeasurable (p := p) (NullAugmentation.driver (VectorBrownian.driver (n+1))) β
      (((n+1 : ℕ) : ℝ≥0)+1) (modelRadius_pos (n+1)) H).comp_measurable
      (measurable_const.prodMk measurable_id)).sub stronglyMeasurable_const
  have hab : ∀ᵐ q ∂μ,|a q|≤2 := by
    filter_upwards [trajectory_onSphere (by omega : 0<n+1) (VectorBrownian.driver (n+1)) β
      (((n+1 : ℕ) : ℝ≥0)+1) (modelRadius_pos (n+1)) (modelRadius_sq (n+1)) H,
      trajectory_onSphere (by omega : 0<n+1) (VectorBrownian.driver (n+1)) β
      (((n+1 : ℕ) : ℝ≥0)+1) (modelRadius_pos (n+1)) (modelRadius_sq (n+1)) s] with q hx hy
    exact (abs_sub _ _).trans ((add_le_add (FiniteCorrelationIto.overlap_abs_le_one (by omega : 0<n+1) hx hy)
      (hbb s)).trans_eq (by norm_num))
  have hmp : MemLp a 2 μ := MemLp.of_bound hm.aestronglyMeasurable 2 (by simpa only [Real.norm_eq_abs] using hab)
  have hi : Integrable (fun q => |a q|) μ := by
    simpa only [Real.norm_eq_abs] using (hmp.integrable (by norm_num)).norm
  change (∫ q,(a q)^2 ∂μ)≤2*(∫ q,|a q| ∂μ)
  rw [← integral_const_mul]
  apply integral_mono_ae hmp.integrable_sq (hi.const_mul 2)
  filter_upwards [hab] with q hq
  nlinarith [abs_nonneg (a q),sq_abs (a q)]

@[expose] def ActualOverlapL1Convergence (p : ℕ) (β : ℝ≥0) (d : CKSpecification.CKData) : Prop :=
  ∀ T : ℝ≥0,∃ δ : ℕ → ℝ,(∀ n,0≤δ n) ∧ Tendsto δ atTop (nhds 0) ∧
    ∀ n H,H≤T → ∀ s,(∫ q,|overlapField (NullAugmentation.driver (VectorBrownian.driver (n+1))) β
      (((n+1 : ℕ) : ℝ≥0)+1) (modelRadius_pos (n+1)) H (s,q)-d.C H s|
      ∂(parameterLaw (n+1) p).prod (VectorBrownian.law (n+1)))≤δ n

@[expose] def ActualTracePrimitiveConvergence {p : ℕ} (hp : 2≤p) (β : ℝ≥0) (d : CKSpecification.CKData) : Prop :=
  ∀ T : ℝ≥0,TendstoUniformlyOn
    (fun n (q : ℝ × ℝ) => ∫ u in q.2..q.1,responseRow hp β n q.1 u-d.R q.1 u)
    (fun _ => 0) atTop (compactTriangle T)

/-- The exact printed preceding L¹ overlap and tail-response primitives
suffice for all clauses of the local fixed-horizon Proposition 4.1. -/
theorem proposition_4_1_from_preceding_bridges {p : ℕ} (β : ℝ≥0) (d : CKSpecification.CKData)
    (h : CKSpecification.CKEquations p β d)
    (hOverlap : ActualOverlapL1Convergence p β d)
    (hTrace : ActualTracePrimitiveConvergence (by have := h.spin_ge_three;omega : 2≤p) β d) :
    (∀ T : ℝ≥0,TendstoUniformlyOn (fun n t => modelEnergy p β t.toNNReal n)
      (fun t => (β : ℝ)*(p : ℝ)*(∫ u in (0 : ℝ)..t,(d.C t u)^(p-1)*d.R t u)) atTop (Icc 0 (T : ℝ))) ∧
      (∀ t : ℝ,0≤t → d.multiplier t=1+(p : ℝ)*(β : ℝ)*CKSpecification.energy p β d t) := by
  apply proposition_4_1 β d h
  · intro T
    obtain ⟨δ,hδ,hδlim,hL1⟩ := hOverlap T
    refine ⟨fun n => Real.sqrt (2*δ n),fun _ => Real.sqrt_nonneg _,?_,?_⟩
    · simpa only [mul_zero,Real.sqrt_zero] using (hδlim.const_mul 2).sqrt
    · intro n H hHT s
      have hbb (s : WaitingTime H) : |d.C H s|≤1 := by
        have hh := (CKPhysicalConsequences.physical_bounds_of_equations h).1 H s H.coe_nonneg s.val.coe_nonneg
        rw [abs_of_nonneg hh.1]
        exact hh.2
      exact (actual_overlap_secondMoment_le_twice_abs (p := p) β H n (fun s => d.C H s) hbb s).trans
        ((mul_le_mul_of_nonneg_left (hL1 n H hHT s) (by norm_num : 0≤(2 : ℝ))).trans_eq
          (Real.sq_sqrt (mul_nonneg (by norm_num) (hδ n))).symm)
  · intro T
    apply prefix_primitives_of_tail_primitives
      (fun n t u => responseRow (by have := h.spin_ge_three;omega : 2≤p) β n t u-d.R t u)
    · intro n t ht
      have hR : ContinuousOn (fun u => d.R t u) (Icc 0 t) :=
        h.response_continuous.comp (continuous_const.prodMk continuous_id).continuousOn (fun u hu => ⟨hu.1,hu.2⟩)
      exact (responseRow_integrable (by have := h.spin_ge_three;omega : 2≤p) β n ht.1).sub (hR.intervalIntegrable_of_Icc ht.1)
    · exact hTrace T

end SphericalAging.ActualEnergyUniformBridge
