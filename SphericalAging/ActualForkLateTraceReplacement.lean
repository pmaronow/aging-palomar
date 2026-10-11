module

public import SphericalAging.ActualForkLateOverlapTransfer
public import SphericalAging.ActualResponseShortHorizonTraceMoments
public import SphericalAging.RandomPowerTraceReplacement

public section

/-! The actual last-window energy trace can replace both random overlap
powers by their literal stationary-profile weights. The bound depends
only on the lag window and the genuine physical overlap error. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualForkLateTraceReplacement
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel HardSphereDynamics
open PhysicalForkDrivers PhysicalForkConstruction WienerForkTransfer ActualForkLateOverlapTransfer
open AnnealedResponseMatrixContraction ActualFiniteHorizonTraceReplacement
open ActualForkTraceFormula ActualForkEnergySubtraction PhysicalForkMeanEnergyDuhamel
open AnnealedHamiltonianEnergyStein TwoTimeResponseTimeParameter EnergyCovarianceContraction
open PhysicalForkOverlapAggregation PhysicalForkLateOverlapLimit ForkParameterBounds
open ActualResponseShortHorizonTraceMoments RandomPowerTraceReplacement
open scoped NNReal ENNReal BigOperators InnerProductSpace
variable {N p K : ℕ}

@[expose] def lateWeight (p K : ℕ) (c : ℝ→ℝ) (L τ : ℝ) : ℝ :=
  (c τ)^(p-1)-(mixedOverlap c K L τ)^(p-1)

@[expose] def replacementField (β : ℝ≥0) (T L : ℝ≥0) (b : Fin K) (c : ℝ→ℝ)
    (U : WaitingTime (T+L)×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ]State N)
    (q : WaitingTime (T+L)×((Disorder N p×State N)×PathSeed N K)) : ℝ :=
  subtractionField β (T+L) T b U q-
    lateWeight p K c L ((T+L : ℝ≥0)-(q.1:ℝ≥0))*normalizedTrace (U q)

/-- True finite-law last-window trace replacement, with no independence
between the response and either overlap and no expected-trace premise. -/
theorem actual_late_trace_abs_bound (hN : 0<N) (hp : 2≤p) (hK : 0<K)
    (β : ℝ≥0) (T L v : ℝ≥0) (hv : v≤L) {c r : ℝ→ℝ} {q : ℝ}
    (H : ProfileCenterEnergy.Profile c r q) (b : Fin K)
    (U : WaitingTime (T+L)×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ]State N)
    (hU : StronglyMeasurable U) (hUs : RepresentsPhysicalMatrix hN β (T+L) T b U)
    {B : ℝ} (hB : lateOverlapError (N:=N) (p:=p) β T L c b v≤B) :
    (∫a,|replacementField β T L b c U (lateWaiting T L v hv,a)|
      ∂(AnnealedModelLaw.parameterLaw N p).prod (pathSeedLaw N K))≤
      2*((p-1:ℕ):ℝ)*Real.sqrt B*Real.sqrt (1+annealedFourthConstant p β L) := by
  let s := lateWaiting T L v hv
  let tr := fun z : ForkSpace N p K => normalizedTrace (U (s,MeasurableEquiv.prodAssoc z))
  have hmp := measurePreserving_prodAssoc (AnnealedModelLaw.parameterLaw N p)
    (futureLaw N K) (VectorBrownian.law N)
  have hlag : T+L-(s:ℝ≥0)=L-v := add_tsub_add_eq_tsub_left T L v
  have ht := actual_trace_fourthMoments_window hN hp (driver (N:=N) (K:=K) T b) β (N+1)
    (modelRadius_pos N) (modelRadius_sq N) (T+L) L U hU hUs s (by rw [hlag];exact tsub_le_self)
  have ht4 : MemLp tr 4 (forkLaw N p K) := ht.1.comp_measurePreserving hmp
  have htC : (∫z,|tr z|^4 ∂forkLaw N p K)≤annealedFourthConstant p β L :=
    (hmp.integral_comp MeasurableEquiv.prodAssoc.measurableEmbedding
      (fun a => |normalizedTrace (U (s,a))|^4)).trans_le ht.2
  let a := c ((L:ℝ)-(v:ℝ))
  let k := mixedOverlap c K L ((L:ℝ)-(v:ℝ))
  have hτ : ((L:ℝ)-(v:ℝ))∈Icc (0:ℝ) L := ⟨sub_nonneg.mpr hv,by linarith [v.coe_nonneg]⟩
  have ha := H.bounds ((L:ℝ)-(v:ℝ)) hτ.1
  have hk := mixed_overlap_bounds H (by omega : 1≤K) L.coe_nonneg hτ
  have hd := weighted_random_power_difference (p-1)
    (pairOverlap_memLp (p:=p) hN β T L v b b).aestronglyMeasurable
    (aestronglyMeasurable_const (b:=a)) (pairOverlap_abs_le_one hN β T L v b b)
    (.of_forall fun _ => by rw [abs_of_nonneg ha.1];exact ha.2) ht4 htC
  have hm := weighted_random_power_difference (p-1)
    (meanOverlap_memLp (p:=p) hN β T L v b).aestronglyMeasurable
    (aestronglyMeasurable_const (b:=k)) (meanOverlap_abs_le_one hN hK β T L v b)
    (.of_forall fun _ => by rw [abs_of_nonneg hk.1];exact hk.2.1) ht4 htC
  let f := fun z : ForkSpace N p K =>
    |((pairOverlap β T L v b b z)^(p-1)-(PhysicalForkOverlapAggregation.meanOverlap β T L v b z)^(p-1)-
      (a^(p-1)-k^(p-1)))*tr z|
  have hbound (z : ForkSpace N p K) : f z≤
      |((pairOverlap β T L v b b z)^(p-1)-a^(p-1))*tr z|+
      |((PhysicalForkOverlapAggregation.meanOverlap β T L v b z)^(p-1)-k^(p-1))*tr z| := by
    have he : ((pairOverlap β T L v b b z)^(p-1)-(PhysicalForkOverlapAggregation.meanOverlap β T L v b z)^(p-1)-
      (a^(p-1)-k^(p-1)))*tr z=
      ((pairOverlap β T L v b b z)^(p-1)-a^(p-1))*tr z-
      ((PhysicalForkOverlapAggregation.meanOverlap β T L v b z)^(p-1)-k^(p-1))*tr z := by ring
    dsimp only [f]
    rw [he]
    exact abs_sub _ _
  have hfm : AEStronglyMeasurable f (forkLaw N p K) :=
    (((((pairOverlap_memLp (p:=p) hN β T L v b b).aestronglyMeasurable.pow (p-1)).sub
      ((meanOverlap_memLp (p:=p) hN β T L v b).aestronglyMeasurable.pow (p-1))).sub
      (aestronglyMeasurable_const (b:=a^(p-1)-k^(p-1)))).mul ht4.aestronglyMeasurable).norm
  have hfi : Integrable f (forkLaw N p K) := (hd.1.add hm.1).mono' hfm
    (.of_forall fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤f z from abs_nonneg _)]
      exact hbound z)
  have herrd : (∫z,(pairOverlap β T L v b b z-a)^2 ∂forkLaw N p K)≤B := by
    unfold lateOverlapError at hB
    rw [Real.toNNReal_coe] at hB
    have hn : (0:ℝ)≤∫z : ForkSpace N p K,(PhysicalForkOverlapAggregation.meanOverlap β T L v b z-k)^2 ∂forkLaw N p K :=
      integral_nonneg (fun _ => sq_nonneg _)
    linarith
  have herrm : (∫z,(PhysicalForkOverlapAggregation.meanOverlap β T L v b z-k)^2 ∂forkLaw N p K)≤B := by
    unfold lateOverlapError at hB
    rw [Real.toNNReal_coe] at hB
    have hn : (0:ℝ)≤∫z : ForkSpace N p K,(pairOverlap β T L v b b z-a)^2 ∂forkLaw N p K :=
      integral_nonneg (fun _ => sq_nonneg _)
    linarith
  have he := hmp.integral_comp MeasurableEquiv.prodAssoc.measurableEmbedding
    (fun a => |replacementField β T L b c U (s,a)|)
  unfold pathSeedLaw
  rw [←he]
  have hfield : (fun z : ForkSpace N p K => |replacementField β T L b c U (s,MeasurableEquiv.prodAssoc z)|)=ᵐ[forkLaw N p K] f := by
    filter_upwards [branchOverlap_eq_pairOverlap hN β T L v hv b,
      meanOverlap_eq_literal hN β T L v hv b] with z hd hm
    have hlagR : ((T+L:ℝ≥0):ℝ)-((s:ℝ≥0):ℝ)=(L:ℝ)-(v:ℝ) := by
      simp only [s,lateWaiting,NNReal.coe_add]
      ring
    simp only [replacementField,subtractionField]
    change |(overlapField _ _ _ _ _ (lateWaiting T L v hv,MeasurableEquiv.prodAssoc z)^(p-1)-
      ActualForkTraceFormula.meanOverlap β (T+L) T b (lateWaiting T L v hv,MeasurableEquiv.prodAssoc z)^(p-1))*
      normalizedTrace (U (s,MeasurableEquiv.prodAssoc z))-
      lateWeight p K c L (((T+L:ℝ≥0):ℝ)-((s:ℝ≥0):ℝ))*normalizedTrace (U (s,MeasurableEquiv.prodAssoc z))|=f z
    rw [hd,hm,hlagR]
    dsimp only [lateWeight,f,tr,a,k]
    congr 1
    ring
  change (∫z,|replacementField β T L b c U (s,MeasurableEquiv.prodAssoc z)| ∂forkLaw N p K)≤_
  rw [integral_congr_ae hfield]
  calc
    _≤(∫z,|((pairOverlap β T L v b b z)^(p-1)-a^(p-1))*tr z| ∂forkLaw N p K)+
      ∫z,|((PhysicalForkOverlapAggregation.meanOverlap β T L v b z)^(p-1)-k^(p-1))*tr z| ∂forkLaw N p K := by
        rw [←integral_add hd.1 hm.1]
        exact integral_mono_ae hfi (hd.1.add hm.1) (.of_forall hbound)
    _≤((p-1:ℕ):ℝ)*Real.sqrt B*Real.sqrt (1+annealedFourthConstant p β L)+
      ((p-1:ℕ):ℝ)*Real.sqrt B*Real.sqrt (1+annealedFourthConstant p β L) :=
        add_le_add (hd.2.trans (by gcongr)) (hm.2.trans (by gcongr))
    _=_ := by ring

end SphericalAging.ActualForkLateTraceReplacement
