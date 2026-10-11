module

public import SphericalAging.ActualForkAveragedTraceReplacement
public import SphericalAging.ActualForkLateEnergyLimit
public import SphericalAging.CurriedLimitTransfer

public section

/-! Ordered full-history branch-averaged trace replacement from genuine
common-past concentration and actual last-window overlap concentration.
No energy limit or weighted response limit is assumed. -/
noncomputable section
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualForkOrderedTraceReplacement
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel HardSphereDynamics
open PhysicalForkDrivers ActualForkTraceFormula ActualForkEnergySubtraction
open ActualForkPastEnergyBound ActualForkLateEnergyReplacement PhysicalForkLateOverlapLimit
open ActualForkLateEnergyLimit ActualForkAveragedTraceReplacement
open AnnealedResponseMatrixContraction ActualCompactJointOverlapVariance
open TwoTimeResponseTimeParameter EnergyCovarianceContraction ActualResponseKernel
open ActualFiniteHorizonTraceReplacement AnnealedHamiltonianEnergyStein
open CKSpecification StationaryClusterInputs ActualForkMeanBridge SphereFisherHelly ActualSphereForkEndpoints
open scoped NNReal ENNReal Topology BigOperators
variable {N p K : ℕ}

@[expose] def canonicalLateWeightedResponse (hN : 0<N) (β T L : ℝ≥0) (c : ℝ→ℝ) : ℝ :=
  ∫s,lateDeterministicWeight p K c T L s*
    annealedResponse (p:=p) (Nat.ne_of_gt hN) β (N+1) (modelRadius_pos N) (modelRadius_sq N)
      (T+L) s ∂waitingMeasure (T+L)

theorem full_trace_difference_le_actual_errors (hN : 3≤N) (hp : 2≤p) (hK : 0<K)
    (β T L : ℝ≥0) {c r : ℝ→ℝ} {q : ℝ} (H : ProfileCenterEnergy.Profile c r q) (b : Fin K)
    (U : WaitingTime (T+L)×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ]State N)
    (hU : StronglyMeasurable U) (hUs : RepresentsPhysicalMatrix (by omega : 0<N) β (T+L) T b U) :
    |(∫a,subtractionField β (T+L) T b U a ∂integratedLaw N p K (T+L))-
      canonicalLateWeightedResponse (p:=p) (K:=K) (by omega : 0<N) β T L c|≤
      (∫a,|pastSubtractionField β (T+L) T b U a| ∂integratedLaw N p K (T+L))+
        ∫a,|lateReplacementField β T L b c U a| ∂integratedLaw N p K (T+L) := by
  have hn : 0<N := by omega
  have hPast := actual_past_integrated_trace_bound hN hp hK β (T+L) T b U hU hUs
  have hLate := actual_late_integrated_replacement_bound hn hp hK β T L H b U hU hUs
    (fun v hv => (lateOverlapError_bounds hn hK β T L H b ⟨v.coe_nonneg,hv⟩).2)
  have hWeight := actual_late_weighted_response hn hp hK β T L H b U hU hUs
  have hsf : subtractionField β (T+L) T b U=
      pastSubtractionField β (T+L) T b U+lateReplacementField β T L b c U+
        (fun a => lateDeterministicWeight p K c T L a.1*normalizedTrace (U a)) :=
    funext (subtractionField_split β T L b c U)
  have he : (∫a,subtractionField β (T+L) T b U a ∂integratedLaw N p K (T+L))-
      canonicalLateWeightedResponse (p:=p) (K:=K) hn β T L c=
      (∫a,pastSubtractionField β (T+L) T b U a ∂integratedLaw N p K (T+L))+
        ∫a,lateReplacementField β T L b c U a ∂integratedLaw N p K (T+L) := by
    unfold canonicalLateWeightedResponse
    rw [←hWeight.2,hsf,integral_add' (hPast.1.add hLate.1) hWeight.1,integral_add' hPast.1 hLate.1]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add
    (by simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
      (f:=pastSubtractionField β (T+L) T b U) (μ:=integratedLaw N p K (T+L))))
    (by simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
      (f:=lateReplacementField β T L b c U) (μ:=integratedLaw N p K (T+L)))))

theorem actual_ordered_averaged_trace_replacement {p K : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j) (hTop : Tendsto dim atTop atTop)
    (E : ∀j,FisherDensity (dim j) p β)
    (hLaw : ∀j,WaitingDensityLaw β (dim j+1) (modelRadius_pos (dim j)) (E j))
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|(E j).full w-f w|) atTop (𝓝 0))
    (hK : 0<K) (L : ℝ≥0)
    (U : ∀n j : ℕ,Fin K→WaitingTime ((T n).toNNReal+L)×
      ((Disorder (dim j) p×State (dim j))×PathSeed (dim j) K)→State (dim j)→L[ℝ]State (dim j))
    (hU : ∀n j b,StronglyMeasurable (U n j b))
    (hUs : ∀n j b,RepresentsPhysicalMatrix (by have hd:=hDim j;omega : 0<dim j)
      β ((T n).toNNReal+L) (T n).toNNReal b (U n j b)) :
    Tendsto (fun z : ℕ×ℕ =>
      (β:ℝ)*(p:ℝ)*(K:ℝ)⁻¹*(∑b : Fin K,
        ∫a,subtractionField β ((T z.1).toNNReal+L) (T z.1).toNNReal b (U z.1 z.2 b) a
          ∂integratedLaw (dim z.2) p K ((T z.1).toNNReal+L))-
      (β:ℝ)*(p:ℝ)*canonicalLateWeightedResponse (p:=p) (K:=K)
        (by have hd:=hDim z.2;omega : 0<dim z.2) β (T z.1).toNNReal L c)
      ((atTop : Filter ℕ).curry (atTop : Filter ℕ)) (𝓝 0) := by
  have hp : 2≤p := by have hh:=h.spin_ge_three;omega
  let C := (β:ℝ)*(p:ℝ)
  have hC : 0≤C := mul_nonneg β.coe_nonneg (Nat.cast_nonneg p)
  let P := fun n j => (((T n).toNNReal+L:ℝ≥0):ℝ)*((p-1:ℕ):ℝ)*
    Real.sqrt (4*jointVarianceCeiling p β ((T n).toNNReal+L+1)/(dim j:ℝ))*
      Real.sqrt (1+annealedFourthConstant p β ((T n).toNNReal+L))
  have hP (n : ℕ) : Tendsto (P n) atTop (𝓝 0) := by
    have hh := ((tendsto_const_div_atTop_nhds_zero_nat
      (4*jointVarianceCeiling p β ((T n).toNNReal+L+1))).comp hTop).sqrt
    simpa only [P,Function.comp_apply,Real.sqrt_zero,mul_zero,zero_mul] using
      (hh.const_mul ((((T n).toNNReal+L:ℝ≥0):ℝ)*((p-1:ℕ):ℝ))).mul_const
        (Real.sqrt (1+annealedFourthConstant p β ((T n).toNNReal+L)))
  rw [Metric.tendsto_nhds]
  intro ε hε
  let η := ε/(2*(C+1))
  have hCp : 0<C+1 := by linarith
  have hη : 0<η := div_pos hε (mul_pos (by norm_num) hCp)
  have he := actual_late_energy_ordered_uniform H hT dim (fun j => (by have hd:=hDim j;omega : 2≤dim j))
    hTop E hLaw hbridge hi hn hL1 hK L U hU hUs hη
  rw [eventually_curry_iff]
  filter_upwards [he] with n hnη
  have hpη := (hP n).eventually (eventually_lt_nhds hη)
  filter_upwards [hnη,hpη] with j hjη hpj
  have hb (b : Fin K) :
      |(∫a,subtractionField β ((T n).toNNReal+L) (T n).toNNReal b (U n j b) a
        ∂integratedLaw (dim j) p K ((T n).toNNReal+L))-
      canonicalLateWeightedResponse (p:=p) (K:=K) (by have hd:=hDim j;omega : 0<dim j)
        β (T n).toNNReal L c|≤2*η := by
    have hx := full_trace_difference_le_actual_errors (hDim j) hp hK β (T n).toNNReal L
      H.profile b (U n j b) (hU n j b) (hUs n j b)
    have hpb := (actual_past_integrated_trace_bound (hDim j) hp hK β ((T n).toNNReal+L)
      (T n).toNNReal b (U n j b) (hU n j b) (hUs n j b)).2
    exact hx.trans (by have hl:=hjη b;change _≤P n j at hpb;linarith only [hpb,hpj,hl])
  have ha := scaled_average_error_le hK hC hb
  rw [Real.dist_eq,sub_zero]
  apply ha.trans_lt
  have heq : (2*(C+1))*η=ε := by dsimp [η];field_simp
  nlinarith only [heq,hη]

end SphericalAging.ActualForkOrderedTraceReplacement
