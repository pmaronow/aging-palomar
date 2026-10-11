module

public import SphericalAging.ActualResponseFieldCongruence

public section

/-! The true normalized response trace moment depends on the remaining
causal lag, rather than the whole age of the diffusion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.ActualResponseShortHorizonTraceMoments
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel
  HardSphereDynamics TwoTimeResponseParameter TwoTimeResponseTimeParameter
  AnnealedTwoTimeResponseMoments AnnealedResponseMatrixContraction
  ActualFiniteHorizonTraceReplacement ActualAnnealedEnergyReplacement
  AnnealedResponseTimeMoments ResponseMatrixEnergyContraction EnergyCovarianceContraction
open scoped NNReal ENNReal BigOperators InnerProductSpace
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem actual_trace_fourthMoments_short (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (H : ℝ≥0)
    (U : WaitingTime H×((Disorder N p×State N)×Ω)→State N→L[ℝ] State N)
    (hU : StronglyMeasurable U)
    (hUs : ∀s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω)))=ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx))
    (s : WaitingTime H) :
    MemLp (fun q => normalizedTrace (U (s,q))) 4 ((parameterLaw N p).prod P) ∧
    (∫q,|normalizedTrace (U (s,q))|^4 ∂(parameterLaw N p).prod P)≤
      annealedFourthConstant p β (H-s) := by
  obtain ⟨V,hV,hVs,hVm,hVC,_⟩ := exists_actual_annealed_matrix hN hp D₀ β R hR hNR
    s (H+1) (H-s) (tsub_le_self.trans (le_add_right le_rfl)) (by positivity)
  have hUm : StronglyMeasurable (fun q => U (s,q)) :=
    hU.comp_measurable (measurable_const.prodMk measurable_id)
  have he : (fun q => U (s,q))=ᵐ[(parameterLaw N p).prod P] V := by
    apply (Measure.ae_prod_iff_ae_ae (hUm.measurableSet_eq_fun hV)).mpr
    filter_upwards [parameterLaw_onSphere (p:=p) hN] with q hx
    exact (hUs s q hx).trans (hVs q hx).symm
  have ht : (fun q => normalizedTrace (U (s,q)))=ᵐ[(parameterLaw N p).prod P]
      (fun q => normalizedTrace (V q)) := he.mono fun q hq => congrArg normalizedTrace hq
  refine ⟨hVm.ae_eq ht.symm,?_⟩
  rw [integral_congr_ae (ht.mono fun q hq => congrArg (fun x : ℝ => |x|^4) hq)]
  exact hVC

theorem actual_trace_fourthMoments_window (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (H L : ℝ≥0)
    (U : WaitingTime H×((Disorder N p×State N)×Ω)→State N→L[ℝ] State N)
    (hU : StronglyMeasurable U)
    (hUs : ∀s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω)))=ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx))
    (s : WaitingTime H) (hs : H-s≤L) :
    MemLp (fun q => normalizedTrace (U (s,q))) 4 ((parameterLaw N p).prod P) ∧
    (∫q,|normalizedTrace (U (s,q))|^4 ∂(parameterLaw N p).prod P)≤annealedFourthConstant p β L := by
  have h := actual_trace_fourthMoments_short hN hp D₀ β R hR hNR H U hU hUs s
  exact ⟨h.1,h.2.trans (annealedFourthConstant_mono p β hs)⟩

end SphericalAging.ActualResponseShortHorizonTraceMoments
