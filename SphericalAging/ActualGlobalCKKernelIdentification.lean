module

public import SphericalAging.ActualPrintedCKRowIdentification
public import SphericalAging.GlobalCKExtension

public section

/-! All compact limits of the literal actual C/Γ/R kernels solve the
complete global CK specification. No deterministic CK equation, nonlinear
memory convergence, derivative, primitive, or diagonal is a premise. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal
namespace SphericalAging.ActualGlobalCKKernelIdentification
open CompactKernelMemoryLimit ActualCompactCKMemoryLimit ActualPrintedCKRowIdentification
  ActualCompactCorrelationProperties CompactCKPrimitiveSlopeIdentification
  ActualResponsePrimitiveInterchange
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} {L : Filter A} [NeBot L] {p : ℕ}

 theorem actual_global_ck_equations_of_uniform_kernels
    (dim : A→ℕ) (hdim : Tendsto dim L atTop) (hD : ∀j,3≤dim j)
    (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β) {C G R : Kernel}
    (hC : ∀T,TendstoUniformlyOn (fun j => Function.uncurry (modelCorrelation (dim j) p β))
      (Function.uncurry C) L (square T))
    (hG : ∀T,TendstoUniformlyOn (fun j => Function.uncurry (modelGamma (dim j) p β))
      (Function.uncurry G) L (square T))
    (hR : ∀T,TendstoUniformlyOn (fun j => Function.uncurry (modelResponse (N := dim j) (p := p) β))
      (Function.uncurry R) L (triangle T))
    (hCc : Continuous (Function.uncurry C)) (hGc : Continuous (Function.uncurry G))
    (hRc : Continuous (Function.uncurry R)) :
    CKSpecification.CKEquations p β (realCKData p β C R) := by
  let d := realCKData p β C R
  have hCd : Continuous (Function.uncurry d.C) := realKernel_continuous hCc
  have hRd : Continuous (Function.uncurry d.R) := realKernel_continuous hRc
  have hμd : Continuous d.multiplier := realCKData_multiplier_continuous p β hCc hRc
  have hSymm : ∀t s,C t s=C s t := fun t s =>
    compact_correlation_limit_symm dim β (max t s) (hC (max t s)) (le_max_left _ _) (le_max_right _ _)
  have hCorrRow : ∀s t : ℝ,0≤s→s≤t→d.C t s=
      1+∫u in s..t,CKSpecification.correlationSlope p β d u s := by
    intro s t hs hst
    have ht := hs.trans hst
    let sn := s.toNNReal
    let tn := t.toNNReal
    have hes : (sn : ℝ)=s := Real.coe_toNNReal _ hs
    have het : (tn : ℝ)=t := Real.coe_toNNReal _ ht
    have hnt : sn≤tn := by change (sn : ℝ)≤tn;rw [hes,het];exact hst
    have hh := actual_printed_correlation_integral_row dim hdim hD hp β (tn+1) (by positivity)
      (hC (tn+1)) (hR (tn+1)) hCc hRc sn tn hnt (by simp)
    simpa only [hes,het] using hh
  have hRespRow : ∀s t : ℝ,0≤s→s≤t→d.R t s=
      1+∫u in s..t,CKSpecification.responseSlope p β d u s := by
    intro s t hs hst
    have ht := hs.trans hst
    let tn := t.toNNReal
    have het : (tn : ℝ)=t := Real.coe_toNNReal _ ht
    have hh := actual_printed_response_integral_row dim hdim hD hp β (tn+1) (by positivity)
      (hC (tn+1)) (hG (tn+1)) (hR (tn+1)) hCc hGc hRc tn (by simp) s
        (by rw [het];exact ⟨hs,hst⟩)
    simpa only [het] using hh
  have hCS := GlobalCKExtension.correlationSlope_continuous_of_data p β d hCd hRd hμd
  have hRS := GlobalCKExtension.responseSlope_continuous_of_data p β d hCd hRd hμd
  refine {
    spin_ge_three := hp
    beta_pos := hβ
    correlation_continuous := hCd.continuousOn
    response_continuous := hRd.continuousOn
    multiplier_continuous := hμd.continuousOn
    correlation_symmetric := ?_
    correlation_diagonal := ?_
    response_diagonal := ?_
    multiplier_eq := ?_
    response_derivative := ?_
    correlation_derivative := ?_
    response_slope_continuous := hRS.continuousOn
    correlation_slope_continuous := hCS.continuousOn
  }
  · intro t s _ _
    exact hSymm t.toNNReal s.toNNReal
  · intro t ht
    exact compact_correlation_limit_diag dim (fun j => by have := hD j;omega) (by omega : 0<p)
      β t.toNNReal (hC t.toNNReal) le_rfl
  · intro t ht
    simpa only [intervalIntegral.integral_same,add_zero] using hRespRow t t ht le_rfl
  · intro t ht
    have hh := effectiveMultiplier_eq_printed (R := R) p β hSymm t.toNNReal
    simpa only [Real.coe_toNNReal _ ht] using hh
  · intro t s hs hst
    exact CKResponsePrimitiveKernel.ckResponse_hasDerivWithinAt_of_integral_row p β d hμd hCd hRd hst
      (fun u hu => hRespRow s u hs hu)
  · intro t s hs hst
    have hS : Continuous (fun u => CKSpecification.correlationSlope p β d u s) :=
      hCS.comp (continuous_id.prodMk continuous_const)
    have hd := (intervalIntegral.integral_hasDerivAt_right (hS.intervalIntegrable s t)
      hS.aestronglyMeasurable.stronglyMeasurableAtFilter hS.continuousAt).const_add (1 : ℝ)
    exact hd.hasDerivWithinAt.congr_of_mem (fun u hu => hCorrRow s u hs hu) hst

end SphericalAging.ActualGlobalCKKernelIdentification
