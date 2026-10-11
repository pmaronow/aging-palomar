module

public import SphericalAging.ActualSphereCKBridges

public section

/-! The Fisher majorant for the unique CK solution is derived from the
actual spherical diffusion. No finite-model or density realization premise
is left: the actual C/Γ/R dimension limits discharge both mean bridges. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology
namespace SphericalAging.ActualSphereFisherTheorem
open FiniteModel CKSpecification StrongBackwardDefect SphereGoodEventFisherClock
open SphereBadEventFisherMass ActualSphereRestrictedFisherBudget
open ActualSphereCKBridges ActualSphereCKFisherMajorant AnnealedHamiltonianEnergyStein
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true

/-- Actual-model Fisher majorant, budget, clock and late tail for any
diverging sequence of dimensions. The only analytic object supplied is
the CK solution; its actual-model approximation is proved. -/
theorem actual_FisherMajorant {p : ℕ} (β : ℝ≥0) {d : CKData} (h : CKEquations p β d)
    (dim : ℕ→ℕ) (hDim : ∀n,3≤dim n) (hdim : Tendsto dim atTop atTop) :
    ∃ (φ : ℕ→ℕ) (aF : ℝ→ℝ),StrictMono φ ∧ (∀s,0≤aF s) ∧ FisherMajorant p β d aF ∧
      (∫s in Ioi 0,aF s)≤(β:ℝ)^2/2 ∧
      (∀s,ContinuousWithinAt aF (Ici s) s) ∧
      Antitone (fun s => Real.exp (-ceilingRate p β (cutoff p)*s)*aF s) ∧
      (∀T : ℝ,Tendsto (fun n => ∫s in Ioc 0 T,
        |full (N:=dim (φ n)) (p:=p) β (dim (φ n)+1) (modelRadius_pos (dim (φ n))) s-aF s|)
        atTop (𝓝 0)) ∧
      Tendsto (FisherLimitClockDecay.lateSup aF) atTop (𝓝 0) := by
  obtain ⟨φ,aF,hφ,ha,hmass,hac,hclock,hFI,hlate⟩ :=
    actual_FisherMajorant_of_source3_3 (by have := h.spin_ge_three;omega) β h dim hDim hdim
    (canonical_MeanBridge h.spin_ge_three β h.beta_pos d h dim hdim)
    (canonical_ResponsePrimitiveBridge h.spin_ge_three β h.beta_pos d h dim hDim hdim)
  have han s : 0≤aF s := by
    by_cases hs : 0<s
    · exact ha.nonneg s hs
    · have hc := hclock (show s≤1 from by linarith)
      exact nonneg_of_mul_nonneg_right
        ((mul_nonneg (Real.exp_nonneg _) (ha.nonneg 1 (by norm_num))).trans hc) (Real.exp_pos _)
  exact ⟨φ,aF,hφ,han,ha,hmass,hac,hclock,hFI,hlate⟩

end SphericalAging.ActualSphereFisherTheorem
