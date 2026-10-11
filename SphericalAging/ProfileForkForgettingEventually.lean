module

public import SphericalAging.IteratedForkForgettingEventually
public import SphericalAging.ForkNormalizationUniformBounds

public section

/-! Actual marginal stationary profile saturation, uniform normalization bounds, and the correctly ordered finite-fork errors imply waiting-state forgetting. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace SphericalAging.ProfileForkForgettingEventually
open MeasureTheory ProbabilityTheory Filter Set FiniteModel
  ForkEnergyComparison RandomGaussianPairing ForkNormalizedEnergy RandomVectorBounds
  AlgorithmEnergyDeficit ForkForgettingLimit ForkWaitingOverlapTransfer
  ProfileCenterEnergy ForkParameterBounds ForkNormalizationUniformBounds ExternalFieldElementaryPenalty
open scoped Topology ENNReal InnerProductSpace

theorem sequence_forgetting_from_eventual_profile_forks {Θ : Type*} {l : Filter Θ} [NeBot l]
    {p : ℕ} (hp : 3≤p)
    {β ell e q : ℝ} {c r : ℝ→ℝ}
    (hβ : 0<β) (H : Profile c r q) (hq : 0<q) (hq1 : q<1)
    (hell : ell=PlateauAlgebra.multiplier p β q) (he : e=(ell-1)/((p:ℝ)*β))
    (hr : ∀u,0<u→0≤r u) (hm : β^2*PlateauAlgebra.marginalityPolynomial p q=1)
    (L : Θ→ℝ) (K : Θ→ℕ) (hL : ∀a,0≤L a) (hK : ∀a,1≤K a)
    (hLK : Tendsto (fun a => (L a,K a)) l (atTop.curry atTop)) (dim : ℕ→ℕ) (hDim : ∀n,0<dim n)
    {Ω : (Θ×ℕ)→ℕ→Type} [∀θ n,MeasurableSpace (Ω θ n)]
    (μ : ∀θ : Θ×ℕ,∀n,Measure (Ω θ n)) [∀θ n,IsProbabilityMeasure (μ θ n)]
    (J : ∀θ : Θ×ℕ,∀n,Ω θ n→Disorder (dim n) p) (hJ : ∀θ n,HasLaw (J θ n) (disorderLaw (dim n) p) (μ θ n))
    (A M X : ∀θ : Θ×ℕ,∀n,Ω θ n→Vector (dim n))
    (Y : ℕ→∀θ : Θ×ℕ,∀n,Ω θ n→Vector (dim n))
    (hA : ∀θ n,AEStronglyMeasurable (A θ n) (μ θ n))
    (hM : ∀θ n,AEStronglyMeasurable (M θ n) (μ θ n))
    (hX : ∀θ n,AEStronglyMeasurable (X θ n) (μ θ n))
    (hY : ∀m θ n,AEStronglyMeasurable (Y m θ n) (μ θ n))
    (hAb : ∀θ n,∀ᵐω ∂μ θ n,‖A θ n ω‖≤Real.sqrt (dim n))
    (hMb : ∀θ n,∀ᵐω ∂μ θ n,‖M θ n ω‖≤Real.sqrt (dim n))
    (hXb : ∀θ n,∀ᵐω ∂μ θ n,‖X θ n ω‖≤Real.sqrt (dim n))
    (hYb : ∀m θ n,∀ᵐω ∂μ θ n,‖Y m θ n ω‖≤Real.sqrt (dim n))
    {ε : Θ→ℝ} {γ κ : (Θ×ℕ)→ℝ} {f : (Θ×ℕ)→ℝ} {g : ℕ→ℝ} {C_Euler : ℝ}
    (hγ : ∀θ,0≤γ θ) (hε : ∀a,0≤ε a) (hκ : ∀θ,0≤κ θ)
    (hc : ∀θ,0≤f θ) (hCEuler : 0≤C_Euler)
    (hMeanEnergy : ∀θ,limsup
      (fun n => |expectedEnergy (μ:=μ θ n) (J θ n) (M θ n)-forkEnergy p β e c r (K θ.1) (L θ.1)|) atTop≤γ θ)
    (hAlgorithmApprox : ∀θ,limsup
      (fun n => distanceRoot (μ θ n) (dim n) (A θ n) (projected (forkNorm c (K θ.1) (L θ.1)) (M θ n))) atTop≤ε θ.1)
    (hProjectionApprox : ∀θ,limsup
      (fun n => distanceRoot (μ θ n) (dim n) (projected (forkNorm c (K θ.1) (L θ.1)) (M θ n)) (normalized (forkNorm c (K θ.1) (L θ.1)) (M θ n))) atTop≤κ θ)
    (hγLimit : ∀a,Tendsto (fun n => γ (a,n)) atTop (𝓝 0))
    (hεLimit : Tendsto ε l (𝓝 0))
    (hκLimit : ∀a,Tendsto (fun n => κ (a,n)) atTop (𝓝 0))
    (hSpan : ∀m : ℕ,0<m→Tendsto
      (fun θ => deficit (thresholdEnergy p) (fun n => expectedEnergy (μ:=μ θ n) (J θ n) (A θ n))) (l.curry atTop) (𝓝 0)→
      Tendsto (fun θ => limsup
        (fun n => ∫ω,|inner ℝ (A θ n ω) (Y m θ n ω)/(dim n:ℝ)|^2 ∂μ θ n) atTop) (l.curry atTop) (𝓝 0))
    (hEuler : ∀m : ℕ,0<m→∀θ,limsup
      (fun n => ∫ω,‖X θ n ω-Y m θ n ω‖^2/(dim n:ℝ) ∂μ θ n) atTop≤C_Euler/(m:ℝ))
    (hPairBridge : ∀θ,Tendsto
      (fun n => pairing (μ:=μ θ n) (M θ n) (X θ n)) atTop (𝓝 (f θ)))
    (hAgreement : f=ᶠ[l.curry atTop] fun θ => g θ.2) : Tendsto g atTop (𝓝 0) := by
  have hB a := profile_fork_normalization_bounds (p:=p) H hq hr (hK a) (hL a)
  exact IteratedForkForgettingEventually.sequence_forgetting_from_eventual_iterated_errors
    (by omega : 0<p) dim hDim μ J hJ A M X Y hA hM hX hY hAb hMb hXb hYb
    (Q:=fun a => forkNorm c (K a) (L a))
    (h:=fun a => forkEnergy p β e c r (K a) (L a))
    (ρ₀:=q^(-((p:ℝ)/2))) (D₀:=comparison p q) (C₀:=(Real.sqrt q)⁻¹)
    (fun a => (hB a).1) (fun a => (hB a).2.1)
    (fun a => (hB a).2.2.2) (fun a => (hB a).2.2.1)
    hγ hε hκ hc hCEuler hMeanEnergy hAlgorithmApprox hProjectionApprox
    (profile_fork_saturation hp hβ H hq hq1 hell he hr hm L K hL hK hLK)
    hγLimit hεLimit hκLimit hSpan hEuler hPairBridge hAgreement

end SphericalAging.ProfileForkForgettingEventually
