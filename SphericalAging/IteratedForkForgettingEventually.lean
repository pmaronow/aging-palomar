module

public import SphericalAging.VariableSeedForkForgetting

public section

/-! The time limit is taken before removing the fork approximation, branch and age parameters. Seed spaces may vary throughout. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace SphericalAging.IteratedForkForgettingEventually
open MeasureTheory ProbabilityTheory Filter Set FiniteModel
  ForkEnergyComparison RandomGaussianPairing ForkNormalizedEnergy RandomVectorBounds
  AlgorithmEnergyDeficit ForkForgettingLimit ForkWaitingOverlapTransfer
open scoped Topology ENNReal InnerProductSpace

theorem sequence_forgetting_from_eventual_iterated_errors {Θ : Type*} {l : Filter Θ} [NeBot l]
    {p : ℕ} (hp : 0<p) (dim : ℕ→ℕ) (hDim : ∀n,0<dim n)
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
    {Q h ε : Θ→ℝ} {γ κ : (Θ×ℕ)→ℝ} {c : (Θ×ℕ)→ℝ} {f : ℕ→ℝ} {E ρ₀ D₀ C₀ C_Euler : ℝ}
    (hQ : ∀a,0<Q a ∧ Q a≤1)
    (hρ : ∀a,0≤(Q a)^(-((p:ℝ)/2)) ∧ (Q a)^(-((p:ℝ)/2))≤ρ₀)
    (hD : ∀a,comparison p (Q a)≤D₀)
    (hRadius : ∀a,(Real.sqrt (Q a))⁻¹≤C₀)
    (hγ : ∀θ,0≤γ θ) (hε : ∀a,0≤ε a) (hκ : ∀θ,0≤κ θ)
    (hc : ∀θ,0≤c θ) (hCEuler : 0≤C_Euler)
    (hMeanEnergy : ∀θ,limsup
      (fun n => |expectedEnergy (μ:=μ θ n) (J θ n) (M θ n)-h θ.1|) atTop≤γ θ)
    (hAlgorithmApprox : ∀θ,limsup
      (fun n => distanceRoot (μ θ n) (dim n) (A θ n) (projected (Q θ.1) (M θ n))) atTop≤ε θ.1)
    (hProjectionApprox : ∀θ,limsup
      (fun n => distanceRoot (μ θ n) (dim n) (projected (Q θ.1) (M θ n)) (normalized (Q θ.1) (M θ n))) atTop≤κ θ)
    (hSaturation : Tendsto (fun a => (Q a)^(-((p:ℝ)/2))*h a) l (𝓝 E))
    (hγLimit : ∀a,Tendsto (fun n => γ (a,n)) atTop (𝓝 0))
    (hεLimit : Tendsto ε l (𝓝 0))
    (hκLimit : ∀a,Tendsto (fun n => κ (a,n)) atTop (𝓝 0))
    (hSpan : ∀m : ℕ,0<m→Tendsto
      (fun θ => deficit E (fun n => expectedEnergy (μ:=μ θ n) (J θ n) (A θ n))) (l.curry atTop) (𝓝 0)→
      Tendsto (fun θ => limsup
        (fun n => ∫ω,|inner ℝ (A θ n ω) (Y m θ n ω)/(dim n:ℝ)|^2 ∂μ θ n) atTop) (l.curry atTop) (𝓝 0))
    (hEuler : ∀m : ℕ,0<m→∀θ,limsup
      (fun n => ∫ω,‖X θ n ω-Y m θ n ω‖^2/(dim n:ℝ) ∂μ θ n) atTop≤C_Euler/(m:ℝ))
    (hPairBridge : ∀θ,Tendsto
      (fun n => pairing (μ:=μ θ n) (M θ n) (X θ n)) atTop (𝓝 (c θ)))
    (hAgreement : c=ᶠ[l.curry atTop] fun θ => f θ.2) : Tendsto f atTop (𝓝 0) := by
  have hg : Tendsto γ (l.curry atTop) (𝓝 0) :=
    CurriedLimitTransfer.tendsto_curried_of_iterated_limits
      (Eventually.of_forall hγLimit) tendsto_const_nhds
  have hk : Tendsto κ (l.curry atTop) (𝓝 0) :=
    CurriedLimitTransfer.tendsto_curried_of_iterated_limits
      (Eventually.of_forall hκLimit) tendsto_const_nhds
  have hfst : Tendsto (Prod.fst : Θ×ℕ→Θ) (l.curry atTop) l :=
    tendsto_fst.mono_left curry_le_prod
  have hs := VariableSeedForkForgetting.from_actual_fork_approximation hp dim hDim μ J hJ
    A M X Y hA hM hX hY hAb hMb hXb hYb
    (Q:=fun θ => Q θ.1) (c:=c) (h:=fun θ => h θ.1)
    (ε:=fun θ => ε θ.1) (γ:=γ) (κ:=κ)
    (fun θ => hQ θ.1) (fun θ => hρ θ.1) (fun θ => hD θ.1)
    (fun θ => hRadius θ.1) hγ (fun θ => hε θ.1) hκ
    hc hCEuler hMeanEnergy hAlgorithmApprox hProjectionApprox
    (hSaturation.comp hfst) hg (hεLimit.comp hfst) hk hSpan hEuler hPairBridge
  exact CurriedLimitTransfer.tendsto_inner_of_curried (hs.2.congr' hAgreement)

end SphericalAging.IteratedForkForgettingEventually
