module

public import SphericalAging.DriverProcessPullback
public import SphericalAging.RandomSDEStateClass
public import SphericalAging.HamiltonianTerminalDerivative

public section

/-! Globally Lipschitz cutoff SDEs and their actual initial-state L²
derivatives commute with a genuine filtered measure-preserving sample
map. No sphere or derivative law is an input. -/
noncomputable section
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GlobalSDEDriverPullback
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open HardSphereDynamics LocalSDE RandomSDEConversions RandomSDEStateClass
open FilteredRandomSDEPullback FilteredItoPullback BrownianDriverPullback
open scoped NNReal ENNReal
variable {N : ℕ} {Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ} {G : Filtration ℝ≥0 mΩ'} {φ : Ω'→Ω}

theorem process_pullback (hφ : MeasurePreserving φ Q P)
    (hF : ∀t,@Measurable Ω' Ω (G t) (F t) φ)
    (D : BrownianDriver N P F) (E : BrownianDriver N Q G)
    (hB : ∀i t,E.coordinate i t=ᵐ[Q](fun ω => D.coordinate i t (φ ω)))
    {Kb Ks : ℝ≥0} {b : Fin N→State N→ℝ} {σ : Fin N→Fin N→State N→ℝ}
    (hb : ∀i,LipschitzWith Kb (b i)) (hσ : ∀i j,LipschitzWith Ks (σ i j))
    (x : State N) :
    ∀ᵐω ∂Q,∀t,GlobalSDE.process E hb hσ x t ω=
      GlobalSDE.process D hb hσ x t (φ ω) := by
  let X := GlobalSDE.process E hb hσ x
  let Y : ℝ≥0→Ω'→State N := fun t ω => GlobalSDE.process D hb hσ x t (φ ω)
  have hX T := localStrongSolution_to_random (fun i => (hb i).continuous)
    (GlobalSDE.process_strongSolution E hb hσ x T)
  have hY T := randomStrongSolution_pullback hφ hF D E hB
    (fun _ => b) (fun _ => σ) (fun _ => x) (GlobalSDE.process D hb hσ x) T
    (localStrongSolution_to_random (fun i => (hb i).continuous)
      (GlobalSDE.process_strongSolution D hb hσ x T))
  have hall : ∀ᵐω ∂Q,∀n : ℕ,∀t,t≤(n:ℝ≥0)→X t ω=Y t ω := by
    apply ae_all_iff.mpr
    intro n
    exact randomStrongSolutions_unique E hb hσ (fun _ => x) (memLp_const x) X Y n (hX n) (hY n)
  filter_upwards [hall] with ω hω
  intro t
  obtain ⟨n,hn⟩ := exists_nat_ge t
  exact hω n t hn

theorem horizonProcess_pullback (hφ : MeasurePreserving φ Q P)
    (hF : ∀t,@Measurable Ω' Ω (G t) (F t) φ)
    (D : BrownianDriver N P F) (E : BrownianDriver N Q G)
    (hB : ∀i t,E.coordinate i t=ᵐ[Q](fun ω => D.coordinate i t (φ ω)))
    {Kb Ks : ℝ≥0} {b : Fin N→State N→ℝ} {σ : Fin N→Fin N→State N→ℝ}
    (hb : ∀i,LipschitzWith Kb (b i)) (hσ : ∀i j,LipschitzWith Ks (σ i j))
    (x : State N) (T t : ℝ≥0) (ht : t≤T) :
    GlobalSDE.horizonProcess E hb hσ x T t=ᵐ[Q]
      (fun ω => GlobalSDE.horizonProcess D hb hσ x T t (φ ω)) := by
  have he := GlobalSDE.process_eq_horizon E hb hσ x T
  have hd := hφ.quasiMeasurePreserving.ae (GlobalSDE.process_eq_horizon D hb hσ x T)
  filter_upwards [process_pullback hφ hF D E hB hb hσ x,he,hd] with ω hp he hd
  exact (he t ht).symm.trans ((hp t).trans (hd t ht))

@[expose] def statePullback (hφ : MeasurePreserving φ Q P) :
    Lp (State N) 2 P→ₗᵢ[ℝ]Lp (State N) 2 Q :=
  Lp.compMeasurePreservingₗᵢ ℝ φ hφ

theorem terminalStateClass_pullback (hφ : MeasurePreserving φ Q P)
    (hF : ∀t,@Measurable Ω' Ω (G t) (F t) φ)
    (D : BrownianDriver N P F) (E : BrownianDriver N Q G)
    (hB : ∀i t,E.coordinate i t=ᵐ[Q](fun ω => D.coordinate i t (φ ω)))
    {Kb Ks : ℝ≥0} {b : Fin N→State N→ℝ} {σ : Fin N→Fin N→State N→ℝ}
    (hb : ∀i,LipschitzWith Kb (b i)) (hσ : ∀i j,LipschitzWith Ks (σ i j))
    (x : State N) (T t : ℝ≥0) (ht : t≤T) :
    FlowTerminalDerivative.stateClass E hb hσ x T t=
      statePullback hφ (FlowTerminalDerivative.stateClass D hb hσ x T t) := by
  apply Lp.ext
  have hcanonical := hφ.quasiMeasurePreserving.ae_eq_comp
    (FlowTerminalDerivative.stateClass_ae D hb hσ x T t)
  filter_upwards [FlowTerminalDerivative.stateClass_ae E hb hσ x T t,
    horizonProcess_pullback hφ hF D E hB hb hσ x T t ht,
    Lp.coeFn_compMeasurePreserving (FlowTerminalDerivative.stateClass D hb hσ x T t) hφ,
    hcanonical] with ω he hp hl hd
  exact he.trans (hp.trans (hd.symm.trans hl.symm))

end SphericalAging.GlobalSDEDriverPullback
