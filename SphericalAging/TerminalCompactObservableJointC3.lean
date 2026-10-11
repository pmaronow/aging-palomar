module

public import SphericalAging.TerminalCompactObservableC3
public import SphericalAging.TerminalObservableVectorJointC2
public import SphericalAging.L2ObservableThirdJet
public import SphericalAging.L2ObservableJointC2

public section

/-! Joint continuity of the literal third spatial derivative of a
compact smooth scalar expectation along the actual terminal SDE. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff InnerProductSpace
namespace SphericalAging.TerminalCompactObservableJointC3
open HardSphereDynamics LocalSDE FlowTerminalDerivative FlowTerminalMomentBounds
open C2ObservableDerivative CompactObservableGradient
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
local instance : NormedAddCommGroup (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] Lp (State N) 2 P) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] Lp (State N) 2 P) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] Lp (State N) 2 P) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] Lp (State N) 2 P) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] Lp (State N) 2 P) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] Lp (State N) 2 P) := inferInstance

theorem third_jet_clamped_joint_continuous (D₀ : BrownianDriver N P F)
    {Kb Ks Lb Ls Mb Ms Ab As : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (hbd3 : ∀i,LipschitzWith Ab (fderiv ℝ (fderiv ℝ (fderiv ℝ (b i)))))
    (hsd3 : ∀i j,LipschitzWith As (fderiv ℝ (fderiv ℝ (fderiv ℝ (s i j)))))
    (T : ℝ≥0) (hT : 0<T) (f : State N→ℝ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) : Continuous (fun z : ℝ≥0×State N =>
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => observable f
        (stateClass (NullAugmentation.driver D₀) hb hs y T (min z.1 T))))) z.2) := by
  let D := NullAugmentation.driver D₀
  let X := fun t x => stateClass D hb hs x T (min t T)
  have hc : Continuous (fun z : ℝ≥0×State N => (min z.1 T,z.2)) :=
    (continuous_fst.min continuous_const).prodMk continuous_snd
  have hX (t) : ContDiff ℝ 3 (X t) := FlowTerminalSpatialC3.stateClass_contDiff_three
    D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT (min t T)
  have hXc : Continuous (fun z : ℝ≥0×State N => X z.1 z.2) := by
    change Continuous ((fun q : ℝ≥0×State N =>
      stateClass (NullAugmentation.driver D₀) hb hs q.2 T q.1) ∘
      (fun z : ℝ≥0×State N => (min z.1 T,z.2)))
    exact (FlowTerminalJointContinuity.stateClass_joint_continuous D₀ hbg hsg hb hs hbd hsd T hT).comp hc
  have hDXc := (FlowTerminalThirdJetContinuity.first_jet_joint_continuous
    D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT).comp hc
  have hDDXc := (FlowTerminalThirdJetContinuity.second_jet_joint_continuous
    D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT).comp hc
  have hDDDXc := (FlowTerminalThirdJetContinuity.third_jet_joint_continuous
    D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT).comp hc
  have hYc := (FlowTerminalJointContinuity.stateResponse_joint_continuous
    D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT).comp hc
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by simp)
  have hg := TerminalCompactObservableC3.gradient_contDiff_infty hf
  have hgc := gradient_hasCompactSupport hfc
  obtain ⟨C0,hC0⟩ := hfc.exists_bound_of_continuous hf.continuous
  obtain ⟨K0,hK0⟩ := (hfc.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv (by simp))
  let C : ℝ≥0 := ⟨max C0 0,le_max_right _ _⟩
  let K : ℝ≥0 := ⟨max K0 0,le_max_right _ _⟩
  have hC : ∀x,‖f x‖≤C := fun x => (hC0 x).trans (le_max_left _ _)
  have hK : ∀x,‖fderiv ℝ f x‖≤K := fun x => (hK0 x).trans (le_max_left _ _)
  have hGb : ∀x,‖gradient f x‖≤K := fun x => by
    simpa only [gradient,LinearIsometryEquiv.norm_map] using hK x
  obtain ⟨M,hM⟩ := gradient_fderiv_bounded hf2 hfc
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hfc.fderiv ℝ)
    (hf.fderiv_right (m:=∞) (by simp)) (by simp)
  obtain ⟨A,hA⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hgc.fderiv ℝ)
    (hg.fderiv_right (m:=∞) (by simp)) (by simp)
  obtain ⟨B,hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport ((hgc.fderiv ℝ).fderiv ℝ)
    ((hg.fderiv_right (m:=∞) (by simp)).fderiv_right (m:=∞) (by simp)) (by simp)
  let G := fun t x => gradientClass f hf2 K hK (X t x)
  have hG (t) : ContDiff ℝ 2 (G t) := TerminalObservableVectorC2.composition_contDiff_two
    D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T (min t T) hT (min_le_right _ _) (gradient f) hg hGb hM hA hB
  have hGc : Continuous (fun z : ℝ≥0×State N => G z.1 z.2) :=
    L2ObservableJointC2.gradientClass_joint_continuous f hf2 K hK
      (gradient_uniformContinuous hf2 hfc) X hXc
  have hDGc : Continuous (fun z : ℝ≥0×State N => fderiv ℝ (G z.1) z.2) := by
    apply continuous_clm_apply.mpr
    intro u
    have hh := (BoundedLpCoefficientContinuity.action_joint_continuous
      (fderiv ℝ (gradient f)) hA.uniformContinuous M hM).comp
        (hXc.prodMk (hYc.clm_apply (continuous_const (y:=u))))
    exact hh.congr (fun z => (TerminalObservableVectorJointC2.composition_first_jet_apply_eq
      D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT (gradient f) hg hGb hM hA hB
        (min z.1 T) (min_le_right _ _) z.2 u).symm)
  have hDDGc : Continuous (fun z : ℝ≥0×State N => fderiv ℝ (fderiv ℝ (G z.1)) z.2) :=
    TerminalObservableVectorJointC2.composition_second_jet_clamped_joint_continuous
      D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT (gradient f) hg hGb hM hA hB
  have hF (t) : ContDiff ℝ 3 (fun y => observable f (X t y)) :=
    TerminalCompactObservableC3.expectation_contDiff_three D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3
      T (min t T) hT (min_le_right _ _) f hf hfc
  apply continuous_clm_apply.mpr
  intro w
  apply continuous_clm_apply.mpr
  intro u
  apply continuous_clm_apply.mpr
  intro v
  have h1 := ((hDDGc.clm_apply (continuous_const (y:=w))).clm_apply
    (continuous_const (y:=u))).inner (𝕜:=ℝ) (hDXc.clm_apply (continuous_const (y:=v)))
  have h2 := (hDGc.clm_apply (continuous_const (y:=u))).inner (𝕜:=ℝ)
    ((hDDXc.clm_apply (continuous_const (y:=w))).clm_apply (continuous_const (y:=v)))
  have h3 := (hDGc.clm_apply (continuous_const (y:=w))).inner (𝕜:=ℝ)
    ((hDDXc.clm_apply (continuous_const (y:=u))).clm_apply (continuous_const (y:=v)))
  have h4 := hGc.inner (𝕜:=ℝ) (((hDDDXc.clm_apply (continuous_const (y:=w))).clm_apply
    (continuous_const (y:=u))).clm_apply (continuous_const (y:=v)))
  exact ((h1.add h2).add (h3.add h4)).congr (fun z =>
    (L2ObservableThirdJet.third_jet_apply f hf2 C K L hC hK hL (X z.1) (hX z.1) (hG z.1)
      (hF z.1) z.2 w u v).symm)

end SphericalAging.TerminalCompactObservableJointC3
