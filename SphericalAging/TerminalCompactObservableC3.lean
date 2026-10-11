module

public import SphericalAging.TerminalObservableVectorC2
public import SphericalAging.FlowTerminalSpatialC3
public import SphericalAging.L2ObservableFamilyC2

public section

/-! Genuine C³ expectations of compact smooth tests along the actual
terminal SDE flow. The gradient composition is C² in L² by actual
fourth/eighth moment estimates and its literal quadratic remainders. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff InnerProductSpace
namespace SphericalAging.TerminalCompactObservableC3
open HardSphereDynamics LocalSDE FlowTerminalDerivative FlowTerminalMomentBounds
open C2ObservableDerivative CompactObservableGradient
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
local instance : NormedAddCommGroup (State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance

theorem gradient_contDiff_infty {f : State N→ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (gradient f) :=
  (InnerProductSpace.toDual ℝ (State N)).symm.toContinuousLinearEquiv.contDiff.comp
    (hf.fderiv_right (m:=∞) (by simp))

theorem expectation_contDiff_three (D₀ : BrownianDriver N P F)
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
    (T t : ℝ≥0) (hT : 0<T) (ht : t≤T) (f : State N→ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ContDiff ℝ 3 (fun x => observable f
      (stateClass (NullAugmentation.driver D₀) hb hs x T t)) := by
  let D := NullAugmentation.driver D₀
  let X := fun x => stateClass D hb hs x T t
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by simp)
  have hg := gradient_contDiff_infty hf
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
  have hG : ContDiff ℝ 2 (fun x => gradientClass f hf2 K hK (X x)) :=
    TerminalObservableVectorC2.composition_contDiff_two D₀ hbg hsg hb hs hbd hsd hbd2 hsd2
      T t hT ht (gradient f) hg hGb hM hA hB
  have hX : ContDiff ℝ 3 X := FlowTerminalSpatialC3.stateClass_contDiff_three
    D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT t
  let DF := fun x => (observableDerivative f hf2 K hK (X x)).comp (fderiv ℝ X x)
  have hDF : ContDiff ℝ 2 DF := by
    apply contDiff_clm_apply_iff.mpr
    intro v
    exact hG.inner ℝ ((hX.fderiv_right (m:=2) (by norm_num)).clm_apply contDiff_const)
  apply contDiff_succ_iff_hasFDerivAt (n:=2) |>.mpr
  refine ⟨DF,hDF,?_⟩
  intro x
  exact (observable_hasFDerivAt f hf2 C K L hC hK hL (X x)).comp x
    ((hX.differentiable (by norm_num)) x).hasFDerivAt

end SphericalAging.TerminalCompactObservableC3
