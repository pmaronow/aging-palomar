module

public import SphericalAging.ActualTreeEnergyPerturbation

public section

/-! A genuine common event bounds the landscape norm of every actual
terminal disorder. Its failure budget follows from branching Jensen and the
original ordered Gaussian landscape tail. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualTreeLandscapeEvent
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure GaussianLandscape
open HamiltonianBranchingNodeLaw ActualTreeEnergyPerturbation IndependentBranchingSuccess
open IndependentBranchingSuccessEvent GaussianBranchingSuccess PartialVarianceBranchingCoefficients
open HamiltonianTreeEnergy
variable {N p K : ℕ}

@[expose] def good (C : ℝ) : Set (TensorSpace N p) := {s | landscapeNorm N p (tensorDecode s)≤C}

theorem good_measurable (C : ℝ) : MeasurableSet (good (N:=N) (p:=p) C) :=
  measurableSet_le ((landscapeNorm_continuous N p).measurable.comp tensorDecode.continuous.measurable) measurable_const

theorem event_eq_leafLandscapeBound (V : ℕ→ℝ) (hV0 : V 0=1) (C : ℝ) (d : ℕ) :
    event K (update (parentCoefficient V) (freshCoefficient V)) (good (N:=N) (p:=p) C) d=
      {z : TensorSpace N p×TreeSample (TensorSpace N p) K d | LeafLandscapeBound V C d z.1 z.2} := by
  induction d with
  | zero =>
    ext z
    simp only [event,good,mem_setOf_eq,LeafLandscapeBound,partialDisorder,hV0,Real.sqrt_one,one_smul]
  | succ d ih =>
    ext z
    simp only [event,mem_setOf_eq,LeafLandscapeBound]
    simp_rw [ih]
    rfl

theorem actual_leaf_landscape_event (hN : 2≤N) (hp : 0<p) (V : ℕ→ℝ)
    (hV : ∀j,0≤V j) (hVm : ∀j,V (j+1)≤V j) (hV0 : V 0=1) (d : ℕ) :
    ∃Z : Set (TensorSpace N p×TreeSample (TensorSpace N p) K d),MeasurableSet Z ∧
      1-((K^d:ℕ):ℝ)*Real.exp (-(N:ℝ))≤
        ((stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K d)).real Z ∧
      ∀z∈Z,LeafLandscapeBound V (landscapeThreshold p+4) d z.1 z.2 := by
  let C := landscapeThreshold p+4
  let B : Set (TensorSpace N p) := good C
  have hB : MeasurableSet B := good_measurable C
  have hlaw : HasLaw (tensorDecode (N:=N) (p:=p)) (disorderLaw N p) (stdGaussian (TensorSpace N p)) :=
    ⟨tensorDecode_measurePreserving.measurable.aemeasurable,tensorDecode_measurePreserving.map_eq⟩
  have hbadm : MeasurableSet {J : Disorder N p | C<landscapeNorm N p J} :=
    measurableSet_lt measurable_const (landscapeNorm_continuous N p).measurable
  have hm := hlaw.measureReal_eq hbadm
  have hbad : (stdGaussian (TensorSpace N p)).real Bᶜ≤Real.exp (-(N:ℝ)) := by
    have he : Bᶜ=tensorDecode ⁻¹' {J : Disorder N p | C<landscapeNorm N p J} := by
      ext z;simp [B,good]
    rw [he]
    change (stdGaussian (TensorSpace N p)).real {s | C<landscapeNorm N p (tensorDecode s)}≤_
    rw [hm]
    exact landscape_exponential_dimension_bound hN hp
  have hcompl := measureReal_add_measureReal_compl (μ:=stdGaussian (TensorSpace N p)) hB
  have hgood : 1-Real.exp (-(N:ℝ))≤(stdGaussian (TensorSpace N p)).real B := by
    simp only [probReal_univ] at hcompl
    linarith
  have hbern := one_add_mul_sub_le_pow
    (by linarith [measureReal_nonneg (μ:=stdGaussian (TensorSpace N p)) (s:=B)] : (-1:ℝ)≤(stdGaussian (TensorSpace N p)).real B) (K^d)
  have hpow : 1-((K^d:ℕ):ℝ)*Real.exp (-(N:ℝ))≤((stdGaussian (TensorSpace N p)).real B)^(K^d) := by
    have hh := mul_le_mul_of_nonneg_left hgood (Nat.cast_nonneg (K^d))
    nlinarith
  let Z := event K (update (parentCoefficient V) (freshCoefficient V)) B d
  refine ⟨Z,event_measurable K _ (update_measurable _ _) B hB d,?_,?_⟩
  · exact hpow.trans (actual_gaussian_tree_success_lower K _ _ (coefficients_unit V hV hVm) B hB d)
  · intro z hz
    change z∈event K (update (parentCoefficient V) (freshCoefficient V)) (good C) d at hz
    rw [event_eq_leafLandscapeBound V hV0 C d] at hz
    exact hz

end SphericalAging.ActualTreeLandscapeEvent
