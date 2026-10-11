module

public import SphericalAging.AdaptiveGradientDisclosure
public import SphericalAging.HamiltonianParameter

public section

/-! Measurability of the actual Hamiltonian gradient from the disclosed
tensor coordinates and the queried state. The disorder projection may vary
with the history; only its preceding measurability receipt is used. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace SphericalAging.GradientDisclosureMeasurability
open Set MeasureTheory FiniteModel HardSphereDynamics HamiltonianParameter AdaptiveGradientDisclosure
open scoped InnerProductSpace BigOperators

 theorem gradient_joint_continuous (N p : ℕ) :
    Continuous (fun z : Disorder N p×Vector N => gradient (Hamiltonian N p z.1) z.2) := by
  have he : (fun z : Disorder N p×Vector N => gradient (Hamiltonian N p z.1) z.2)=
      fun z => ∑I : TensorIndex N p,z.1 I • hamiltonianGradient (disorderBasis I) z.2 := by
    funext z
    simpa only [hamiltonianGradient,Finset.sum_apply,Pi.smul_apply] using congrFun (gradient_sum_basis z.1) z.2
  rw [he]
  apply continuous_finsetSum
  intro I _
  exact ((continuous_apply I).comp continuous_fst).smul
    ((hamiltonianGradient_contDiff (disorderBasis I)).continuous.comp continuous_snd)

 theorem gradient_measurable_from_disclosure {Ω : Type*} {m : MeasurableSpace Ω} {N p : ℕ}
    (hp : 2≤p) (W : Ω→Submodule ℝ (Vector N)) (J : Ω→Disorder N p) (X : Ω→Vector N)
    (hJ : Measurable (fun ω => disclosedDisorder (W ω) (J ω))) (hX : Measurable X)
    (hx : ∀ω,X ω∈W ω) : Measurable (fun ω => gradient (Hamiltonian N p (J ω)) (X ω)) := by
  have hh := (gradient_joint_continuous N p).measurable.comp (hJ.prodMk hX)
  convert hh using 1
  funext ω
  exact gradient_eq_disclosed hp (W ω) (J ω) (hx ω)

end SphericalAging.GradientDisclosureMeasurability
