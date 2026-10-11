module

public import SphericalAging.FiniteDisclosurePhysicalState
public import SphericalAging.LocalSDE
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

public section

/-! Joint measurability of inverse orthogonal frames, derived from their
literal basis coefficients rather than supplied as a frame premise. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators
namespace SphericalAging.FrameInverseMeasurable
open FiniteModel HardSphereDynamics FiniteDisclosurePhysicalState
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

theorem inverse_coordinate (F : Frame N) (y : Vector N) (i : Fin N) :
    (F.symm y) i=inner ℝ (F (basisVector i)) y := by
  have hh := F.inner_map_map (basisVector i) (F.symm y)
  rw [F.apply_symm_apply] at hh
  simpa [basisVector,PiLp.inner_apply] using hh.symm

theorem inverse_basis_expansion (F : Frame N) (y : Vector N) :
    F.symm y=∑i : Fin N,inner ℝ (F (basisVector i)) y • basisVector i := by
  rw [←LocalSDE.state_sum_basis (F.symm y)]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun a : ℝ => a • basisVector i) (inverse_coordinate F y i))

theorem inverse_joint_measurable {S : Type*} [MeasurableSpace S]
    (F : S→Frame N) (hF : Measurable (fun q : S×Vector N => F q.1 q.2)) :
    Measurable (fun q : S×Vector N => (F q.1).symm q.2) := by
  have hi (i : Fin N) : Measurable (fun q : S×Vector N => inner ℝ (F q.1 (basisVector i)) q.2 • basisVector i) :=
    ((hF.comp (measurable_fst.prodMk measurable_const)).inner measurable_snd).smul_const _
  have hh := Finset.measurable_sum Finset.univ (fun i _ => hi i)
  convert hh using 1
  funext q
  simpa only [Finset.sum_apply] using inverse_basis_expansion (F q.1) q.2

end SphericalAging.FrameInverseMeasurable
