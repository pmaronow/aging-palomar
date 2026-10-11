module

public import SphericalAging.TensorOrthogonalAction

public section

/-! Joint measurable evaluation of the inverse of an actual orthogonal
frame follows from its finite matrix coefficients. -/
noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.OrthogonalInverseMeasurability
open Set MeasureTheory FiniteModel HardSphereDynamics
open scoped InnerProductSpace

theorem inverse_coordinate {N : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) (x : Vector N) (i : Fin N) :
    O.symm x i=⟪O (basisVector i),x⟫_ℝ := by
  have hh := O.inner_map_map (basisVector i) (O.symm x)
  simpa only [LinearIsometryEquiv.apply_symm_apply,basisVector,EuclideanSpace.inner_single_left,
    map_one,one_mul] using hh.symm

theorem inverse_joint_measurable {N : ℕ} {S : Type*} [MeasurableSpace S]
    (O : S→Vector N≃ₗᵢ[ℝ]Vector N)
    (hO : Measurable (fun z : S×Vector N => O z.1 z.2)) :
    Measurable (fun z : S×Vector N => (O z.1).symm z.2) := by
  have hcoord : Measurable (fun z : S×Vector N => fun i : Fin N => ⟪O z.1 (basisVector i),z.2⟫_ℝ) := by
    apply measurable_pi_iff.mpr
    intro i
    have hi : Measurable (fun z : S×Vector N => O z.1 (basisVector i)) :=
      hO.comp (measurable_fst.prodMk measurable_const)
    exact (continuous_fst.inner continuous_snd).measurable.comp (hi.prodMk measurable_snd)
  have hh := (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).measurable.comp hcoord
  convert hh using 1
  funext z
  ext i
  exact inverse_coordinate (O z.1) z.2 i

end SphericalAging.OrthogonalInverseMeasurability
