module

public import SphericalAging.SphereGeneratorRegularity
public import SphericalAging.SphereGamma2Algebra

public section

/-! Joint continuity of the spherical generator from genuine spatial
first and second derivatives. No mixed time-space differentiability is
needed by this local analytic interface. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace SphericalAging.SphereSpatialGeneratorRegularity
open FiniteModel SphericalIntegrationByParts SphereGeneratorIntegrationByParts SphereGamma2Algebra
open scoped BigOperators

theorem joint_lieDerivative_continuous {N : ℕ} {m : ℝ→Vector N→ℝ} (A : Operator N)
    (hm : Continuous (fun z : ℝ×Vector N => fderiv ℝ (m z.1) z.2)) :
    Continuous (fun z : ℝ×Vector N => lieDerivative A (m z.1) z.2) :=
  hm.clm_apply (A.continuous.comp continuous_snd)

theorem joint_rotationGenerator_continuous {N p : ℕ} {ι : Type*} [Fintype ι]
    (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N) {m : ℝ→Vector N→ℝ}
    (hs : ∀t,ContDiff ℝ 2 (m t))
    (hfirst : Continuous (fun z : ℝ×Vector N => fderiv ℝ (m z.1) z.2))
    (hsecond : Continuous (fun z : ℝ×Vector N => fderiv ℝ (fderiv ℝ (m z.1)) z.2)) :
    Continuous (fun z : ℝ×Vector N => rotationGenerator κ β J A (m z.1) z.2) := by
  classical
  have htwice i : Continuous (fun z : ℝ×Vector N => lieDerivative (A i) (lieDerivative (A i) (m z.1)) z.2) := by
    have hh : Continuous (fun z : ℝ×Vector N =>
        fderiv ℝ (fderiv ℝ (m z.1)) z.2 (A i z.2) (A i z.2)+
          fderiv ℝ (m z.1) z.2 (A i (A i z.2))) :=
      ((hsecond.clm_apply ((A i).continuous.comp continuous_snd)).clm_apply
        ((A i).continuous.comp continuous_snd)).add
          (hfirst.clm_apply ((A i).continuous.comp ((A i).continuous.comp continuous_snd)))
    exact hh.congr (fun z => (lieDerivative_twice_fderiv (A i) (A i) (hs z.1) z.2).symm)
  unfold rotationGenerator
  exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
    (htwice i).add ((continuous_const.mul
      ((lieDerivative_continuous (A i) ((Hamiltonian_contDiff J).of_le (by simp))).comp continuous_snd)).mul
        (joint_lieDerivative_continuous (A i) hfirst)))

end SphericalAging.SphereSpatialGeneratorRegularity
