module

public import SphericalAging.ActualC2GeneratorAtZero
public import SphericalAging.ActualSphereContinuousSemigroup

public section

/-! Genuine backward generator identity derived from actual restart,
Chapman-Kolmogorov, and C² Itô. The remaining spatial regularity hypothesis
is explicitly on the actual transition observable; no PDE identity is an
input. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualC2BackwardGenerator
open HardSphereDynamics LocalSDE ActualSphereTransition ActualC2Dynkin
open ActualC2GeneratorAtZero ActualSphereContinuousSemigroup
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- Actual generator commutation, conditional only on the explicitly
remaining spatial C² regularity of the actual transition observable. -/
theorem transition_generator_commutes_of_contDiff (hN : N ≠ 0)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) (ht : 0<t)
    (hg : ContDiff ℝ 2 (transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t.toNNReal f)) :
    SphereGenerator.coefficientGenerator β J
      (transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t.toNNReal f) x=
    transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t.toNNReal
      (SphereGenerator.coefficientGenerator β J f) x := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let g := transition D β R hR J t.toNNReal f
  have hzero := transition_C2_hasDerivWithinAt_zero hN β R hR hNR J x hx hg
  have hd := transition_C2_hasDerivAt hN β R hR hNR J x hx hf t ht
  have hshift : HasDerivAt (fun s : ℝ => transition D β R hR J (s+t).toNNReal f x)
      (transition D β R hR J t.toNNReal (SphereGenerator.coefficientGenerator β J f) x) 0 := by
    have hline : HasDerivAt (fun s : ℝ => s+t) 1 0 := (hasDerivAt_id (0 : ℝ)).add_const t
    have hd' : HasDerivAt (fun s : ℝ => transition D β R hR J s.toNNReal f x)
        (transition D β R hR J t.toNNReal (SphereGenerator.coefficientGenerator β J f) x) (0+t) := by
      simpa only [zero_add] using hd
    simpa only [Function.comp_def,mul_one] using hd'.comp 0 hline
  have hsame (s : ℝ) (hs : s ∈ Ici 0) :
      transition D β R hR J s.toNNReal g x=transition D β R hR J (s+t).toNNReal f x := by
    have hck := transition_semigroup_continuous hN β R hR hNR J s.toNNReal t.toNNReal f hf.continuous x hx
    rw [← Real.toNNReal_add hs ht.le] at hck
    exact hck.symm
  have hright : HasDerivWithinAt (fun s : ℝ => transition D β R hR J s.toNNReal g x)
      (transition D β R hR J t.toNNReal (SphereGenerator.coefficientGenerator β J f) x) (Ici 0) 0 := by
    apply hshift.hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact hsame s hs
    · exact hsame 0 self_mem_Ici
  have he := (uniqueDiffOn_Ici 0).eq self_mem_Ici hzero hright
  have he1 := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) he
  simpa only [ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul,one_mul] using he1

/-- Genuine backward evolution follows from the true semigroup and actual
Itô generator once the actual transition observable is spatially C². -/
theorem transition_backward_hasDerivAt_of_contDiff (hN : N ≠ 0)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) (ht : 0<t)
    (hg : ContDiff ℝ 2 (transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t.toNNReal f)) :
    HasDerivAt (fun s : ℝ => transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J s.toNNReal f x)
      (SphereGenerator.coefficientGenerator β J
        (transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t.toNNReal f) x) t := by
  rw [transition_generator_commutes_of_contDiff hN β R hR hNR J x hx hf t ht hg]
  exact transition_C2_hasDerivAt hN β R hR hNR J x hx hf t ht

/-- Canonical rotational form of the genuine backward evolution, retaining
only the explicit spatial regularity boundary of the actual transition. -/
theorem transition_backward_canonicalGenerator_of_contDiff (hN : N ≠ 0)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) (ht : 0<t)
    (hg : ContDiff ℝ 2 (transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t.toNNReal f)) :
    HasDerivAt (fun s : ℝ => transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J s.toNNReal f x)
      (SphereGeneratorIntegrationByParts.rotationGenerator (1/(2*(N : ℝ))) β J
        (fun ij : Fin N × Fin N => SphereRotationGeometry.coordinateRotation ij.1 ij.2)
        (transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t.toNNReal f) x) t := by
  rw [SphereCanonicalGenerator.canonical_rotationGenerator_eq_coefficientGenerator
    (Nat.pos_of_ne_zero hN) β J hg x hx]
  exact transition_backward_hasDerivAt_of_contDiff hN β R hR hNR J x hx hf t ht hg

end SphericalAging.ActualC2BackwardGenerator
