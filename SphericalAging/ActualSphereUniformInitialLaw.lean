module

public import SphericalAging.ActualSphereCompactSemigroup
public import SphericalAging.ActualSphereKernelSupport

public section

/-! The literal uniform-initial, fixed-disorder sphere SDE waiting law.
Its support and test integrals are derived from the genuine solution. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualSphereUniformInitialLaw
open MeasureTheory Set Filter FiniteModel HardSphereDynamics LocalSDE SphereInitialLaw
open ActualSphereTransition ActualSphereCompactSemigroup ActualSphereKernelSupport
open scoped NNReal ENNReal Topology
variable {N p : ℕ}

@[expose] def waitingLaw (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (t : ℝ≥0) : Measure (State N) :=
  ((sphereLaw N).prod (VectorBrownian.law N)).map
    (fun z : State N×VectorBrownian.Space N =>
      jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,z.1) t z.2)

instance waitingLaw_probability (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (t : ℝ≥0) :
    IsProbabilityMeasure (waitingLaw β R hR J t) := by
  unfold waitingLaw
  infer_instance

theorem waitingLaw_sphere_support (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (t : ℝ≥0) :
    ∀ᵐx∂waitingLaw β R hR J t,OnSphere x := by
  rw [waitingLaw]
  apply (ae_map_iff (terminal_measurable _ β R hR J t).aemeasurable
    measurableSet_onSphere).2
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_onSphere.preimage (terminal_measurable _ β R hR J t))).2
  filter_upwards [sphereLaw_support hN] with x hx
  exact (jointProcess_onSphere (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR J x
    ((onSphere_iff_norm_sq x).mpr hx)).mono (fun ω hω => hω t)

theorem waitingLaw_compact_test_integral (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p)
    {f : State N→ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (t : ℝ≥0) :
    (∫y,f y ∂waitingLaw β R hR J t)=
      ∫x : State N,realTransition β R hR J f t x ∂sphereLaw N := by
  have hm := terminal_measurable (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t
  obtain ⟨C,hC⟩ := hfc.exists_bound_of_continuous hf
  have hi : Integrable (fun z : State N×VectorBrownian.Space N =>
      f (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,z.1) t z.2))
        ((sphereLaw N).prod (VectorBrownian.law N)) :=
    Integrable.of_bound (hf.stronglyMeasurable.comp_measurable hm).aestronglyMeasurable C
      (.of_forall (fun z => hC _))
  rw [waitingLaw,integral_map hm.aemeasurable hf.stronglyMeasurable.aestronglyMeasurable,
    integral_prod _ hi]
  simp only [realTransition,Real.toNNReal_coe,transition]

end SphericalAging.ActualSphereUniformInitialLaw
