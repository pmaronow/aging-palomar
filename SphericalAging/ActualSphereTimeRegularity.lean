module

public import SphericalAging.ActualSphereJointTransitionContinuity

public section

/-! Genuine additional temporal regularity from repeated actual generator
observations. Spatial C² of the transition mean remains a separate theorem. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualSphereTimeRegularity
open HardSphereDynamics LocalSDE ActualSphereTransition ActualC2Dynkin PhysicalC2Ito
open ActualSphereJointTransitionContinuity
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- The actual coefficient generator loses precisely two spatial
derivatives; C⁴ observables therefore yield a true C² generator observable. -/
lemma generator_contDiff_two (β : ℝ) (J : FiniteModel.Disorder N p)
    {f : State N → ℝ} (hf : ContDiff ℝ 4 f) :
    ContDiff ℝ 2 (SphereGenerator.coefficientGenerator β J f) := by
  have hD : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hH : ContDiff ℝ 2 (MultivariateTaylor.Hessian f) :=
    (hf.fderiv_right (m := 3) (by norm_num)).fderiv_right (by norm_num)
  have hb : ContDiff ℝ 2 (hamiltonianDrift β J) := (contDiff_hamiltonianDrift β J).of_le (by simp)
  have hn (j : Fin N) : ContDiff ℝ 2 (fun x : State N => noiseColumn x j) :=
    (contDiff_noiseColumn j).of_le (by simp)
  unfold SphereGenerator.coefficientGenerator
  exact (hD.clm_apply hb).add (contDiff_const.mul
    (ContDiff.sum (s := Finset.univ) (fun j _ => (hH.clm_apply (hn j)).clm_apply (hn j))))

/-- The true time derivative of a C⁴ transition observable is jointly
continuous in time and sphere state, including its right limit at zero. -/
theorem transition_C4_generator_jointContinuous_sphere (hN : N ≠ 0)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) {f : State N → ℝ} (hf : ContDiff ℝ 4 f) :
    Continuous (fun q : ℝ≥0 × {y : State N // OnSphere y} =>
      transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J q.1
        (SphereGenerator.coefficientGenerator β J f) q.2.val) :=
  transition_C2_jointContinuous_sphere hN β R hR hNR J (generator_contDiff_two β J hf)

/-- Actual second time derivative of the constructed transition
expectation, obtained by two genuine C² Itô generator evolutions. -/
theorem transition_C4_secondDerivAt (hN : N ≠ 0)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x)
    {f : State N → ℝ} (hf : ContDiff ℝ 4 f) (t : ℝ) (ht : 0<t) :
    HasDerivAt (fun s : ℝ => deriv (fun r : ℝ => transition
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J r.toNNReal f x) s)
      (transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t.toNNReal
        (SphereGenerator.coefficientGenerator β J (SphereGenerator.coefficientGenerator β J f)) x) t := by
  have hd := transition_C2_hasDerivAt hN β R hR hNR J x hx (generator_contDiff_two β J hf) t ht
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  exact (transition_C2_hasDerivAt hN β R hR hNR J x hx (hf.of_le (by norm_num)) s hs).deriv

end SphericalAging.ActualSphereTimeRegularity
