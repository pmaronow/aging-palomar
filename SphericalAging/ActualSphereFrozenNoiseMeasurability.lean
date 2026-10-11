module

public import SphericalAging.ActualSphereFrozenNoiseIncrement

public section

/-! Genuine joint measurability and square integrability of the literal
physical frozen-noise step. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ActualSphereFrozenNoiseMeasurability
open HardSphereDynamics LocalSDE BrownianVectorMoments SphereEulerPredictable
open ActualSphereFrozenNoiseIncrement
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

theorem increment_eq_brownian (h : ℝ≥0) (ω : VectorBrownian.Space N) :
    increment (NullAugmentation.driver (VectorBrownian.driver N)) h 0 ω=
      brownianVector h ω-brownianVector 0 ω := by
  simp only [increment,grid,Nat.zero_add,Nat.cast_one,Nat.cast_zero,mul_one,mul_zero,NullAugmentation.driver,VectorBrownian.driver]
  exact state_sum_basis (brownianVector h ω-brownianVector 0 ω)

theorem frozenNoise_joint_stronglyMeasurable (h : ℝ≥0) :
    StronglyMeasurable (fun q : State N×VectorBrownian.Space N => frozenNoise h q.1 q.2) := by
  have hinc : StronglyMeasurable (increment (NullAugmentation.driver (VectorBrownian.driver N)) h 0) :=
    (increment_stronglyMeasurable _ h 0).mono ((NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)).le _)
  have hx : StronglyMeasurable (Prod.fst : State N×VectorBrownian.Space N→State N) := measurable_fst.stronglyMeasurable
  have hz : StronglyMeasurable (fun q : State N×VectorBrownian.Space N => increment (NullAugmentation.driver (VectorBrownian.driver N)) h 0 q.2) := hinc.comp_measurable measurable_snd
  exact ((contDiff_projection_pair).continuous.comp_stronglyMeasurable (hx.prodMk hz)).const_smul (Real.sqrt 2)

theorem frozenNoise_memLp_two (hN : 0<N) (h : ℝ≥0) (x : State N) (hx : OnSphere x) :
    MemLp (frozenNoise h x) 2 (VectorBrownian.law N) := by
  have hΔ : MemLp (fun ω => brownianVector h ω-brownianVector 0 ω) 2 (VectorBrownian.law N) :=
    (brownianVector_memLp h (q:=2) (by norm_num)).sub (brownianVector_memLp 0 (q:=2) (by norm_num))
  have hm := frozenNoise_joint_stronglyMeasurable (N:=N) h |>.comp_measurable
    (show Measurable (fun ω : VectorBrownian.Space N => (x,ω)) from measurable_const.prodMk measurable_id)
  apply (hΔ.norm.const_mul (Real.sqrt 2)).mono' hm.aestronglyMeasurable
  exact .of_forall (fun ω => by
    change ‖Real.sqrt 2 • projection x (increment (NullAugmentation.driver (VectorBrownian.driver N)) h 0 ω)‖≤_
    rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),increment_eq_brownian]
    exact mul_le_mul_of_nonneg_left (projection_norm_le_onSphere (Nat.ne_of_gt hN) x _ hx) (Real.sqrt_nonneg _))

end SphericalAging.ActualSphereFrozenNoiseMeasurability
