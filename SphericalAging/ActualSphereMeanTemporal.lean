module

public import SphericalAging.ActualSphereTimeRegularity

public section

/-! Genuine temporal properties of the actual expected sphere SDE state.
These establish actual mean identification, joint C0 continuity, and first
and second time derivatives, without assuming spatial C² of the mean. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualSphereMeanTemporal
open HardSphereDynamics LocalSDE ActualSphereTransition ActualCoordinateDynkin
open ActualC2Dynkin ActualSphereTimeRegularity ActualSphereJointTransitionContinuity
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- The actual vector expected state has precisely the actual coordinate
transition expectations; Bochner evaluation is justified by sphere support. -/
theorem mean_coordinate (hN : N ≠ 0)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) (x : State N) (hx : OnSphere x) (i : Fin N) :
    mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t x i=
      transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t (fun y : State N => y i) x := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let X := jointProcess D β R hR (J,x)
  have hi : Integrable (X t) (VectorBrownian.law N) := by
    apply Integrable.of_bound (((terminal_measurable D β R hR J t).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable) R
    filter_upwards [jointProcess_onSphere hN (VectorBrownian.driver N) β R hR hNR J x hx] with ω hω
    have hn : ‖X t ω‖^2=(N : ℝ) := by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hω t
    change ‖X t ω‖≤(R : ℝ)
    nlinarith [norm_nonneg (X t ω)]
  simpa only [mean,transition,PiLp.proj_apply] using
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).integral_comp_comm hi).symm

/-- The actual expected state is jointly continuous in time and physical
sphere initial state, including at the initial boundary. -/
theorem mean_jointContinuous_sphere (hN : N ≠ 0)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) :
    Continuous (fun q : ℝ≥0 × {y : State N // OnSphere y} =>
      mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J q.1 q.2.val) := by
  have hc (i : Fin N) := transition_C2_jointContinuous_sphere hN β R hR hNR J
    (f := fun y : State N => y i) (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).contDiff
  have he : (fun q : ℝ≥0 × {y : State N // OnSphere y} =>
      mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J q.1 q.2.val)=
      fun q => WithLp.toLp 2 (fun i : Fin N => transition
        (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J q.1 (fun y : State N => y i) q.2.val) := by
    funext q
    apply PiLp.ext
    intro i
    exact mean_coordinate hN β R hR hNR J q.1 q.2.val q.2.property i
  rw [he]
  exact (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).comp (continuous_pi hc)

/-- The genuine first time derivative of the actual coordinate mean. -/
theorem mean_coordinate_hasDerivAt (hN : N ≠ 0)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x) (i : Fin N)
    (t : ℝ) (ht : 0<t) :
    HasDerivAt (fun s : ℝ => mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J s.toNNReal x i)
      (transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t.toNNReal
        (SphereGenerator.coefficientGenerator β J (fun y : State N => y i)) x) t := by
  have he : (fun s : ℝ => mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J s.toNNReal x i)=
      fun s : ℝ => transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J s.toNNReal (fun y : State N => y i) x :=
    funext (fun s => mean_coordinate hN β R hR hNR J s.toNNReal x hx i)
  rw [he]
  exact transition_coordinate_generator_hasDerivAt hN β R hR hNR J x hx t ht i

/-- The actual coordinate mean has a genuine second time derivative. -/
theorem mean_coordinate_secondDerivAt (hN : N ≠ 0)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x) (i : Fin N)
    (t : ℝ) (ht : 0<t) :
    HasDerivAt (fun s : ℝ => deriv (fun r : ℝ => mean
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J r.toNNReal x i) s)
      (transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t.toNNReal
        (SphereGenerator.coefficientGenerator β J (SphereGenerator.coefficientGenerator β J (fun y : State N => y i))) x) t := by
  have he : (fun s : ℝ => mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J s.toNNReal x i)=
      fun s : ℝ => transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J s.toNNReal (fun y : State N => y i) x :=
    funext (fun s => mean_coordinate hN β R hR hNR J s.toNNReal x hx i)
  rw [he]
  exact transition_C4_secondDerivAt hN β R hR hNR J x hx
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).contDiff t ht

end SphericalAging.ActualSphereMeanTemporal
