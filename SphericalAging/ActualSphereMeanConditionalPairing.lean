module

public import SphericalAging.ActualSphereDensityResponse
public import SphericalAging.ActualSphereConditionalKernel

public section

/-! Genuine waiting-state/future-state pairing with the actual conditional
mean. Bounded coordinate tests agree with coordinates on the physical
sphere, so the Markov identity applies without unbounded-test assumptions. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualSphereMeanConditionalPairing
open FiniteModel HardSphereDynamics SphereInitialLaw ActualSphereTransition
open ActualSphereMarkovRestart ActualSphereConditionalKernel ActualSphereMeanBackward
open ActualSphereMeanSpatialInterface
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
variable {N p : ℕ}

@[expose] def boundedCoordinate (R : ℝ≥0) (i : Fin N) (x : State N) : ℝ :=
  max (-(R:ℝ)) (min (R:ℝ) (x i))

theorem boundedCoordinate_continuous (R : ℝ≥0) (i : Fin N) :
    Continuous (boundedCoordinate R i) := by unfold boundedCoordinate;fun_prop

theorem boundedCoordinate_bound (R : ℝ≥0) (i : Fin N) (x : State N) :
    ‖boundedCoordinate R i x‖≤R := by
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  exact ⟨le_max_left _ _,max_le (by linarith [R.coe_nonneg]) (min_le_left _ _)⟩

theorem boundedCoordinate_eq_of_norm_le (R : ℝ≥0) (i : Fin N) (x : State N)
    (hx : ‖x‖≤R) : boundedCoordinate R i x=x i := by
  have hi : |x i|≤R := by simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x i).trans hx
  rw [boundedCoordinate,min_eq_right (abs_le.mp hi).2,max_eq_right (abs_le.mp hi).1]

theorem sphere_norm_le_radius (R : ℝ≥0) (hNR : (N:ℝ)<(R:ℝ)^2)
    {x : State N} (hx : OnSphere x) : ‖x‖≤R := by
  have he := (onSphere_iff_norm_sq x).mp hx
  nlinarith [norm_nonneg x,R.coe_nonneg]

theorem transition_boundedCoordinate_eq_mean (hN : N≠0) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (u : ℝ≥0) (i : Fin N) (x : State N) (hx : OnSphere x) :
    transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J u (boundedCoordinate R i) x=
      mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J u x i := by
  rw [←transition_coordinate_eq_mean β R hR J u i x]
  unfold transition
  apply integral_congr_ae
  filter_upwards [jointProcess_onSphere hN (VectorBrownian.driver N) β R hR hNR J x hx] with ω hω
  exact boundedCoordinate_eq_of_norm_le R i _ (sphere_norm_le_radius R hNR (hω u))

theorem coordinate_waiting_identity (hN : N≠0) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (x : State N) (hx : OnSphere x) (s u : ℝ≥0) (i : Fin N) :
    (∫ω : VectorBrownian.Space N,
      (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) s ω) i*
        (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) (s+u) ω) i
      ∂VectorBrownian.law N)=
    ∫ω : VectorBrownian.Space N,
      (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) s ω) i*
        (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J u
          (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) s ω)) i
      ∂VectorBrownian.law N := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let X := jointProcess D β R hR (J,x)
  have hsol := fun T => jointProcess_physical hN (VectorBrownian.driver N) β R hR hNR J x hx T
  have hsphere := jointProcess_onSphere hN (VectorBrownian.driver N) β R hR hNR J x hx
  have hH : StronglyMeasurable[(NullAugmentation.augment (VectorBrownian.filtration N)
      (VectorBrownian.law N)) s] (fun ω => boundedCoordinate R i (X s ω)) :=
    (boundedCoordinate_continuous R i).stronglyMeasurable.comp_measurable ((hsol 0).2.1 s).measurable
  have he := waiting_test_identity hN β R hR hNR J X hsol hsphere s u
    (boundedCoordinate R i) (boundedCoordinate_continuous R i).stronglyMeasurable R
    (boundedCoordinate_bound R i) (fun ω => boundedCoordinate R i (X s ω)) hH R
    (fun ω => boundedCoordinate_bound R i (X s ω))
  calc
    _=(∫ω,boundedCoordinate R i (X s ω)*boundedCoordinate R i (X (s+u) ω)
      ∂VectorBrownian.law N) := by
      apply integral_congr_ae
      filter_upwards [hsphere] with ω hω
      rw [boundedCoordinate_eq_of_norm_le R i _ (sphere_norm_le_radius R hNR (hω s)),
        boundedCoordinate_eq_of_norm_le R i _ (sphere_norm_le_radius R hNR (hω (s+u)))]
    _=∫ω,boundedCoordinate R i (X s ω)*transition D β R hR J u (boundedCoordinate R i) (X s ω)
      ∂VectorBrownian.law N := he
    _=_ := by
      apply integral_congr_ae
      filter_upwards [hsphere] with ω hω
      rw [boundedCoordinate_eq_of_norm_le R i _ (sphere_norm_le_radius R hNR (hω s)),
        transition_boundedCoordinate_eq_mean hN β R hR hNR J u i _ (hω s)]

theorem mean_waiting_inner_identity (hN : N≠0) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (x : State N) (hx : OnSphere x) (s u : ℝ≥0) :
    (∫ω : VectorBrownian.Space N,
      ⟪jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) s ω,
        jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) (s+u) ω⟫_ℝ
      ∂VectorBrownian.law N)=
    ∫ω : VectorBrownian.Space N,
      ⟪jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) s ω,
        mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J u
          (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) s ω)⟫_ℝ
      ∂VectorBrownian.law N := by
  classical
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let X := jointProcess D β R hR (J,x)
  have hXm (v : ℝ≥0) : Measurable (X v) :=
    (terminal_measurable D β R hR J v).comp (measurable_const.prodMk measurable_id)
  have hsphere := jointProcess_onSphere hN (VectorBrownian.driver N) β R hR hNR J x hx
  have hleft (i : Fin N) : Integrable (fun ω => (X s ω) i*(X (s+u) ω) i) (VectorBrownian.law N) := by
    have hm := ((PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin N => ℝ) i).continuous.measurable.comp (hXm s)).mul
      ((PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin N => ℝ) i).continuous.measurable.comp (hXm (s+u)))
    apply Integrable.of_bound hm.aestronglyMeasurable ((R:ℝ)^2)
    filter_upwards [hsphere] with ω hω
    change ‖(X s ω) i*(X (s+u) ω) i‖≤(R:ℝ)^2
    rw [norm_mul]
    have h1 := (PiLp.norm_apply_le (X s ω) i).trans (sphere_norm_le_radius R hNR (hω s))
    have h2 := (PiLp.norm_apply_le (X (s+u) ω) i).trans (sphere_norm_le_radius R hNR (hω (s+u)))
    simpa only [pow_two] using mul_le_mul h1 h2 (norm_nonneg _) R.coe_nonneg
  have hright (i : Fin N) : Integrable (fun ω => (X s ω) i*(mean D β R hR J u (X s ω)) i)
      (VectorBrownian.law N) := by
    have hm := ((PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin N => ℝ) i).continuous.measurable.comp (hXm s)).mul
      ((realMean_coordinate_spatial_contDiff β R hR J i (u:ℝ)).continuous.measurable.comp (hXm s))
    have hm' : AEStronglyMeasurable (fun ω => (X s ω) i*(mean D β R hR J u (X s ω)) i)
        (VectorBrownian.law N) := by
      convert hm.aestronglyMeasurable using 1
      funext ω
      simp only [realMean,Real.toNNReal_coe,Function.comp_def,Pi.mul_apply,PiLp.proj_apply,D]
    apply Integrable.of_bound hm' ((R:ℝ)^2)
    filter_upwards [hsphere] with ω hω
    rw [norm_mul]
    have h1 := (PiLp.norm_apply_le (X s ω) i).trans (sphere_norm_le_radius R hNR (hω s))
    have hsqr := mean_norm_sq_le hN (VectorBrownian.driver N) β R hR hNR J u (X s ω) (hω s)
    have h2 : ‖mean D β R hR J u (X s ω)‖≤R := by
      nlinarith [norm_nonneg (mean D β R hR J u (X s ω)),R.coe_nonneg]
    simpa only [pow_two] using mul_le_mul h1 ((PiLp.norm_apply_le _ i).trans h2) (norm_nonneg _) R.coe_nonneg
  simp_rw [SphereRotationGeometry.real_inner_coordinates]
  rw [integral_finsetSum _ (fun i _ => hleft i),integral_finsetSum _ (fun i _ => hright i)]
  exact Finset.sum_congr rfl (fun i _ => coordinate_waiting_identity hN β R hR hNR J x hx s u i)

end SphericalAging.ActualSphereMeanConditionalPairing
