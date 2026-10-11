module

public import SphericalAging.SphereTensorObservable
public import SphericalAging.ActualCompactTransitionRegularity
public import SphericalAging.ActualC2BackwardGenerator
public import SphericalAging.SphereSpatialGeneratorRegularity

public section

/-! Literal actual tensor transition means for the ordered observables
Phi_k. A compact ambient extension equals Phi_k near the physical sphere;
its actual mean has genuine spatial C² and satisfies the true backward
generator equation on the sphere. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualSphereTensorSemigroup
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open FiniteModel HardSphereDynamics LocalSDE AdaptiveGradientDisclosure SphereTensorObservable
open ActualSphereTransition ActualCompactTransitionRegularity ActualSphereBackwardIto
open ActualC2BackwardGenerator SphereGeneratorIntegrationByParts SphereQuenchedFDT
open scoped Topology NNReal InnerProductSpace
variable {N p k : ℕ}

@[expose] def compactObservable (R : ℝ≥0) (hR : 0<(R:ℝ)) (x : State N) : TensorSpace N k :=
  coefficientBump (N:=N) R hR x • observable N k x

@[expose] def compactCoordinate (R : ℝ≥0) (hR : 0<(R:ℝ)) (I : TensorIndex N k) (x : State N) : ℝ :=
  compactObservable (k:=k) R hR x I

theorem compactObservable_contDiff (R : ℝ≥0) (hR : 0<(R:ℝ)) :
    ContDiff ℝ (⊤:ℕ∞) (compactObservable (N:=N) (k:=k) R hR) :=
  (coefficientBump (N:=N) R hR).contDiff.smul (observable_contDiff N k)

theorem compactObservable_hasCompactSupport (R : ℝ≥0) (hR : 0<(R:ℝ)) :
    HasCompactSupport (compactObservable (N:=N) (k:=k) R hR) :=
  (coefficientBump (N:=N) R hR).hasCompactSupport.smul_right

theorem compactCoordinate_contDiff (R : ℝ≥0) (hR : 0<(R:ℝ)) (I : TensorIndex N k) :
    ContDiff ℝ (⊤:ℕ∞) (compactCoordinate (N:=N) R hR I) :=
  (PiLp.proj (𝕜:=ℝ) 2 (fun _ : TensorIndex N k => ℝ) I).contDiff.comp
    (compactObservable_contDiff R hR)

theorem compactCoordinate_hasCompactSupport (R : ℝ≥0) (hR : 0<(R:ℝ)) (I : TensorIndex N k) :
    HasCompactSupport (compactCoordinate (N:=N) R hR I) :=
  (compactObservable_hasCompactSupport (N:=N) (k:=k) R hR).comp_left
    (g:=fun y : TensorSpace N k => y I) rfl

theorem compactObservable_eventuallyEq (R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) {x : State N} (hx : OnSphere x) :
    compactObservable (k:=k) R hR=ᶠ[𝓝 x] observable N k := by
  have hxr : ‖x‖<(R:ℝ) := by
    have hh := (onSphere_iff_norm_sq x).mp hx
    nlinarith [norm_nonneg x,R.coe_nonneg]
  have hm : x∈Metric.ball (0 : State N) (coefficientBump (N:=N) R hR).rIn := by
    simpa only [coefficientBump,Metric.mem_ball,dist_zero_right] using hxr
  exact ((coefficientBump (N:=N) R hR).eventuallyEq_one_of_mem_ball hm).mono
    (fun y hy => by simp only [compactObservable,hy,Pi.one_apply,one_smul])

@[expose] def tensorMean (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p)
    (t : ℝ≥0) (x : State N) : TensorSpace N k :=
  ∫ω,compactObservable (k:=k) R hR
    (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) t ω)
      ∂VectorBrownian.law N

@[expose] def realTensorMean (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p)
    (t : ℝ) (x : State N) : TensorSpace N k := tensorMean (k:=k) β R hR J t.toNNReal x

theorem compact_terminal_integrable (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (t : ℝ≥0) (x : State N) :
    Integrable (fun ω => compactObservable (k:=k) R hR
      (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) t ω))
      (VectorBrownian.law N) := by
  obtain ⟨C,hC⟩ := (compactObservable_hasCompactSupport (N:=N) (k:=k) R hR).exists_bound_of_continuous
    (compactObservable_contDiff R hR).continuous
  apply Integrable.of_bound
    ((compactObservable_contDiff (N:=N) (k:=k) R hR).continuous.measurable.comp
      ((terminal_measurable _ β R hR J t).comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable C
  exact ae_of_all _ fun ω => hC _

theorem tensorMean_coordinate (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (t : ℝ≥0) (x : State N) (I : TensorIndex N k) :
    tensorMean (k:=k) β R hR J t x I=
      transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t
        (compactCoordinate R hR I) x := by
  exact ((PiLp.proj (𝕜:=ℝ) 2 (fun _ : TensorIndex N k => ℝ) I).integral_comp_comm
    (compact_terminal_integrable β R hR J t x)).symm

theorem tensorMean_eq_actual_observable (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (t : ℝ≥0) (x : State N) (hx : OnSphere x) :
    tensorMean (k:=k) β R hR J t x=
      ∫ω,observable N k (jointProcess (NullAugmentation.driver (VectorBrownian.driver N))
        β R hR (J,x) t ω) ∂VectorBrownian.law N := by
  apply integral_congr_ae
  filter_upwards [jointProcess_onSphere (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR J x hx] with ω hω
  exact (compactObservable_eventuallyEq R hR hNR (hω t)).eq_of_nhds

theorem tensorMean_norm_le_one (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (t : ℝ≥0) (x : State N) (hx : OnSphere x) :
    ‖tensorMean (k:=k) β R hR J t x‖≤1 := by
  rw [tensorMean_eq_actual_observable hN β R hR hNR J t x hx]
  have hb : ∀ᵐ ω ∂VectorBrownian.law N,‖observable N k
      (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) t ω)‖≤1 := by
    filter_upwards [jointProcess_onSphere (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR J x hx] with ω hω
    exact (observable_norm_one hN (LandscapeDerivatives.sphere_norm _ ((onSphere_iff_norm_sq _).mp (hω t)))).le
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hb

theorem coordinate_spatialC2Transition (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (I : TensorIndex N k) :
    SpatialC2Transition β R hR J (compactCoordinate R hR I) :=
  compact_spatialC2Transition β R hR J
    ((compactCoordinate_contDiff R hR I).of_le (by simp)) (compactCoordinate_hasCompactSupport R hR I)

theorem tensorMean_contDiff_two (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (t : ℝ≥0) :
    ContDiff ℝ 2 (tensorMean (k:=k) β R hR J t) := by
  have he : tensorMean (k:=k) β R hR J t=fun x => (EuclideanSpace.equiv (TensorIndex N k) ℝ).symm
      (fun I => transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t (compactCoordinate R hR I) x) := by
    funext x
    ext I
    exact tensorMean_coordinate β R hR J t x I
  rw [he]
  exact (EuclideanSpace.equiv (TensorIndex N k) ℝ).symm.contDiff.comp
    (contDiff_pi.mpr fun I => (coordinate_spatialC2Transition β R hR J I).slices t)

theorem realTensorMean_coordinate_joint_continuous (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (I : TensorIndex N k) :
    Continuous (fun z : ℝ×State N => realTensorMean (k:=k) β R hR J z.1 z.2 I) := by
  have hh := (coordinate_spatialC2Transition β R hR J I).value.comp
    ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)
  simpa only [Function.comp_def,←tensorMean_coordinate,realTensorMean] using hh

theorem realTensorMean_coordinate_first_joint_continuous (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (I : TensorIndex N k) :
    Continuous (fun z : ℝ×State N => fderiv ℝ (fun x => realTensorMean (k:=k) β R hR J z.1 x I) z.2) := by
  have he t : (fun x => tensorMean (k:=k) β R hR J t x I)=
      transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t (compactCoordinate R hR I) :=
    funext (fun x => tensorMean_coordinate β R hR J t x I)
  have hh := (coordinate_spatialC2Transition β R hR J I).first.comp
    ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)
  simpa only [Function.comp_def,realTensorMean,←he] using hh

theorem realTensorMean_coordinate_second_joint_continuous (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (I : TensorIndex N k) :
    Continuous (fun z : ℝ×State N => fderiv ℝ
      (fderiv ℝ (fun x => realTensorMean (k:=k) β R hR J z.1 x I)) z.2) := by
  have he t : (fun x => tensorMean (k:=k) β R hR J t x I)=
      transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t (compactCoordinate R hR I) :=
    funext (fun x => tensorMean_coordinate β R hR J t x I)
  have hh := (coordinate_spatialC2Transition β R hR J I).second.comp
    ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)
  simpa only [Function.comp_def,realTensorMean,←he,MultivariateTaylor.Hessian] using hh

theorem realTensorMean_coordinate_backward (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (I : TensorIndex N k)
    (t : ℝ) (ht : 0<t) (x : State N) (hx : OnSphere x) :
    HasDerivAt (fun s => realTensorMean (k:=k) β R hR J s x I)
      (rotationGenerator (1/(2*(N:ℝ))) β J (canonicalRotations N)
        (fun y => realTensorMean (k:=k) β R hR J t y I) x) t := by
  have he s : (fun x => tensorMean (k:=k) β R hR J s x I)=
      transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J s (compactCoordinate R hR I) :=
    funext (fun x => tensorMean_coordinate β R hR J s x I)
  have hd := transition_backward_canonicalGenerator_of_contDiff (Nat.ne_of_gt hN) β R hR hNR J x hx
    ((compactCoordinate_contDiff R hR I).of_le (by simp)) t ht
    ((coordinate_spatialC2Transition β R hR J I).slices t.toNNReal)
  simpa only [realTensorMean,he,tensorMean_coordinate,canonicalRotations] using hd

end SphericalAging.ActualSphereTensorSemigroup
