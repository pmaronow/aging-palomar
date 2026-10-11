module

public import SphericalAging.ActualSphereForkMoment
public import SphericalAging.ActualSphereConditionalKernel
public import SphericalAging.ActualSphereTensorProductCurrent

public section

/-! The zero-age fork endpoint is the actual same-path correlation
moment. The identity follows from the genuine conditional transition
theorem, applied to every coordinate of the literal tensor observable. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter
open scoped NNReal ENNReal InnerProductSpace BigOperators
namespace SphericalAging.ActualSphereForkConditional
open FiniteModel HardSphereDynamics AnnealedSDECore ActualSphereTransition
  ActualSphereConditionalKernel ActualSphereTensorSemigroup ActualSphereForkMoment
  ActualSphereTensorProductCurrent SphereTensorObservable
variable {N p k : ℕ}

theorem tensorMean_zero (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (x : State N) :
    tensorMean (k:=k) β R hR J 0 x=compactObservable (k:=k) R hR x := by
  ext I
  rw [tensorMean_coordinate,transition_zero]
  rfl

theorem compactCoordinate_bounded (R : ℝ≥0) (hR : 0<(R:ℝ)) (I : TensorIndex N k) :
    ∃C : ℝ≥0,∀x : State N,‖compactCoordinate R hR I x‖≤C := by
  obtain ⟨C,hC⟩ := (compactCoordinate_hasCompactSupport R hR I).exists_bound_of_continuous
    (compactCoordinate_contDiff R hR I).continuous
  exact ⟨C.toNNReal,fun x => (hC x).trans (Real.le_coe_toNNReal C)⟩

theorem compact_waiting_inner_identity (hN : N≠0) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (X : ℝ≥0→VectorBrownian.Space N→State N) {Z0 : VectorBrownian.Space N→State N}
    (hX : ∀T,IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X T)
    (hXs : ∀ᵐω ∂VectorBrownian.law N,∀t,OnSphere (X t ω)) (s b : ℝ≥0) :
    (∫ω,⟪compactObservable (k:=k) R hR (X s ω),compactObservable (k:=k) R hR (X (s+b) ω)⟫_ℝ
      ∂VectorBrownian.law N)=
    ∫ω,⟪compactObservable (k:=k) R hR (X s ω),tensorMean (k:=k) β R hR J b (X s ω)⟫_ℝ
      ∂VectorBrownian.law N := by
  let F := NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)
  have hXm t : Measurable (X t) := (((hX 0).2.1 t).measurable).mono (F.le t) le_rfl
  have hf (I : TensorIndex N k) (t : ℝ≥0) : StronglyMeasurable (fun ω => compactCoordinate R hR I (X t ω)) :=
    (compactCoordinate_contDiff R hR I).continuous.stronglyMeasurable.comp_measurable (hXm t)
  have hg (I : TensorIndex N k) : StronglyMeasurable (fun ω => tensorMean (k:=k) β R hR J b (X s ω) I) := by
    have hh := (transition_measurable (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J b
      (compactCoordinate R hR I) (compactCoordinate_contDiff R hR I).continuous.stronglyMeasurable).comp_measurable (hXm s)
    simpa only [Function.comp_def,←tensorMean_coordinate] using hh
  have hl (I : TensorIndex N k) : Integrable (fun ω => compactCoordinate R hR I (X s ω)*
      compactCoordinate R hR I (X (s+b) ω)) (VectorBrownian.law N) := by
    obtain ⟨C,hC⟩ := compactCoordinate_bounded R hR I
    apply Integrable.of_bound ((hf I s).mul (hf I (s+b))).aestronglyMeasurable ((C:ℝ)^2)
    apply ae_of_all
    intro ω
    dsimp only [Pi.mul_apply]
    rw [norm_mul]
    simpa only [pow_two] using mul_le_mul (hC (X s ω)) (hC (X (s+b) ω)) (norm_nonneg _) C.coe_nonneg
  have hr (I : TensorIndex N k) : Integrable (fun ω => compactCoordinate R hR I (X s ω)*
      tensorMean (k:=k) β R hR J b (X s ω) I) (VectorBrownian.law N) := by
    obtain ⟨C,hC⟩ := compactCoordinate_bounded R hR I
    apply Integrable.of_bound ((hf I s).mul (hg I)).aestronglyMeasurable ((C:ℝ)^2)
    apply ae_of_all
    intro ω
    dsimp only [Pi.mul_apply]
    rw [norm_mul,tensorMean_coordinate]
    simpa only [pow_two] using mul_le_mul (hC (X s ω))
      (transition_bound _ β R hR J b (compactCoordinate R hR I) C hC (X s ω)) (norm_nonneg _) C.coe_nonneg
  have he (I : TensorIndex N k) : (∫ω,compactCoordinate R hR I (X s ω)*compactCoordinate R hR I (X (s+b) ω)
      ∂VectorBrownian.law N)=
      ∫ω,compactCoordinate R hR I (X s ω)*tensorMean (k:=k) β R hR J b (X s ω) I ∂VectorBrownian.law N := by
    obtain ⟨C,hC⟩ := compactCoordinate_bounded R hR I
    have hH : StronglyMeasurable[F s] (fun ω => compactCoordinate R hR I (X s ω)) :=
      (compactCoordinate_contDiff R hR I).continuous.stronglyMeasurable.comp_measurable ((hX 0).2.1 s).measurable
    have hh := waiting_test_identity hN β R hR hNR J X hX hXs s b
      (compactCoordinate R hR I) (compactCoordinate_contDiff R hR I).continuous.stronglyMeasurable
      C hC (fun ω => compactCoordinate R hR I (X s ω)) hH C (fun ω => hC _)
    simpa only [←tensorMean_coordinate] using hh
  simp_rw [tensor_inner_eq_sum]
  change (∫ω,∑I,compactCoordinate R hR I (X s ω)*compactCoordinate R hR I (X (s+b) ω)
    ∂VectorBrownian.law N)=
    ∫ω,∑I,compactCoordinate R hR I (X s ω)*tensorMean (k:=k) β R hR J b (X s ω) I
      ∂VectorBrownian.law N
  rw [integral_finset_sum Finset.univ (fun I _ => hl I),
    integral_finset_sum Finset.univ (fun I _ => hr I)]
  exact Finset.sum_congr rfl (fun I _ => he I)

/-- Actual conditional restart proves the same-path endpoint, for every
k and hence both k=1 and k=2 in source10.3. -/
theorem zero_branch_eq_same_path (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (X : ℝ≥0→VectorBrownian.Space N→State N) {Z0 : VectorBrownian.Space N→State N}
    (hX : ∀T,IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X T)
    (hXs : ∀ᵐω ∂VectorBrownian.law N,∀t,OnSphere (X t ω)) (s b : ℝ≥0) :
    waitingForkMoment (k:=k) (VectorBrownian.law N) (X s) β R hR J 0 b=
      ∫ω,(⟪X s ω,X (s+b) ω⟫_ℝ/(N:ℝ))^k ∂VectorBrownian.law N := by
  have hXm : Measurable (X s) := (((hX 0).2.1 s).measurable).mono
    ((NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)).le s) le_rfl
  rw [waitingForkMoment_eq_tensorMean hXm (hXs.mono fun _ h => h s) hN β R hR hNR J 0 b]
  simp_rw [tensorMean_zero]
  rw [←compact_waiting_inner_identity (Nat.ne_of_gt hN) β R hR hNR J X hX hXs s b]
  apply integral_congr_ae
  filter_upwards [hXs] with ω hω
  rw [(compactObservable_eventuallyEq R hR hNR (hω s)).eq_of_nhds,
    (compactObservable_eventuallyEq R hR hNR (hω (s+b))).eq_of_nhds]
  exact observable_inner hN _ _

end SphericalAging.ActualSphereForkConditional
