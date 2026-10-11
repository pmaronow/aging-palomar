module

public import SphericalAging.RandomVectorSDELocalization

public section

/-! Actual tangent-projected random initial linear responses. The initial
projection, F₀ measurability, support bound, strong SDE and moment estimate
are constructed, as needed at the waiting time of a two-time response. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ProjectedRandomResponseMoments
open HardSphereDynamics LocalSDE PredictableLinearCoefficient
set_option maxHeartbeats 1800000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def projectedInitial (Z0 : Ω → State N) (v : State N) : Ω → State N :=
  fun ω => projection (Z0 ω) v

theorem projectedInitial_stronglyMeasurable (Z0 : Ω → State N)
    (hZ0 : StronglyMeasurable[F 0] Z0) (v : State N) :
    StronglyMeasurable[F 0] (projectedInitial Z0 v) :=
  (differentiable_projection v).continuous.comp_stronglyMeasurable hZ0

theorem projectedInitial_norm_bound (hN : N ≠ 0) (Z0 : Ω → State N)
    (hSphere : ∀ᵐ ω ∂P,OnSphere (Z0 ω)) (v : State N) :
    ∀ᵐ ω ∂P,‖projectedInitial Z0 v ω‖ ≤ ‖v‖ := by
  filter_upwards [hSphere] with ω hω
  exact projection_norm_le_onSphere hN _ v hω

theorem projectedInitial_memLp (hN : N ≠ 0) (Z0 : Ω → State N)
    (hZ0 : StronglyMeasurable[F 0] Z0) (hSphere : ∀ᵐ ω ∂P,OnSphere (Z0 ω)) (v : State N) :
    MemLp (projectedInitial Z0 v) 2 P :=
  MemLp.of_bound ((projectedInitial_stronglyMeasurable Z0 hZ0 v).mono (F.le 0)).aestronglyMeasurable
    ‖v‖ (projectedInitial_norm_bound hN Z0 hSphere v)

theorem projectedInitial_energy_le (hN : N ≠ 0) (Z0 : Ω → State N)
    (hZ0 : StronglyMeasurable[F 0] Z0) (hSphere : ∀ᵐ ω ∂P,OnSphere (Z0 ω)) (v : State N) :
    (∫ ω,‖projectedInitial Z0 v ω‖^2 ∂P) ≤ ‖v‖^2 := by
  have hm := projectedInitial_memLp hN Z0 hZ0 hSphere v
  have hi : Integrable (fun ω => ‖projectedInitial Z0 v ω‖^2) P := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using hm.integrable_norm_rpow'
  calc
    _ ≤ ∫ _ω : Ω,‖v‖^2 ∂P := by
      apply integral_mono_ae hi (integrable_const _)
      filter_upwards [projectedInitial_norm_bound hN Z0 hSphere v] with ω hω
      exact pow_le_pow_left₀ (norm_nonneg _) hω 2
    _ = _ := by simp

/-- A real adapted continuous tangent-projected response is constructed
from the actual bounded predictable matrices, with the physical vector
rate and a deterministic direction bound. Its SDE is a conclusion. -/
theorem exists_projected_response_with_secondMoment {Kb Ks : ℝ≥0}
    (hN : N ≠ 0) (F₀ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (D : BrownianDriver N P (NullAugmentation.augment F₀ P))
    (a : Fin N → Coefficient (N := N) (F := NullAugmentation.augment F₀ P) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := NullAugmentation.augment F₀ P) (P := P) Ks)
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[NullAugmentation.augment F₀ P 0] Z0)
    (hSphere : ∀ᵐ ω ∂P,OnSphere (Z0 ω)) (v : State N)
    (driftBound noiseTraceBound : ℝ≥0)
    (haNorm : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,∀ w : State N,
      ‖WithLp.toLp 2 (fun i => (a i).value q w)‖ ≤ driftBound*‖w‖)
    (hsTrace : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,∀ w : State N,
      (∑ i : Fin N,∑ j : Fin N,((sigma i j).value q w)^2) ≤ noiseTraceBound*‖w‖^2)
    (T : ℝ≥0) : ∃ X,
      RandomLinearVariationalSDE.IsStrongSolutionOn a sigma D (projectedInitial Z0 v) X T ∧
      ∀ t,t ≤ T → MemLp (X t) 2 P ∧ (∫ ω,‖X t ω‖^2 ∂P) ≤
        ‖v‖^2*Real.exp (((2*driftBound+1+noiseTraceBound) : ℝ)*(t : ℝ)) := by
  let V0 := projectedInitial Z0 v
  have hV0 := projectedInitial_stronglyMeasurable Z0 hZ0 v
  have hmem := projectedInitial_memLp hN Z0 hZ0 hSphere v
  let X := RandomLinearVariationalSDE.process D a sigma V0 hV0 hmem T
  refine ⟨X,RandomLinearVariationalSDE.process_strongSolution D a sigma V0 hV0 hmem T,?_⟩
  intro t ht
  have hm := RandomVectorSDELocalization.constructed_random_vector_secondMoment_augmented F₀
    D a sigma V0 hV0 hmem ‖v‖₊ (projectedInitial_norm_bound hN Z0 hSphere v)
    driftBound noiseTraceBound haNorm hsTrace T t ht
  refine ⟨hm.1,hm.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (projectedInitial_energy_le hN Z0 hZ0 hSphere v)
    (Real.exp_nonneg _)

end SphericalAging.ProjectedRandomResponseMoments
