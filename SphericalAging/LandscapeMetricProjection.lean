module

public import SphericalAging.ConvexMetricProjection
public import SphericalAging.GaussianLandscape
public import Mathlib.Analysis.Normed.Module.FiniteDimension

public section
/-! A genuine nonexpansive Euclidean coefficient cutoff, fixing every
landscape below the chosen bound. Its definition uses actual Hilbert
metric projection onto a closed convex multilinear operator norm ball. -/
noncomputable section
open Set Filter Topology Metric
open scoped NNReal InnerProductSpace BigOperators
namespace SphericalAging.LandscapeMetricProjection
open FiniteModel GaussianLandscape
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}
@[expose] abbrev CoefficientSpace (N p : ℕ) := EuclideanSpace ℝ (TensorIndex N p)

@[expose] def formLinear (N p : ℕ) : CoefficientSpace N p →ₗ[ℝ] TensorForm N p where
  toFun := fun J => tensorForm N p J.ofLp
  map_add' J K := by
    classical
    simp only [WithLp.ofLp_add,tensorForm,Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' a J := by
    classical
    simp only [WithLp.ofLp_smul,tensorForm,Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum,RingHom.id_apply]

@[expose] def formOperator (N p : ℕ) : CoefficientSpace N p →L[ℝ] TensorForm N p :=
  (formLinear N p).toContinuousLinearMap

@[simp] theorem formOperator_apply (N p : ℕ) (J : CoefficientSpace N p) :
    formOperator N p J=tensorForm N p J.ofLp := rfl

@[expose] def goodSet (N p : ℕ) (A : ℝ≥0) : Set (CoefficientSpace N p) :=
  (formOperator N p) ⁻¹' closedBall 0 ((A : ℝ)*Real.sqrt N)

theorem goodSet_closed (N p : ℕ) (A : ℝ≥0) : IsClosed (goodSet N p A) :=
  isClosed_closedBall.preimage (formOperator N p).continuous

theorem goodSet_convex (N p : ℕ) (A : ℝ≥0) : Convex ℝ (goodSet N p A) := by
  change Convex ℝ ((formLinear N p) ⁻¹' closedBall 0 ((A : ℝ)*Real.sqrt N))
  exact (convex_closedBall (0 : TensorForm N p) ((A : ℝ)*Real.sqrt N)).linear_preimage (formLinear N p)

theorem goodSet_nonempty (N p : ℕ) (A : ℝ≥0) : (goodSet N p A).Nonempty := by
  refine ⟨0,?_⟩
  simp only [goodSet,mem_preimage,map_zero,mem_closedBall,dist_self]
  positivity

@[expose] def project (N p : ℕ) (A : ℝ≥0) : CoefficientSpace N p → CoefficientSpace N p :=
  ConvexMetricProjection.project (goodSet N p A) (goodSet_closed N p A)
    (goodSet_convex N p A) (goodSet_nonempty N p A)

theorem project_lipschitz (N p : ℕ) (A : ℝ≥0) : LipschitzWith 1 (project N p A) :=
  ConvexMetricProjection.project_lipschitz _ _ _ _

theorem project_continuous (N p : ℕ) (A : ℝ≥0) : Continuous (project N p A) :=
  (project_lipschitz N p A).continuous

theorem project_measurable (N p : ℕ) (A : ℝ≥0) : Measurable (project N p A) :=
  (project_continuous N p A).measurable

theorem project_mem (N p : ℕ) (A : ℝ≥0) (J : CoefficientSpace N p) : project N p A J∈goodSet N p A :=
  ConvexMetricProjection.project_mem _ _ _ _ _

theorem goodSet_iff (hN : 0<N) (p : ℕ) (A : ℝ≥0) (J : CoefficientSpace N p) :
    J∈goodSet N p A ↔ landscapeNorm N p J.ofLp≤A := by
  have hr : 0<Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  simp only [goodSet,mem_preimage,mem_closedBall,dist_zero_right,formOperator_apply,landscapeNorm]
  exact (div_le_iff₀ hr).symm

theorem project_landscape_le (hN : 0<N) (p : ℕ) (A : ℝ≥0) (J : CoefficientSpace N p) :
    landscapeNorm N p (project N p A J).ofLp≤A :=
  (goodSet_iff hN p A _).mp (project_mem N p A J)

theorem project_eq_self (hN : 0<N) (p : ℕ) (A : ℝ≥0) (J : CoefficientSpace N p)
    (hJ : landscapeNorm N p J.ofLp≤A) : project N p A J=J :=
  ConvexMetricProjection.project_eq_self _ _ _ _ ((goodSet_iff hN p A J).mpr hJ)

@[expose] def cutoff (N p : ℕ) (A : ℝ≥0) (J : Disorder N p) : Disorder N p :=
  (project N p A (WithLp.toLp 2 J)).ofLp

theorem cutoff_measurable (N p : ℕ) (A : ℝ≥0) : Measurable (cutoff N p A) :=
  ((PiLp.continuous_ofLp 2 (fun _ : TensorIndex N p => ℝ)).comp
    ((project_continuous N p A).comp (PiLp.continuous_toLp 2 (fun _ : TensorIndex N p => ℝ)))).measurable

theorem cutoff_landscape_le (hN : 0<N) (p : ℕ) (A : ℝ≥0) (J : Disorder N p) :
    landscapeNorm N p (cutoff N p A J)≤A := project_landscape_le hN p A _

theorem cutoff_eq_self (hN : 0<N) (p : ℕ) (A : ℝ≥0) (J : Disorder N p)
    (hJ : landscapeNorm N p J≤A) : cutoff N p A J=J := by
  unfold cutoff
  rw [project_eq_self hN p A _ hJ]
end SphericalAging.LandscapeMetricProjection
