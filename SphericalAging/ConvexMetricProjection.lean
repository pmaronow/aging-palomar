module

public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic

public section
/-! Actual metric projection onto closed convex Hilbert-space sets.
The map is nonexpansive, continuous and fixes every point in the set. -/
noncomputable section
open Set Filter Topology
open scoped InnerProductSpace
namespace SphericalAging.ConvexMetricProjection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (K : Set E) (hclosed : IsClosed K) (hconvex : Convex ℝ K) (hne : K.Nonempty)

@[expose] def project (x : E) : E :=
  (exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconvex x).choose

theorem project_mem (x : E) : project K hclosed hconvex hne x∈K :=
  (exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconvex x).choose_spec.1

theorem project_inner_le (x y : E) (hy : y∈K) :
    ⟪x-project K hclosed hconvex hne x,y-project K hclosed hconvex hne x⟫_ℝ≤0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hconvex (project_mem K hclosed hconvex hne x)).mp
    (exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconvex x).choose_spec.2 y hy

theorem project_eq_self {x : E} (hx : x∈K) : project K hclosed hconvex hne x=x := by
  have hh := project_inner_le K hclosed hconvex hne x x hx
  rw [real_inner_self_eq_norm_sq] at hh
  have hz : ‖x-project K hclosed hconvex hne x‖=0 := by nlinarith [norm_nonneg (x-project K hclosed hconvex hne x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

theorem project_dist_le (x y : E) :
    dist (project K hclosed hconvex hne x) (project K hclosed hconvex hne y)≤dist x y := by
  let p := project K hclosed hconvex hne x
  let q := project K hclosed hconvex hne y
  let d := p-q
  have hx := project_inner_le K hclosed hconvex hne x q (project_mem K hclosed hconvex hne y)
  have hy := project_inner_le K hclosed hconvex hne y p (project_mem K hclosed hconvex hne x)
  have hx' : 0≤⟪d,x-p⟫_ℝ := by
    change ⟪x-p,q-p⟫_ℝ≤0 at hx
    have he : q-p= -d := by dsimp [d];abel
    rw [he,inner_neg_right,real_inner_comm] at hx
    linarith
  have hy' : 0≤⟪d,q-y⟫_ℝ := by
    change ⟪y-q,d⟫_ℝ≤0 at hy
    rw [show q-y= -(y-q) by abel,inner_neg_right,real_inner_comm]
    linarith
  have he : x-y=(x-p)+d+(q-y) := by dsimp [d];abel
  have hsq : ‖d‖^2≤⟪d,x-y⟫_ℝ := by
    rw [he,inner_add_right,inner_add_right,real_inner_self_eq_norm_sq]
    linarith
  have hb := hsq.trans ((le_abs_self _).trans (abs_real_inner_le_norm d (x-y)))
  rw [dist_eq_norm,dist_eq_norm]
  change ‖d‖≤‖x-y‖
  by_cases hd : ‖d‖=0
  · rw [hd];exact norm_nonneg _
  · have hp : 0<‖d‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
    rw [pow_two] at hb
    exact le_of_mul_le_mul_left hb hp

theorem project_lipschitz : LipschitzWith 1 (project K hclosed hconvex hne) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one,one_mul] using project_dist_le K hclosed hconvex hne x y

theorem project_continuous : Continuous (project K hclosed hconvex hne) :=
  (project_lipschitz K hclosed hconvex hne).continuous
end SphericalAging.ConvexMetricProjection
