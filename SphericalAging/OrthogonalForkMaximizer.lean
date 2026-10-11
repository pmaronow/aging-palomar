module

public import SphericalAging.OrthogonalForkNonempty
public import SphericalAging.OrthogonalForkSupremumTransport
public import Mathlib.Topology.Order.Compact

public section

/-! The genuine compact orthogonal-fork domain and attainment of its
actual Hamiltonian increment supremum. No maximizer is supplied as data. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.OrthogonalForkMaximizer
open Set MeasureTheory FiniteModel GaussianOrthogonalForkCovariance
open OrthogonalForkNonempty OrthogonalForkSupremumTransport
open scoped BigOperators InnerProductSpace
variable {N p K : ℕ}

@[expose] def forkSet (x : Vector N) (r q : ℝ) : Set (Fin K→Vector N) :=
  {y | OrthogonalFork x y r q}

theorem forkSet_isClosed (x : Vector N) (r q : ℝ) : IsClosed (forkSet (K:=K) x r q) := by
  have heq : forkSet (K:=K) x r q=
      {y | ‖x‖^2=(N:ℝ)*r}∩
        (⋂i,{y | ‖y i‖^2=(N:ℝ)*q})∩
        (⋂i,{y | ⟪y i-x,x⟫_ℝ=0})∩
        (⋂i,⋂j,⋂_h : i≠j,{y | ⟪y i-x,y j-x⟫_ℝ=0}) := by
    ext y
    simp only [forkSet,mem_setOf_eq,mem_inter_iff,mem_iInter]
    exact ⟨fun h => ⟨⟨⟨h.base_norm,h.leaf_norm⟩,h.increment_base⟩,h.increment_orthogonal⟩,
      fun h => ⟨h.1.1.1,h.1.1.2,h.1.2,h.2⟩⟩
  rw [heq]
  refine (((isClosed_eq continuous_const continuous_const).inter ?_).inter ?_).inter ?_
  · exact isClosed_iInter (fun i => isClosed_eq ((continuous_apply i).norm.pow 2) continuous_const)
  · exact isClosed_iInter (fun i => isClosed_eq
      (((continuous_apply i).sub continuous_const).inner continuous_const) continuous_const)
  · exact isClosed_iInter (fun i => isClosed_iInter (fun j => isClosed_iInter (fun _ =>
      isClosed_eq (((continuous_apply i).sub continuous_const).inner
        ((continuous_apply j).sub continuous_const)) continuous_const)))

theorem forkSet_isCompact (x : Vector N) (r q : ℝ) (hq : 0≤q) :
    IsCompact (forkSet (K:=K) x r q) := by
  apply Metric.isCompact_of_isClosed_isBounded (forkSet_isClosed x r q)
  apply (isBounded_iff_forall_norm_le).2
  refine ⟨Real.sqrt ((N:ℝ)*q),?_⟩
  intro y hy
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro i
  exact Real.le_sqrt_of_sq_le (hy.leaf_norm i).le

theorem averagedIncrement_continuous (a b : ℝ) (x : Vector N) (J : ForkDisorder N p K) :
    Continuous (fun y : Fin K→Vector N => averagedIncrement a b x y J) := by
  unfold averagedIncrement increment sharedIncrement block
  refine (continuous_finset_sum _ (fun i _ => ?_)).div_const _
  exact (continuous_const.mul (((Hamiltonian_contDiff (J none)).continuous.comp
    (continuous_apply i)).sub continuous_const)).add
      (continuous_const.mul ((Hamiltonian_contDiff (J (some i))).continuous.comp (continuous_apply i)))

theorem actual_fork_maximizer (hN : 0<N) (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (a b r q : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hr : 0≤r) (hrq : r≤q) (hq1 : q≤1) (x : Vector N) (hx : ‖x‖^2=(N:ℝ)*r)
    (J : ForkDisorder N p K) :
    ∃y : Fin K→Vector N,OrthogonalFork x y r q ∧ averagedIncrement a b x y J=
      GaussianFixedBaseForkConcentration.supremum a b r q x J := by
  obtain ⟨⟨y0,hy0⟩⟩ := leafDomain_nonempty hKN x r q hr hrq hx
  letI : Nonempty (GaussianFixedBaseForkConcentration.LeafDomain N K x r q) := ⟨⟨y0,hy0⟩⟩
  obtain ⟨y,hy,hmax⟩ := (forkSet_isCompact x r q (hr.trans hrq)).exists_isMaxOn ⟨y0,hy0⟩
    (averagedIncrement_continuous a b x J).continuousOn
  refine ⟨y,hy,le_antisymm ?_ ?_⟩
  · exact le_csSup (actual_range_bddAbove hN hp hK a b r q ha hab hb hr (hr.trans hrq) hq1 x J)
      (Set.mem_range_self (⟨y,hy⟩ : GaussianFixedBaseForkConcentration.LeafDomain N K x r q))
  · apply csSup_le (Set.range_nonempty _)
    rintro t ⟨z,rfl⟩
    exact hmax z.property

end SphericalAging.OrthogonalForkMaximizer
