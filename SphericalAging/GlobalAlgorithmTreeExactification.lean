module

public import SphericalAging.FiniteTreeSeparation
public import SphericalAging.RegularTreeEdgeList

public section

/-! Correct a fixed small-branching subtree of the genuine large-branching
leaf constellation. Full-tree centroids supply the internal vertices, so
only the original large branching enters their approximation error. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GlobalAlgorithmTreeExactification
open FiniteModel RegularTreeEnergyTelescoping RegularTreeGlobalToLocal RegularTreeCentroidGeometry
open RegularTreeHighEnergyPruning RegularTreeEdgeList FiniteTreeSeparation
open FiniteTreeCommonOrthogonalDirection RegularTreeExactApproximation TreeExactificationError
open scoped InnerProductSpace
variable {N K k : ℕ}

theorem prune_barycenter_leaf (d : ℕ) (σ : Selection K k d)
    (z : TreeData (Vector N) K d) (a : Fin d→Fin k) :
    leafAt d (prune d σ (barycenterTree d z)) a=leafAt d (prune d σ z) a := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih (σ.2 (a 0)) (z.2 (σ.1 (a 0))) (fun i => a i.succ)

theorem allLeaves_prune (P : Vector N→Prop) (d : ℕ) (σ : Selection K k d)
    (z : TreeData (Vector N) K d) (hz : RegularTreeGlobalToLocal.AllLeaves P d z) :
    RegularTreeGlobalToLocal.AllLeaves P d (prune d σ z) := by
  induction d with
  | zero => exact hz
  | succ d ih => exact fun i => ih (σ.2 i) (z.2 (σ.1 i)) (hz (σ.1 i))

theorem fork_allLeaves_ball (q : ℕ→ℝ) (d : ℕ) (w : TreeData (Vector N) k d)
    (hw : ForkTree q d w) (hn : ‖root d w‖^2=(N:ℝ)*q 0) (hq : q d≤1) :
    RegularTreeGlobalToLocal.AllLeaves (fun x => ‖x‖≤Real.sqrt N) d w := by
  induction d generalizing q with
  | zero =>
    change ‖(show Vector N from w)‖≤Real.sqrt N
    change ‖(show Vector N from w)‖^2=(N:ℝ)*q 0 at hn
    have hh := mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg N)
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg N),norm_nonneg (show Vector N from w),Real.sqrt_nonneg (N:ℝ)]
  | succ d ih =>
    intro i
    exact ih (fun l => q (l+1)) (w.2 i) (hw.2 i) (hw.1.leaf_norm i) hq

theorem actual_global_to_exact_fixed_subtree (hN : 0<N) (hK : 0<K) (hkn : k<N)
    (d : ℕ) (hDim : nodeCount k d<N) (σ : Selection K k d)
    (q : ℕ→ℝ) (hq : Monotone q) (hr : ∀l,q l∈Set.Icc (0:ℝ) 1)
    (ε δ : ℝ) (hε : 0≤ε) (hδ : δ∈Set.Ioc (0:ℝ) 1)
    (hsmall : SmallConditions k d δ ((1-δ)*(ε+2/(K:ℝ))))
    (z : TreeData (Vector N) K d) (hz : GlobalOverlapTree q ε d z) :
    ∃w : TreeData (Vector N) k d,
      ForkTree (fun l => separatedOverlap δ (q l)) d w ∧
      ‖root d w‖^2=(N:ℝ)*separatedOverlap δ (q 0) ∧
      RegularTreeGlobalToLocal.AllLeaves (fun x => ‖x‖≤Real.sqrt N) d w ∧
      ∀a : Fin d→Fin k,‖leafAt d w a-leafAt d (prune d σ z) a‖/Real.sqrt N≤
        2*Real.sqrt δ+correctionError k ((1-δ)*(ε+2/(K:ℝ))) d := by
  let zh := prune d σ (barycenterTree d z)
  let qs := fun l => separatedOverlap δ (q l)
  let η := (1-δ)*(ε+2/(K:ℝ))
  have hl : LocalOverlapTree q (ε+2/(K:ℝ)) d zh :=
    local_prune q _ d σ _ (actual_source_HS_A_5 hN hK q hr ε hε d z hz)
  have hδc : δ∈Set.Icc (0:ℝ) 1 := ⟨hδ.1.le,hδ.2⟩
  obtain ⟨zs,hzs,hclose⟩ := actual_finite_tree_separation hN δ hδc q _ d hDim zh hl
  have hqs : Monotone qs := by
    intro i j hij
    exact add_le_add_left (mul_le_mul_of_nonneg_left (hq hij) (sub_nonneg.mpr hδ.2)) δ
  have hlow : ∀l,δ≤qs l := by
    intro l
    have hh := mul_nonneg (sub_nonneg.mpr hδ.2) (hr l).1
    dsimp [qs,separatedOverlap]
    linarith
  obtain ⟨w,hw,hn,hd⟩ := actual_source_HS_A_3_geometry hN hkn δ η hδ.1 qs hqs hlow d hsmall zs hzs
  have hqD : qs d≤1 := by
    have hh := mul_le_mul_of_nonneg_left (hr d).2 (sub_nonneg.mpr hδ.2)
    dsimp [qs,separatedOverlap]
    linarith
  refine ⟨w,hw,hn,fork_allLeaves_ball qs d w hw hn hqD,?_⟩
  intro a
  have hc := norm_sub_le_norm_sub_add_norm_sub (leafAt d w a) (leafAt d zs a) (leafAt d zh a)
  have hh := div_le_div_of_nonneg_right hc (Real.sqrt_nonneg (N:ℝ))
  rw [add_div] at hh
  have hbound := hh.trans (add_le_add (hd a) (hclose a))
  have he : leafAt d zh a=leafAt d (prune d σ z) a := prune_barycenter_leaf d σ z a
  rw [he] at hbound
  simpa only [add_comm] using hbound

end SphericalAging.GlobalAlgorithmTreeExactification
