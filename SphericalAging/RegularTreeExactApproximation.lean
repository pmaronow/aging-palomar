module

public import SphericalAging.RegularTreeExactification
public import SphericalAging.TreeExactificationError

public section

/-! Actual HS A.3 geometric exactification. An original locally constrained
finite tree is perturbed into a literal orthogonal fork tree, uniformly in
ambient dimension, with an explicitly constructed error tending to zero. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.RegularTreeExactApproximation
open FiniteModel RegularTreeEnergyTelescoping RegularTreeGlobalToLocal RegularTreeCentroidGeometry
open UnitRegularTreeGeometry RegularTreeExactification TreeExactificationError
open NormedVectorRescaling RegularTreePathGeometry GaussianOrthogonalForkCovariance
open scoped InnerProductSpace Topology
variable {N K : ℕ}

theorem actual_unit_tree_exactification (hKN : K<N) (qmin η : ℝ) (hmin : 0<qmin)
    (q : ℕ→ℝ) (hq : Monotone q) (hqlow : ∀l,qmin≤q l) (d : ℕ)
    (hsmall : SmallConditions K d qmin η)
    (z : TreeData (Vector N) K d) (hz : ApproximateTree q η d z) :
    ∃w : TreeData (Vector N) K d,ExactTree q d w ∧
      TreeDistance (correctionError K η) d z w := by
  have hq0 : 0<q 0 := hmin.trans_le (hqlow 0)
  have hnorm := approximate_root_norm q η d z hz
  have hne : root d z≠0 := by
    intro hzero
    rw [hzero,norm_zero,zero_pow (by omega),zero_sub,abs_neg,abs_of_pos hq0] at hnorm
    linarith [hqlow 0,hsmall.2.1]
  let τ := rescale (q 0) (root d z)
  have hτ : ‖τ‖^2=q 0 := by
    rw [rescale_norm _ _ hne,Real.sq_sqrt hq0.le]
  have hclose : ‖τ-root d z‖≤correctionError K η 0 := by
    rw [rescale_distance_self _ _ hne]
    have hh := nonnegative_square_difference (Real.sqrt (q 0)) ‖root d z‖ η
      (Real.sqrt_nonneg _) (norm_nonneg _) hsmall.1
      (by rw [Real.sq_sqrt hq0.le,abs_sub_comm];exact hnorm)
    exact hh
  obtain ⟨w,hwe,hwd,_⟩ := exists_correction_at_root hKN qmin η hmin hsmall.1 q
    (correctionError K η) hq hqlow (correctionError_nonneg K η) d
    (fun _ _ => rfl) (fun l hl => (hsmall.2.2 l hl).1) (fun l hl => (hsmall.2.2 l hl).2)
    z hz τ hτ hclose
  exact ⟨w,hwe,hwd⟩

private theorem scale_norm_sq (x : Vector N) :
    ‖Real.sqrt N • x‖^2=(N:ℝ)*‖x‖^2 := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg N)]

theorem scale_exactTree (q : ℕ→ℝ) (d : ℕ) (z : TreeData (Vector N) K d)
    (hz : ExactTree q d z) : ForkTree q d (map (fun x : Vector N => Real.sqrt N • x) d z) ∧
      ‖root d (map (fun x : Vector N => Real.sqrt N • x) d z)‖^2=(N:ℝ)*q 0 := by
  have hn := exact_root_norm q d z hz
  have hroot : ‖root d (map (fun x : Vector N => Real.sqrt N • x) d z)‖^2=(N:ℝ)*q 0 := by
    rw [root_map,scale_norm_sq,hn]
  refine ⟨?_,hroot⟩
  clear hn hroot
  induction d generalizing q with
  | zero => trivial
  | succ d ih =>
    simp only [map,ForkTree,root_map]
    refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
    · rw [scale_norm_sq,hz.1]
    · intro i;rw [scale_norm_sq,hz.2.1 i]
    · intro i
      rw [←smul_sub,real_inner_smul_left,real_inner_smul_right,hz.2.2.1 i,mul_zero,mul_zero]
    · intro i j hij
      rw [←smul_sub,←smul_sub,real_inner_smul_left,real_inner_smul_right,hz.2.2.2.1 i j hij,mul_zero,mul_zero]
    · intro i;exact ih (fun l => q (l+1)) (z.2 i) (hz.2.2.2.2 i)

theorem leafAt_map (f : Vector N→Vector N) : ∀d (z : TreeData (Vector N) K d) (a : Fin d→Fin K),
    leafAt d (map f d z) a=f (leafAt d z a) := by
  intro d
  induction d with
  | zero => intros;rfl
  | succ d ih => intros;exact ih _ _

private theorem scale_normalizedVertex (hN : 0<N) (x : Vector N) :
    Real.sqrt N • normalizedVertex x=x := by
  have hs : Real.sqrt (N:ℝ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'
  rw [normalizedVertex,smul_smul,mul_inv_cancel₀ hs,one_smul]

theorem actual_source_HS_A_3_geometry (hN : 0<N) (hKN : K<N) (qmin η : ℝ)
    (hmin : 0<qmin) (q : ℕ→ℝ) (hq : Monotone q) (hqlow : ∀l,qmin≤q l)
    (d : ℕ) (hsmall : SmallConditions K d qmin η)
    (z : TreeData (Vector N) K d) (hz : LocalOverlapTree q η d z) :
    ∃w : TreeData (Vector N) K d,ForkTree q d w ∧
      ‖root d w‖^2=(N:ℝ)*q 0 ∧
      ∀a : Fin d→Fin K,‖leafAt d w a-leafAt d z a‖/Real.sqrt N≤correctionError K η d := by
  let zn := map normalizedVertex d z
  have hzn : ApproximateTree q η d zn := normalize_approximateTree hN q η d z hz
  obtain ⟨wn,hwn,hwd⟩ := actual_unit_tree_exactification hKN qmin η hmin q hq hqlow d hsmall zn hzn
  let w := map (fun x : Vector N => Real.sqrt N • x) d wn
  have hw := scale_exactTree q d wn hwn
  refine ⟨w,hw.1,hw.2,?_⟩
  intro a
  have hd := leaf_distance (correctionError K η) d zn wn hwd a
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have heq : leafAt d w a-leafAt d z a=
      Real.sqrt N • (leafAt d wn a-leafAt d zn a) := by
    rw [smul_sub,show leafAt d zn a=normalizedVertex (leafAt d z a) from leafAt_map normalizedVertex d z a,
      scale_normalizedVertex hN]
    change leafAt d (map (fun x : Vector N => Real.sqrt N • x) d wn) a-leafAt d z a=_
    rw [leafAt_map]
  rw [heq,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs.le,mul_div_cancel_left₀ _ hs.ne']
  exact hd

end SphericalAging.RegularTreeExactApproximation
