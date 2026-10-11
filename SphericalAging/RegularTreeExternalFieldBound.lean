module

public import SphericalAging.RegularTreeCentroidGeometry

public section

/-! The literal external-field term in HS Proposition 3.3 is controlled by
the actual root norm and the proven root-to-leaf-centroid displacement. -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.RegularTreeExternalFieldBound
open FiniteModel RegularTreeEnergyTelescoping RegularTreeCentroidGeometry
open scoped BigOperators InnerProductSpace
variable {N K : ℕ}

theorem leafMean_inner_eq (hK : 0<K) (h : Vector N) (d : ℕ)
    (z : TreeData (Vector N) K d) :
    leafMean d (map (fun x => ⟪h,x⟫_ℝ) d z)=⟪h,leafCentroid d z⟫_ℝ := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change (∑i,leafMean d (map (fun x => ⟪h,x⟫_ℝ) d (z.2 i)))/(K:ℝ)=
      ⟪h,OrthogonalForkCentroid.centroid (fun i => leafCentroid d (z.2 i))⟫_ℝ
    simp_rw [ih]
    rw [OrthogonalForkCentroid.centroid,inner_smul_right,inner_sum]
    ring

theorem root_norm_eq_sqrt (x : Vector N) (q : ℝ) (hq : 0≤q)
    (hx : ‖x‖^2=(N:ℝ)*q) : ‖x‖=Real.sqrt N*Real.sqrt q := by
  have hs : (Real.sqrt N*Real.sqrt q)^2=(N:ℝ)*q := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N),Real.sq_sqrt hq]
  have hp : 0≤Real.sqrt N*Real.sqrt q := by positivity
  nlinarith [norm_nonneg x]

theorem actual_external_field_bound (hN : 0<N) (hK : 0<K) (q : ℕ→ℝ)
    (hq : Monotone q) (d : ℕ) (hq0 : 0≤q 0) (hqd : q d≤1)
    (z : TreeData (Vector N) K d) (hz : ForkTree q d z)
    (hroot : ‖root d z‖^2=(N:ℝ)*q 0)
    (h : Vector N) (H : ℝ) (hH : 0≤H) (hnorm : ‖h‖≤Real.sqrt N*H) :
    leafMean d (map (fun x => ⟪h,x⟫_ℝ) d z)/(N:ℝ)≤
      H*Real.sqrt (q 0)+H*Real.sqrt ((d:ℝ)/(K:ℝ)) := by
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hn
  have hcent := actual_source_HS_2_9 hN hK q hq d hq0 hqd z hz
  have hdist : ‖leafCentroid d z-root d z‖≤Real.sqrt N*Real.sqrt ((d:ℝ)/(K:ℝ)) := by
    have hh := (div_le_iff₀ hs).mp hcent
    simpa only [mul_comm] using hh
  have hleaf : ‖leafCentroid d z‖≤Real.sqrt N*(Real.sqrt (q 0)+Real.sqrt ((d:ℝ)/(K:ℝ))) := by
    calc
      _≤‖leafCentroid d z-root d z‖+‖root d z‖ := by
        simpa only [sub_add_cancel] using norm_add_le (leafCentroid d z-root d z) (root d z)
      _≤Real.sqrt N*Real.sqrt ((d:ℝ)/(K:ℝ))+Real.sqrt N*Real.sqrt (q 0) := by
        rw [root_norm_eq_sqrt _ _ hq0 hroot]
        exact add_le_add_left hdist _
      _=_ := by ring
  rw [leafMean_inner_eq hK]
  calc
    _≤(‖h‖*‖leafCentroid d z‖)/(N:ℝ) :=
      div_le_div_of_nonneg_right (real_inner_le_norm _ _) hn.le
    _≤((Real.sqrt N*H)*(Real.sqrt N*(Real.sqrt (q 0)+Real.sqrt ((d:ℝ)/(K:ℝ)))))/(N:ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul hnorm hleaf (norm_nonneg _) (mul_nonneg hs.le hH)) hn.le
    _=_ := by
      have he : (Real.sqrt N*H)*(Real.sqrt N*(Real.sqrt (q 0)+Real.sqrt ((d:ℝ)/(K:ℝ))))=
          (Real.sqrt N)^2*(H*(Real.sqrt (q 0)+Real.sqrt ((d:ℝ)/(K:ℝ)))) := by ring
      rw [he,Real.sq_sqrt hn.le,mul_div_cancel_left₀ _ hn.ne']
      ring

end SphericalAging.RegularTreeExternalFieldBound
