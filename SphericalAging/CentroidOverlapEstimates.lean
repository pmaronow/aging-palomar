module

public import SphericalAging.RegularTreeCentroidGeometry

public section

/-! Literal finite-average overlap estimates used in HS Appendix A.5. -/
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.CentroidOverlapEstimates
open FiniteModel OrthogonalForkCentroid RegularTreeCentroidGeometry
open scoped BigOperators InnerProductSpace
variable {N K : ℕ}

@[expose] def overlap (x y : Vector N) : ℝ := ⟪x,y⟫_ℝ/(N:ℝ)

theorem average_deviation_le (hK : 0<K) (f : Fin K→ℝ) (r : ℝ) :
    |(∑i,f i)/(K:ℝ)-r|≤(∑i,|f i-r|)/(K:ℝ) := by
  have hk : 0<(K:ℝ) := Nat.cast_pos.mpr hK
  have heq : (∑i,f i)/(K:ℝ)-r=(∑i,(f i-r))/(K:ℝ) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  rw [heq,abs_div,abs_of_pos hk]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hk.le

theorem average_deviation_bound (hK : 0<K) (f : Fin K→ℝ) (r η : ℝ)
    (h : ∀i,|f i-r|≤η) : |(∑i,f i)/(K:ℝ)-r|≤η := by
  have hk : 0<(K:ℝ) := Nat.cast_pos.mpr hK
  calc
    _≤(∑i,|f i-r|)/(K:ℝ) := average_deviation_le hK f r
    _≤(∑_i : Fin K,η)/(K:ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => h i)) hk.le
    _=η := by simp [hk.ne']

theorem overlap_centroid_left (a : Fin K→Vector N) (b : Vector N) :
    overlap (centroid a) b=(∑i,overlap (a i) b)/(K:ℝ) := by
  unfold overlap centroid
  rw [inner_smul_left,sum_inner]
  simp only [conj_trivial]
  rw [←Finset.sum_div]
  ring

theorem overlap_centroid_right (a : Vector N) (b : Fin K→Vector N) :
    overlap a (centroid b)=(∑i,overlap a (b i))/(K:ℝ) := by
  unfold overlap centroid
  rw [inner_smul_right,inner_sum]
  rw [←Finset.sum_div]
  ring

theorem overlap_centroids_bound (hK : 0<K) (a b : Fin K→Vector N) (r η : ℝ)
    (h : ∀i j,|overlap (a i) (b j)-r|≤η) :
    |overlap (centroid a) (centroid b)-r|≤η := by
  rw [overlap_centroid_left]
  apply average_deviation_bound hK
  intro i
  rw [overlap_centroid_right]
  exact average_deviation_bound hK _ r η (h i)

theorem overlap_abs_le_one (hN : 0<N) (x y : Vector N)
    (hx : ‖x‖≤Real.sqrt N) (hy : ‖y‖≤Real.sqrt N) : |overlap x y|≤1 := by
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hi : |⟪x,y⟫_ℝ|≤(N:ℝ) := by
    calc
      _≤‖x‖*‖y‖ := abs_real_inner_le_norm x y
      _≤Real.sqrt N*Real.sqrt N :=
        mul_le_mul hx hy (norm_nonneg y) (Real.sqrt_nonneg N)
      _=(N:ℝ) := Real.mul_self_sqrt hn.le
  unfold overlap
  rw [abs_div,abs_of_pos hn]
  exact (div_le_one hn).mpr hi

theorem overlap_deviation_le_two (hN : 0<N) (x y : Vector N)
    (hx : ‖x‖≤Real.sqrt N) (hy : ‖y‖≤Real.sqrt N)
    (r : ℝ) (hr0 : 0≤r) (hr1 : r≤1) : |overlap x y-r|≤2 := by
  have hi := overlap_abs_le_one hN x y hx hy
  calc
    _≤|overlap x y|+|r| := abs_sub _ _
    _≤1+1 := add_le_add hi (by rwa [abs_of_nonneg hr0])
    _=2 := by norm_num

/-- A single exceptional diagonal contributes at most 2/K to the child-parent overlap. -/
theorem child_parent_overlap_bound (hN : 0<N) (hK : 0<K)
    (a : Fin K→Vector N) (ha : ∀i,‖a i‖≤Real.sqrt N)
    (r η : ℝ) (hr0 : 0≤r) (hr1 : r≤1) (hη : 0≤η)
    (hcross : ∀i j,i≠j→|overlap (a i) (a j)-r|≤η) (i : Fin K) :
    |overlap (a i) (centroid a)-r|≤η+2/(K:ℝ) := by
  classical
  have hk : 0<(K:ℝ) := Nat.cast_pos.mpr hK
  rw [overlap_centroid_right]
  calc
    _≤(∑j,|overlap (a i) (a j)-r|)/(K:ℝ) := average_deviation_le hK _ r
    _≤(∑j : Fin K,(η+(if i=j then 2 else 0)))/(K:ℝ) := by
      apply div_le_div_of_nonneg_right _ hk.le
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i=j
      · subst j
        simpa using (overlap_deviation_le_two hN (a i) (a i) (ha i) (ha i) r hr0 hr1).trans
          (by linarith : (2:ℝ)≤η+2)
      · simpa only [if_neg hij,add_zero] using hcross i j hij
    _=η+2/(K:ℝ) := by
      rw [Finset.sum_add_distrib]
      simp [hk.ne',add_div]

theorem parent_self_overlap_bound (hN : 0<N) (hK : 0<K)
    (a : Fin K→Vector N) (ha : ∀i,‖a i‖≤Real.sqrt N)
    (r η : ℝ) (hr0 : 0≤r) (hr1 : r≤1) (hη : 0≤η)
    (hcross : ∀i j,i≠j→|overlap (a i) (a j)-r|≤η) :
    |overlap (centroid a) (centroid a)-r|≤η+2/(K:ℝ) := by
  rw [overlap_centroid_left]
  exact average_deviation_bound hK _ _ _
    (child_parent_overlap_bound hN hK a ha r η hr0 hr1 hη hcross)

end SphericalAging.CentroidOverlapEstimates
