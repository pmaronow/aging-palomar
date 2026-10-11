module

public import SphericalAging.DyadicContinuousChaining
public import SphericalAging.FiniteFourthExceedance

public section

/-! Fourth moments of adjacent dyadic increments give uniform compact
sample-path control outside a quantitatively small event. -/
noncomputable section
open Set MeasureTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.DyadicProcessGoodEvent
open DyadicContinuousChaining FiniteFourthExceedance
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω} [IsFiniteMeasure P]
set_option maxHeartbeats 800000

@[expose] def badGrid (X : ℝ≥0→Ω→E) (T : ℝ≥0) (r : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∃k : Fin (2^n),r^n < ‖X (uniformPartitionTime T (2^n) (k.val+1)) ω-
    X (uniformPartitionTime T (2^n) k.val) ω‖}

@[expose] def badTail (X : ℝ≥0→Ω→E) (T : ℝ≥0) (r : ℝ) (m : ℕ) : Set Ω :=
  ⋃j : ℕ,badGrid X T r (m+j+1)

theorem geometric_fourth_ratio (B r : ℝ) (hr : 0 < r) (n : ℕ) :
    (2^n:ℝ)*(B/(2^n:ℝ)^2)/(r^n)^4 = B*(1/(2*r^4))^n := by
  have hp : (r^n)^4=(r^4)^n := by rw [←pow_mul,←pow_mul,Nat.mul_comm n 4]
  rw [hp,div_pow,mul_pow]
  field_simp
  <;> ring

theorem badGrid_measure_le (X : ℝ≥0→Ω→E) (T : ℝ≥0) (r B : ℝ)
    (hr : 0 < r) (n : ℕ)
    (hmem : ∀k : Fin (2^n),MemLp (fun ω => X (uniformPartitionTime T (2^n) (k.val+1)) ω-
      X (uniformPartitionTime T (2^n) k.val) ω) 4 P)
    (hmoment : ∀k : Fin (2^n),(∫ω,‖X (uniformPartitionTime T (2^n) (k.val+1)) ω-
      X (uniformPartitionTime T (2^n) k.val) ω‖^4 ∂P) ≤ B/(2^n:ℝ)^2) :
    P (badGrid X T r n) ≤ ENNReal.ofReal (B*(1/(2*r^4))^n) := by
  have hh := finite_exceedance_le
    (fun k : Fin (2^n) => fun ω => X (uniformPartitionTime T (2^n) (k.val+1)) ω-
      X (uniformPartitionTime T (2^n) k.val) ω) hmem (pow_pos hr n) hmoment
  simpa only [badGrid,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,geometric_fourth_ratio B r hr n] using hh

theorem badTail_measure_le (X : ℝ≥0→Ω→E) (T : ℝ≥0) (r B : ℝ)
    (hB : 0 ≤ B) (hr : 0 < r) (hq : 1/(2*r^4) < 1) (m : ℕ)
    (hgrid : ∀n,P (badGrid X T r n) ≤ ENNReal.ofReal (B*(1/(2*r^4))^n)) :
    P (badTail X T r m) ≤ ENNReal.ofReal (B*(1/(2*r^4))^(m+1)/(1-1/(2*r^4))) := by
  let q : ℝ := 1/(2*r^4)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqn : ‖q‖ < 1 := by simpa only [Real.norm_of_nonneg hq0] using hq
  have hgeom := summable_geometric_of_norm_lt_one hqn
  have hs : Summable (fun j : ℕ => B*q^(m+j+1)) := by
    have hh := hgeom.mul_left (B*q^(m+1))
    simpa only [pow_add,mul_assoc,mul_left_comm,mul_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
  unfold badTail
  refine (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum (fun j => hgrid (m+j+1))).trans_eq ?_)
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg hB (pow_nonneg hq0 _)) hs]
  congr 1
  calc
    (∑'j : ℕ,B*q^(m+j+1)) = ∑'j : ℕ,(B*q^(m+1))*q^j := by
      congr 1
      funext j
      rw [show m+j+1=(m+1)+j by omega,pow_add,mul_assoc]
    _ = B*q^(m+1)*(1-q)⁻¹ := by rw [tsum_mul_left,tsum_geometric_of_norm_lt_one hqn]
    _ = _ := by rfl

theorem path_distance_to_grid_on_good {X : ℝ≥0→Ω→E} {T : ℝ≥0} {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) {m : ℕ} {ω : Ω}
    (hω : ω ∉ badTail X T r m) (hcts : Continuous (fun t => X t ω))
    (s : ℝ≥0) (hs : s ≤ T) :
    ‖X (timeApprox T m s) ω-X s ω‖ ≤ r^(m+1)/(1-r) := by
  have hgeom : Summable (fun n : ℕ => r^n) :=
    summable_geometric_of_norm_lt_one (by simpa only [Real.norm_of_nonneg hr] using hr1)
  have hsumm : Summable (fun j : ℕ => r^(m+j+1)) := by
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (summable_nat_add_iff (f:=fun n : ℕ => r^n) (m+1)).mpr hgeom
  have hstep (n k : ℕ) (hk : k < 2^(m+n+1)) :
      dist (X (uniformPartitionTime T (2^(m+n+1)) k) ω)
        (X (uniformPartitionTime T (2^(m+n+1)) (k+1)) ω) ≤ r^(m+n+1) := by
    have hn : ω ∉ badGrid X T r (m+n+1) := fun h => hω (mem_iUnion.mpr ⟨n,h⟩)
    have he := not_lt.mp (fun h => hn ⟨⟨k,hk⟩,h⟩)
    simpa only [dist_eq_norm, norm_sub_rev] using he
  -- A shifted path estimate only needs the increment levels above the selected grid.
  have hb (i : ℕ) : dist (X (timeApprox T m s) ω) (X (timeApprox T (m+i) s) ω) ≤
      ∑'j : ℕ,r^(m+j+1) := by
    have hh := dist_le_range_sum_of_dist_le (f:=fun j : ℕ => X (timeApprox T (m+j) s) ω) i
      (d:=fun j : ℕ => r^(m+j+1)) (fun {j} _ => by
        simpa only [Nat.add_assoc] using
          timeApprox_step_le (fun t => X t ω) T s hs (m+j) (r^(m+j+1))
            (pow_nonneg hr _) (hstep j))
    simp only [Nat.add_zero] at hh
    exact hh.trans (hsumm.sum_le_tsum (Finset.range i) (fun j _ => pow_nonneg hr _))
  have ht : Tendsto (fun i : ℕ => X (timeApprox T (m+i) s) ω) atTop (𝓝 (X s ω)) :=
    hcts.continuousAt.tendsto.comp ((tendsto_uniformPartitionTime_dyadicApproxIndex hs).comp
      (by simpa only [Nat.add_comm] using (tendsto_add_atTop_nat m)))
  have he := le_of_tendsto (tendsto_const_nhds.dist ht) (.of_forall hb)
  rw [dist_eq_norm] at he
  refine he.trans_eq ?_
  calc
    (∑'j : ℕ,r^(m+j+1)) = ∑'j : ℕ,r^(m+1)*r^j := by
      congr 1
      funext j
      rw [show m+j+1=(m+1)+j by omega,pow_add]
    _ = _ := by rw [tsum_mul_left,tsum_geometric_of_norm_lt_one (by simpa only [Real.norm_of_nonneg hr] using hr1),div_eq_mul_inv]

end SphericalAging.DyadicProcessGoodEvent
