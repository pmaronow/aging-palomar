module

public import SphericalAging.OrthogonalForkCentroid
public import SphericalAging.RegularTreeEnergyTelescoping
public import Mathlib.Algebra.Order.Chebyshev

public section

/-! Actual finite-tree geometry from Huang--Sellke Lemma 2.9. Each local
certificate is a literal orthogonal fork, and the leaf centroid is constructed
by recursively averaging the actual leaves. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.RegularTreeCentroidGeometry
open FiniteModel GaussianOrthogonalForkCovariance OrthogonalForkCentroid
open RegularTreeEnergyTelescoping
open scoped BigOperators InnerProductSpace
variable {N K : ℕ}

@[expose] def leafCentroid : (d : ℕ)→TreeData (Vector N) K d→Vector N
  | 0,z => z
  | d+1,z => centroid (fun i => leafCentroid d (z.2 i))

@[expose] def ForkTree (q : ℕ→ℝ) : (d : ℕ)→TreeData (Vector N) K d→Prop
  | 0,_ => True
  | d+1,z => OrthogonalFork z.1 (fun i => root d (z.2 i)) (q 0) (q 1) ∧
      ∀i,ForkTree (fun l => q (l+1)) d (z.2 i)

@[expose] def budget (K : ℕ) (q : ℕ→ℝ) : ℕ→ℝ
  | 0 => 0
  | d+1 => Real.sqrt ((q 1-q 0)/(K:ℝ))+budget K (fun l => q (l+1)) d

theorem centroid_difference (a b : Fin K→Vector N) :
    centroid a-centroid b=centroid (fun i => a i-b i) := by
  simp only [centroid,Finset.sum_sub_distrib,smul_sub]

theorem centroid_norm_le (hK : 0<K) (a : Fin K→Vector N) (B : ℝ)
    (h : ∀i,‖a i‖≤B) : ‖centroid a‖≤B := by
  have hk : 0<(K:ℝ) := Nat.cast_pos.mpr hK
  calc
    ‖centroid a‖=(K:ℝ)⁻¹*‖∑i,a i‖ := by
      rw [centroid,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hk.le)]
    _≤(K:ℝ)⁻¹*(∑i,‖a i‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hk.le)
    _≤(K:ℝ)⁻¹*(∑_i : Fin K,B) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => h i)) (inv_nonneg.mpr hk.le)
    _=B := by simp [hk.ne']

theorem budget_eq_sum (q : ℕ→ℝ) (d : ℕ) :
    budget K q d=∑l∈Finset.range d,Real.sqrt ((q (l+1)-q l)/(K:ℝ)) := by
  induction d generalizing q with
  | zero => simp [budget]
  | succ d ih =>
    rw [budget,ih,Finset.sum_range_succ']
    simp only [Nat.zero_add,Nat.add_zero]
    ring

theorem leafCentroid_displacement_le (hK : 0<K) (q : ℕ→ℝ) (hq : Monotone q)
    (d : ℕ) (z : TreeData (Vector N) K d) (hz : ForkTree q d z) :
    ‖leafCentroid d z-root d z‖≤Real.sqrt N*budget K q d := by
  induction d generalizing q with
  | zero => simp [leafCentroid,root,budget]
  | succ d ih =>
    obtain ⟨hroot,hchildren⟩ := hz
    have hchild : ∀i,‖leafCentroid d (z.2 i)-root d (z.2 i)‖≤
        Real.sqrt N*budget K (fun l => q (l+1)) d := by
      intro i
      exact ih (fun l => q (l+1)) (fun a b hab => hq (Nat.add_le_add_right hab 1))
        (z.2 i) (hchildren i)
    have havg := centroid_norm_le hK
      (fun i => leafCentroid d (z.2 i)-root d (z.2 i)) _ hchild
    have hlocal := centroid_distance hK hroot (hq (by omega : 0≤1))
    change ‖centroid (fun i => leafCentroid d (z.2 i))-z.1‖≤_
    calc
      _≤‖centroid (fun i => leafCentroid d (z.2 i))-centroid (fun i => root d (z.2 i))‖+
          ‖centroid (fun i => root d (z.2 i))-z.1‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le
          (centroid (fun i => leafCentroid d (z.2 i))-centroid (fun i => root d (z.2 i)))
          (centroid (fun i => root d (z.2 i))-z.1)
      _≤Real.sqrt N*budget K (fun l => q (l+1)) d+
          Real.sqrt N*Real.sqrt ((q 1-q 0)/(K:ℝ)) := by
        rw [centroid_difference,hlocal]
        exact add_le_add_left havg _
      _=Real.sqrt N*budget K q (d+1) := by rw [budget]; ring

theorem sum_gaps (q : ℕ→ℝ) (d : ℕ) :
    ∑l∈Finset.range d,(q (l+1)-q l)=q d-q 0 := by
  induction d with
  | zero => simp
  | succ d ih => rw [Finset.sum_range_succ,ih]; ring

theorem budget_sq_le (hK : 0<K) (q : ℕ→ℝ) (hq : Monotone q)
    (d : ℕ) : (budget K q d)^2≤(d:ℝ)*(q d-q 0)/(K:ℝ) := by
  rw [budget_eq_sum]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range d)
    (f := fun l => Real.sqrt ((q (l+1)-q l)/(K:ℝ)))
  have hnon (l : ℕ) : 0≤(q (l+1)-q l)/(K:ℝ) :=
    div_nonneg (sub_nonneg.mpr (hq (Nat.le_succ l))) (Nat.cast_nonneg K)
  simp_rw [Real.sq_sqrt (hnon _)] at hcs
  rw [←Finset.sum_div,sum_gaps] at hcs
  simpa only [Finset.card_range,mul_div_assoc] using hcs

theorem budget_le_sqrt (hK : 0<K) (q : ℕ→ℝ) (hq : Monotone q)
    (d : ℕ) (hq0 : 0≤q 0) (hqd : q d≤1) :
    budget K q d≤Real.sqrt ((d:ℝ)/(K:ℝ)) := by
  have hs := budget_sq_le hK q hq d
  have hg : q d-q 0≤1 := by linarith
  have hs' : (budget K q d)^2≤(d:ℝ)/(K:ℝ) := by
    calc
      _≤(d:ℝ)*(q d-q 0)/(K:ℝ) := hs
      _≤(d:ℝ)*1/(K:ℝ) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg d)) (Nat.cast_nonneg K)
      _=_ := by ring
  have hn : 0≤(d:ℝ)/(K:ℝ) := by positivity
  have hr := Real.sq_sqrt hn
  nlinarith [Real.sqrt_nonneg ((d:ℝ)/(K:ℝ))]

/-- HS Lemma 2.9 for the actual finite complete tree in the single-species model. -/
theorem actual_source_HS_2_9 (hN : 0<N) (hK : 0<K) (q : ℕ→ℝ) (hq : Monotone q)
    (d : ℕ) (hq0 : 0≤q 0) (hqd : q d≤1)
    (z : TreeData (Vector N) K d) (hz : ForkTree q d z) :
    ‖leafCentroid d z-root d z‖/Real.sqrt N≤Real.sqrt ((d:ℝ)/(K:ℝ)) := by
  have hn : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  calc
    _≤(Real.sqrt N*budget K q d)/Real.sqrt N :=
      div_le_div_of_nonneg_right (leafCentroid_displacement_le hK q hq d z hz) hn.le
    _=budget K q d := mul_div_cancel_left₀ _ hn.ne'
    _≤_ := budget_le_sqrt hK q hq d hq0 hqd

end SphericalAging.RegularTreeCentroidGeometry
