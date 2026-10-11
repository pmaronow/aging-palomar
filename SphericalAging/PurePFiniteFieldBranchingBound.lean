module

public import SphericalAging.MeshMassInterpolation
public import SphericalAging.PurePVariationalUpperBound

public section

/-! A genuine arbitrary finite mesh ceiling for the pure-p field branching
sum. No differentiability of the correlation schedule is assumed. The actual
step density supplies the continuum obstacle, with only a mesh-sized excess. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace SphericalAging.PurePFiniteFieldBranchingBound
open PurePBranchingVariationalBound PurePVariationalUpperBound
open ExternalFieldElementaryPenalty MeshMassInterpolation
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem prime_growth_bound {p : ℕ} (hp : 2≤p) {x y : ℝ}
    (hx : 0≤x) (hxy : x≤y) (hy : y≤1) :
    prime p y≤prime p x+(p:ℝ)*((p:ℝ)-1)*(y-x) := by
  by_cases he : x=y
  · simp [he]
  · have hlt : x<y := lt_of_le_of_ne hxy he
    have hc : Continuous (prime p) := continuous_const.mul (continuous_id.pow (p-1))
    obtain ⟨u,hu,hd⟩ := exists_deriv_eq_slope (prime p) hlt hc.continuousOn
      (fun u hu => (prime_hasDerivAt hp u).differentiableAt.differentiableWithinAt)
    rw [(prime_hasDerivAt hp u).deriv] at hd
    have hpR : 2≤(p:ℝ) := by exact_mod_cast hp
    have hcurv : curvature p u≤(p:ℝ)*((p:ℝ)-1) := by
      unfold curvature
      exact mul_le_of_le_one_right (mul_nonneg (Nat.cast_nonneg p) (by linarith))
        (pow_le_one₀ (hx.trans hu.1.le) (hu.2.le.trans hy))
    rw [hd] at hcurv
    have hh := (div_le_iff₀ (sub_pos.mpr hlt)).mp hcurv
    linarith

theorem algorithmicField_continuous {p : ℕ} (hp : 3≤p) : Continuous (algorithmicField p) := by
  have hpR : 3≤(p:ℝ) := by exact_mod_cast hp
  have hord : Continuous (fieldOrder p) := by
    unfold fieldOrder
    exact (Real.continuous_rpow_const (div_nonneg (by norm_num) (by linarith) : 0≤1/((p:ℝ)-1))).comp
      ((continuous_id.pow 2).div_const _)
  have hl : Continuous (fun κ : ℝ => thresholdEnergy p+
      ((p:ℝ)-2)/(p:ℝ)*Real.sqrt ((p:ℝ)*((p:ℝ)-1))*(fieldOrder p κ)^((p:ℝ)/2)) :=
    continuous_const.add (continuous_const.mul
      ((Real.continuous_rpow_const (by positivity : 0≤(p:ℝ)/2)).comp hord))
  have hh : Continuous (fun κ : ℝ => Real.sqrt ((p:ℝ)+κ^2)) :=
    Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2))
  apply hl.if_le hh (continuous_id.pow 2) continuous_const
  intro κ hκ
  change κ^2=(p:ℝ)*((p:ℝ)-2) at hκ
  have he := ExternalFieldSharpScalar.algorithmicField_high hp hκ.ge
  simpa only [algorithmicField,ite_eq_left hκ.le] using he

/-- The first field interval may be long. It is exempt from the mesh
condition precisely because its cumulative mass is at most κ². -/
theorem density_cumulative_cap {p : ℕ} (hp : 2≤p) (D : ℕ) (q A : ℕ→ℝ)
    (hq : Monotone q) (hq0 : q 0=0) (hqD : q D=1) (hzero : A 0=0)
    (hA : ∀i<D,0≤A (i+1)-A i) {κ δ : ℝ} (hδ : 0≤δ)
    (hcap : ∀i≤D,A i≤κ^2+prime p (q i))
    (hmesh : ∀i<D,A (i+1)≤κ^2 ∨ q (i+1)-q i≤δ) :
    ∀x∈Icc 0 1,SqrtMassIntegralPartition.mass (density D q A) x≤
      κ^2+prime p x+(p:ℝ)*((p:ℝ)-1)*δ := by
  intro x hx
  have hpR : 2≤(p:ℝ) := by exact_mod_cast hp
  have hC : 0≤(p:ℝ)*((p:ℝ)-1) := mul_nonneg (Nat.cast_nonneg p) (by linarith)
  by_cases hx0 : x=0
  · simp only [hx0,SqrtMassIntegralPartition.mass,intervalIntegral.integral_same]
    exact add_nonneg (add_nonneg (sq_nonneg κ) (prime_nonneg p (by norm_num))) (mul_nonneg hC hδ)
  · obtain ⟨i,hi,hxi⟩ := exists_cell D q (x:=x) (by
      rw [hq0,hqD];exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0),hx.2⟩)
    have hqi : 0≤q i := by rw [←hq0];exact hq (Nat.zero_le i)
    have hqin : q (i+1)≤1 := by rw [←hqD];exact hq (by omega)
    have hm : SqrtMassIntegralPartition.mass (density D q A) x≤A (i+1) := by
      have hh := intervalIntegral.integral_mono_interval (μ:=volume) (f:=density D q A)
        (a:=0) (b:=x) (c:=q 0) (d:=q (i+1)) (by rw [hq0]) hx.1 hxi.2
        (ae_of_all _ (fun y => density_nonneg D q A hq hA y))
        (IntervalIntegrable.trans_iterate (fun j hj => density_cell_integrable D q A hq (by omega)))
      rw [hq0] at hh
      exact hh.trans (by simpa only [hq0] using mass_at_node_le D q A hq hzero hA (j:=i+1) (by omega))
    rcases hmesh i hi with hs | hs
    · have hn := prime_nonneg p hx.1
      have he := mul_nonneg hC hδ
      linarith
    · have hg := prime_growth_bound hp hx.1 hxi.2 hqin
      have hg' : (p:ℝ)*((p:ℝ)-1)*(q (i+1)-x)≤(p:ℝ)*((p:ℝ)-1)*δ :=
        mul_le_mul_of_nonneg_left (by linarith [hxi.1]) hC
      have ha := hcap (i+1) (by omega)
      linarith

theorem finite_cumulative_ceiling {p : ℕ} (hp : 3≤p) (D : ℕ) (q A : ℕ→ℝ)
    (hq : Monotone q) (hq0 : q 0=0) (hqD : q D=1) (hzero : A 0=0)
    (hA : ∀i<D,0≤A (i+1)-A i) {κ δ : ℝ} (hδ : 0≤δ)
    (hcap : ∀i≤D,A i≤κ^2+prime p (q i))
    (hmesh : ∀i<D,A (i+1)≤κ^2 ∨ q (i+1)-q i≤δ) :
    (∑i∈Finset.range D,Real.sqrt ((q (i+1)-q i)*(A (i+1)-A i)))≤
      algorithmicField p (Real.sqrt (κ^2+(p:ℝ)*((p:ℝ)-1)*δ)) := by
  have hpR : 3≤(p:ℝ) := by exact_mod_cast hp
  have hk : 0≤κ^2+(p:ℝ)*((p:ℝ)-1)*δ := add_nonneg (sq_nonneg κ)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg p) (by linarith)) hδ)
  have hh := integral_sqrt_le_algorithmicField hp
    (κ:=Real.sqrt (κ^2+(p:ℝ)*((p:ℝ)-1)*δ)) (Real.sqrt_nonneg _) (density D q A)
    (by simpa only [hq0,hqD] using density_integrable D q A hq)
    (fun x hx => density_nonneg D q A hq hA x)
    (by simpa only [hq0,hqD] using sqrt_density_integrable D q A hq)
    (by simpa only [Real.sq_sqrt hk,add_assoc,add_comm,add_left_comm] using
      density_cumulative_cap (by omega : 2≤p) D q A hq hq0 hqD hzero hA hδ hcap hmesh)
  have he := integral_sqrt_eq_sum D q A hq hA
  rw [hq0,hqD] at he
  rw [he] at hh
  exact hh

theorem mesh_field_ceiling_tendsto {p : ℕ} (hp : 3≤p) {κ : ℝ} (hκ : 0≤κ)
    {α : Type*} {l : Filter α} {δ : α→ℝ} (hδ : Tendsto δ l (𝓝 0)) :
    Tendsto (fun i => algorithmicField p (Real.sqrt (κ^2+(p:ℝ)*((p:ℝ)-1)*δ i)))
      l (𝓝 (algorithmicField p κ)) := by
  have hh := ((algorithmicField_continuous hp).tendsto (Real.sqrt (κ^2+(p:ℝ)*((p:ℝ)-1)*0))).comp
    ((Real.continuous_sqrt.tendsto _).comp (tendsto_const_nhds.add (tendsto_const_nhds.mul hδ)))
  simpa only [Function.comp_def,mul_zero,add_zero,Real.sqrt_sq hκ] using hh

@[expose] def fieldNodes (q : ℕ→ℝ) : ℕ→ℝ
  | 0 => 0
  | i+1 => q i
@[expose] def fieldCumulative (p : ℕ) (κ : ℝ) (q c : ℕ→ℝ) : ℕ→ℝ
  | 0 => 0
  | i+1 => κ^2+c i*prime p (q i)-c 0*prime p (q 0)

theorem fieldNodes_monotone (q : ℕ→ℝ) (hq : Monotone q) (hq0 : 0≤q 0) :
    Monotone (fieldNodes q) := by
  intro i j hij
  cases i with
  | zero =>
    cases j with
    | zero => exact le_rfl
    | succ j => exact hq0.trans (hq (Nat.zero_le j))
  | succ i =>
    cases j with
    | zero => omega
    | succ j => exact hq (by omega)

theorem field_sum_eq_cumulative {p D : ℕ} {κ : ℝ} (hκ : 0≤κ)
    (q c : ℕ→ℝ) (hq0 : 0≤q 0) :
    PurePBranchingHighFieldBound.fieldBranchingSum p D κ q c=
      ∑i∈Finset.range (D+1),Real.sqrt
        ((fieldNodes q (i+1)-fieldNodes q i)*
          (fieldCumulative p κ q c (i+1)-fieldCumulative p κ q c i)) := by
  rw [Finset.sum_range_succ']
  have hfirst : Real.sqrt
      ((fieldNodes q 1-fieldNodes q 0)*(fieldCumulative p κ q c 1-fieldCumulative p κ q c 0))=
        κ*Real.sqrt (q 0) := by
    simp only [fieldNodes,fieldCumulative,sub_zero]
    rw [show κ^2+c 0*prime p (q 0)-c 0*prime p (q 0)=κ^2 by ring,
      Real.sqrt_mul hq0,Real.sqrt_sq hκ,mul_comm]
  rw [hfirst]
  unfold PurePBranchingHighFieldBound.fieldBranchingSum
  rw [add_comm _ (κ*Real.sqrt (q 0))]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [fieldNodes,fieldCumulative]
  congr 2
  ring

/-- The literal finite field branching sum, for arbitrary nondecreasing
levels and correlations. Repeated levels and a positive initial level are
included. Only the actual edge mesh enters the error. -/
theorem fieldBranchingSum_le_perturbed_algorithmicField {p D : ℕ} (hp : 3≤p)
    {κ δ : ℝ} (hκ : 0≤κ) (hδ : 0≤δ) (q c : ℕ→ℝ)
    (hq : Monotone q) (hq0 : 0≤q 0) (hqD : q D=1)
    (hc : Monotone c) (hcn : ∀i≤D,c i∈Icc 0 1)
    (hmesh : ∀i<D,q (i+1)-q i≤δ) :
    PurePBranchingHighFieldBound.fieldBranchingSum p D κ q c≤
      algorithmicField p (Real.sqrt (κ^2+(p:ℝ)*((p:ℝ)-1)*δ)) := by
  have hq' := fieldNodes_monotone q hq hq0
  have hF0 : 0≤c 0*prime p (q 0) := mul_nonneg (hcn 0 (Nat.zero_le D)).1 (prime_nonneg p hq0)
  have hFm (i j : ℕ) (hij : i≤j) (hj : j≤D) : c i*prime p (q i)≤c j*prime p (q j) :=
    mul_le_mul (hc hij)
      (prime_monotoneOn p (hq0.trans (hq (Nat.zero_le i)))
        (hq0.trans (hq (Nat.zero_le j))) (hq hij))
      (prime_nonneg p (hq0.trans (hq (Nat.zero_le i)))) (hcn j hj).1
  rw [field_sum_eq_cumulative hκ q c hq0]
  refine finite_cumulative_ceiling hp (D+1) (fieldNodes q) (fieldCumulative p κ q c)
    hq' rfl hqD rfl ?_ hδ ?_ ?_
  · intro i hi
    cases i with
    | zero => simpa only [fieldCumulative,sub_zero,add_sub_cancel_right] using sq_nonneg κ
    | succ i =>
      have hm := hFm i (i+1) (Nat.le_succ i) (by omega)
      simp only [fieldCumulative]
      linarith
  · intro i hi
    cases i with
    | zero =>
      simp only [fieldCumulative,fieldNodes]
      exact add_nonneg (sq_nonneg _) (prime_nonneg p (by norm_num))
    | succ i =>
      have hm : c i*prime p (q i)≤prime p (q i) :=
        mul_le_of_le_one_left (prime_nonneg p (hq0.trans (hq (Nat.zero_le i)))) (hcn i (by omega)).2
      simp only [fieldCumulative,fieldNodes]
      linarith
  · intro i hi
    cases i with
    | zero =>
      left
      simp only [fieldCumulative]
      linarith
    | succ i => exact Or.inr (hmesh i (by omega))

/-- The mesh threshold is uniform over every finite nondecreasing schedule,
including flat levels. This is the actual finite-ceiling to ALG passage. -/
theorem fieldBranchingSum_uniform_small_mesh {p : ℕ} (hp : 3≤p)
    {κ : ℝ} (hκ : 0≤κ) {ε : ℝ} (hε : 0<ε) :
    ∃δ>0,∀ (D : ℕ) (q c : ℕ→ℝ),Monotone q → 0≤q 0 → q D=1 →
      Monotone c → (∀i≤D,c i∈Icc 0 1) → (∀i<D,q (i+1)-q i≤δ) →
      PurePBranchingHighFieldBound.fieldBranchingSum p D κ q c≤algorithmicField p κ+ε := by
  have ht := mesh_field_ceiling_tendsto hp hκ (α:=ℝ) (l:=𝓝 0) (δ:=id) tendsto_id
  have he : ∀ᶠδ : ℝ in 𝓝 0,algorithmicField p (Real.sqrt (κ^2+(p:ℝ)*((p:ℝ)-1)*δ))<
      algorithmicField p κ+ε :=
    ht.eventually (eventually_lt_nhds (by linarith))
  obtain ⟨η,hη,hbound⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨η/2,by linarith,?_⟩
  intro D q c hq hq0 hqD hc hcn hmesh
  have hh := hbound (y:=η/2) (by
    simp only [Real.dist_eq,sub_zero,abs_of_pos (by linarith : 0<η/2)]
    linarith)
  exact (fieldBranchingSum_le_perturbed_algorithmicField hp hκ (by linarith : 0≤η/2)
    q c hq hq0 hqD hc hcn hmesh).trans hh.le

end SphericalAging.PurePFiniteFieldBranchingBound
