module

public import SphericalAging.HeightCoordinateIntervals
public import SphericalAging.UniversalRootKernelConvergence

public section

/-! Actual measurable cumulative-mass sampling, including interval coverage
and the genuine mesh estimate used by universal-root kernel convergence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.HeightMassSampling
open CausalTree TreeCeilings TreeCoherentRoot UniversalRootInterval HeightCoordinateIntervals
local instance (α : Type*) : DecidableEq α := Classical.decEq α

theorem upper_mass_exists (v : Space 2) (hv : ‖v‖=1) {x : ℝ} (hx : x<1) :
    ∃ j : ℕ, x≤massBelow v (j+1) := by
  have hh : ∀ᶠ j : ℕ in atTop, x<massBelow v (j+1) :=
    tendsto_const_nhds.eventually_lt
      ((massBelow_tendsto v hv).comp (tendsto_add_atTop_nat 1)) hx
  obtain ⟨j,hj⟩ := hh.exists
  exact ⟨j,hj.le⟩

@[expose] def heightIndex (v : Space 2) (hv : ‖v‖=1) (x : ℝ) : ℕ :=
  if hx : x∈Ioo (0:ℝ) 1 then Nat.find (upper_mass_exists v hv hx.2) else 0

theorem heightIndex_interval (v : Space 2) (hv : ‖v‖=1) {x : ℝ} (hx : x∈Ioo (0:ℝ) 1) :
    x∈heightInterval v (heightIndex v hv x) := by
  simp only [heightIndex,dif_pos hx,heightInterval,mem_Ioc]
  let hh := upper_mass_exists v hv hx.2
  change massBelow v (Nat.find hh)<x ∧ x≤massBelow v (Nat.find hh+1)
  refine ⟨?_,Nat.find_spec hh⟩
  cases he : Nat.find hh with
  | zero => simpa only [he,massBelow_zero] using hx.1
  | succ j =>
    have hbefore : ¬x≤massBelow v (j+1) := Nat.find_min hh (by omega : j<Nat.find hh)
    simpa only [he] using lt_of_not_ge hbefore

theorem heightIndex_eq_iff (v : Space 2) (hv : ‖v‖=1) {x : ℝ} (hx : x∈Ioo (0:ℝ) 1) (j : ℕ) :
    heightIndex v hv x=j ↔ x∈heightInterval v j := by
  constructor
  · intro he
    simpa only [he] using heightIndex_interval v hv hx
  · intro hj
    by_contra hne
    exact Set.disjoint_left.mp (heightInterval_disjoint v hne) (heightIndex_interval v hv hx) hj

theorem heightIndex_positive_mass (v : Space 2) (hv : ‖v‖=1) {x : ℝ}
    (hx : x∈Ioo (0:ℝ) 1) : 0<heightMass v (heightIndex v hv x) := by
  have hj := heightIndex_interval v hv hx
  have hs := massBelow_succ v (heightIndex v hv x)
  linarith [hj.1,hj.2]

theorem heightInterval_cover (v : Space 2) (hv : ‖v‖=1) {x : ℝ}
    (hx : x∈Ioo (0:ℝ) 1) : ∃ j : ℕ, x∈heightInterval v j :=
  ⟨heightIndex v hv x,heightIndex_interval v hv hx⟩

theorem heightIndex_measurable (v : Space 2) (hv : ‖v‖=1) : Measurable (heightIndex v hv) := by
  apply measurable_to_countable'
  intro j
  have he : heightIndex v hv ⁻¹' {j}=
      (heightInterval v j∩Ioo (0:ℝ) 1)∪(if j=0 then (Ioo (0:ℝ) 1)ᶜ else ∅) := by
    ext x
    by_cases hx : x∈Ioo (0:ℝ) 1
    · change heightIndex v hv x=j ↔
        (x∈heightInterval v j ∧ x∈Ioo (0:ℝ) 1) ∨ x∈(if j=0 then (Ioo (0:ℝ) 1)ᶜ else ∅)
      rw [heightIndex_eq_iff v hv hx]
      split_ifs <;> simp only [hx,and_true,mem_compl_iff,not_true_eq_false,or_false,mem_empty_iff_false]
    · simp [heightIndex,hx,eq_comm]
  rw [he]
  apply MeasurableSet.union (measurableSet_Ioc.inter measurableSet_Ioo)
  split_ifs
  · exact measurableSet_Ioo.compl
  · exact MeasurableSet.empty

@[expose] def upperMass (v : Space 2) (hv : ‖v‖=1) (x : ℝ) : ℝ :=
  massBelow v (heightIndex v hv x+1)

theorem upperMass_measurable (v : Space 2) (hv : ‖v‖=1) : Measurable (upperMass v hv) :=
  (measurable_of_countable (fun j : ℕ => massBelow v (j+1))).comp (heightIndex_measurable v hv)

theorem upperMass_le_one (v : Space 2) (hv : ‖v‖=1) (x : ℝ) : upperMass v hv x≤1 := by
  simpa only [upperMass,hv,one_pow] using massBelow_le_norm_sq v (heightIndex v hv x+1)

theorem upperMass_bounds (v : Space 2) (hv : ‖v‖=1) {x M : ℝ} (hx : x∈Ioo (0:ℝ) 1)
    (hmesh : ∀ j, heightMass v j≤M) : x≤upperMass v hv x ∧ upperMass v hv x≤x+M := by
  have hj := heightIndex_interval v hv hx
  refine ⟨hj.2,?_⟩
  unfold upperMass
  rw [massBelow_succ]
  linarith [hj.1,hmesh (heightIndex v hv x)]

@[expose] def pairMass (v : Space 2) (hv : ‖v‖=1) (z : ℝ × ℝ) : ℝ :=
  max (upperMass v hv z.1) (upperMass v hv z.2)

theorem pairMass_measurable (v : Space 2) (hv : ‖v‖=1) : Measurable (pairMass v hv) :=
  ((upperMass_measurable v hv).comp measurable_fst).max ((upperMass_measurable v hv).comp measurable_snd)

theorem pairMass_on_rectangle (v : Space 2) (hv : ‖v‖=1) {x y : ℝ} {i j : ℕ}
    (hx : x∈Ioo (0:ℝ) 1) (hy : y∈Ioo (0:ℝ) 1)
    (hxi : x∈heightInterval v i) (hyj : y∈heightInterval v j) :
    pairMass v hv (x,y)=massBelow v (max i j+1) := by
  have hi := (heightIndex_eq_iff v hv hx i).mpr hxi
  have hj := (heightIndex_eq_iff v hv hy j).mpr hyj
  simp only [pairMass,upperMass,hi,hj]
  rcases le_total i j with hij | hji
  · rw [max_eq_right hij,max_eq_right (massBelow_monotone v (Nat.succ_le_succ hij))]
  · rw [max_eq_left hji,max_eq_left (massBelow_monotone v (Nat.succ_le_succ hji))]

theorem pairMass_bounds (v : Space 2) (hv : ‖v‖=1) {z : ℝ × ℝ} {M : ℝ}
    (hz : z.1∈Ioo (0:ℝ) 1 ∧ z.2∈Ioo (0:ℝ) 1) (hmesh : ∀ j, heightMass v j≤M) :
    max z.1 z.2≤pairMass v hv z ∧ pairMass v hv z≤max z.1 z.2+M := by
  have hx := upperMass_bounds v hv hz.1 hmesh
  have hy := upperMass_bounds v hv hz.2 hmesh
  refine ⟨max_le_max hx.1 hy.1,?_⟩
  apply max_le
  · linarith [hx.2,le_max_left z.1 z.2]
  · linarith [hy.2,le_max_right z.1 z.2]

theorem unit_ae_interior : ∀ᵐ x ∂unitMeasure, x∈Ioo (0:ℝ) 1 := by
  have hne : ∀ᵐ x ∂unitMeasure, x≠1 := by
    rw [ae_iff]
    have hs : unitMeasure {(1:ℝ)}=0 := by
      rw [unitMeasure,Measure.restrict_apply (measurableSet_singleton _)]
      exact measure_mono_null inter_subset_left (measure_singleton _)
    simpa using hs
  filter_upwards [UniversalRootKernel.unit_ae,hne] with x hx hn
  exact ⟨hx.1,lt_of_le_of_ne hx.2 hn⟩

theorem product_ae_interior : ∀ᵐ z ∂unitMeasure.prod unitMeasure,
    z.1∈Ioo (0:ℝ) 1 ∧ z.2∈Ioo (0:ℝ) 1 := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae unit_ae_interior,
    Measure.quasiMeasurePreserving_snd.ae unit_ae_interior] with z hx hy
  exact ⟨hx,hy⟩

@[expose] def meshBound (v : Space 2) : ℝ := Real.sqrt (4*Real.sqrt 2*(cubicCeiling-functional v))

theorem actual_sampling_bounds (v : Space 2) (hv : ‖v‖=1) :
    ∀ᵐ z ∂unitMeasure.prod unitMeasure,
      max z.1 z.2≤pairMass v hv z ∧ pairMass v hv z≤max z.1 z.2+meshBound v := by
  filter_upwards [product_ae_interior] with z hz
  exact pairMass_bounds v hv hz (height_mesh_bound v hv)

theorem actual_sampled_kernel_tendsto (v : ℕ → Space 2) (hv : ∀ n, ‖v n‖=1)
    (hf : Tendsto (fun n => functional (v n)) atTop (𝓝 cubicCeiling)) :
    ∃ hk : ∀ n, MemLp (UniversalRootKernelConvergence.sampledKernel (pairMass (v n) (hv n)))
        2 (unitMeasure.prod unitMeasure),
      Tendsto (fun n => (hk n).toLp (UniversalRootKernelConvergence.sampledKernel (pairMass (v n) (hv n))))
        atTop (𝓝 UniversalRootKernel.kernelL2) := by
  apply UniversalRootKernelConvergence.sampledKernel_tendsto
    (fun n => pairMass_measurable (v n) (hv n)) (mesh:=fun n => meshBound (v n))
  · filter_upwards [product_ae_interior] with z hz
    intro n
    exact pairMass_bounds (v n) (hv n) hz (height_mesh_bound (v n) (hv n))
  · have hd : Tendsto (fun n => cubicCeiling-functional (v n)) atTop (𝓝 (0:ℝ)) := by
      simpa only [sub_self] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => cubicCeiling) atTop (𝓝 cubicCeiling)).sub hf
    have hs := (hd.const_mul (4*Real.sqrt 2)).sqrt
    simpa only [meshBound,mul_zero,Real.sqrt_zero] using hs

end SphericalAging.HeightMassSampling
