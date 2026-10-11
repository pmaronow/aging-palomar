module

public import SphericalAging.HeightMassSampling

public section

/-! The true coherent-root step denominator in actual height coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace SphericalAging.CoherentRootSampling
open CausalTree TreeCeilings TreeCoherentRoot UniversalRootInterval HeightCoordinateIntervals HeightMassSampling

@[expose] def rootHeight (v : Space 2) (hv : ‖v‖=1) (z : ℝ × ℝ) : ℕ :=
  max (heightIndex v hv z.1) (heightIndex v hv z.2)

@[expose] def denominator (v : Space 2) (hv : ‖v‖=1) (z : ℝ × ℝ) : ℝ :=
  massBelow v (rootHeight v hv z)+massBelow v (rootHeight v hv z+1)

theorem rootHeight_measurable (v : Space 2) (hv : ‖v‖=1) : Measurable (rootHeight v hv) :=
  ((heightIndex_measurable v hv).comp measurable_fst).max
    ((heightIndex_measurable v hv).comp measurable_snd)

theorem denominator_measurable (v : Space 2) (hv : ‖v‖=1) : Measurable (denominator v hv) :=
  (measurable_of_countable (fun j : ℕ => massBelow v j+massBelow v (j+1))).comp
    (rootHeight_measurable v hv)

theorem maximum_in_height_interval (v : Space 2) (hv : ‖v‖=1) {z : ℝ × ℝ}
    (hz : z.1∈Ioo (0:ℝ) 1 ∧ z.2∈Ioo (0:ℝ) 1) :
    max z.1 z.2∈heightInterval v (rootHeight v hv z) := by
  have hx := heightIndex_interval v hv hz.1
  have hy := heightIndex_interval v hv hz.2
  unfold rootHeight
  rcases le_total (heightIndex v hv z.1) (heightIndex v hv z.2) with hij | hji
  · rw [max_eq_right hij]
    exact ⟨hy.1.trans_le (le_max_right _ _),max_le
      (hx.2.trans (massBelow_monotone v (Nat.succ_le_succ hij))) hy.2⟩
  · rw [max_eq_left hji]
    exact ⟨hx.1.trans_le (le_max_left _ _),max_le hx.2
      (hy.2.trans (massBelow_monotone v (Nat.succ_le_succ hji)))⟩

theorem denominator_on_rectangle (v : Space 2) (hv : ‖v‖=1) {x y : ℝ} {i j : ℕ}
    (hx : x∈Ioo (0:ℝ) 1) (hy : y∈Ioo (0:ℝ) 1)
    (hxi : x∈heightInterval v i) (hyj : y∈heightInterval v j) :
    denominator v hv (x,y)=massBelow v (max i j)+massBelow v (max i j+1) := by
  simp only [denominator,rootHeight,(heightIndex_eq_iff v hv hx i).mpr hxi,
    (heightIndex_eq_iff v hv hy j).mpr hyj]

theorem denominator_bounds (v : Space 2) (hv : ‖v‖=1) {z : ℝ × ℝ} {M : ℝ}
    (hz : z.1∈Ioo (0:ℝ) 1 ∧ z.2∈Ioo (0:ℝ) 1) (hmesh : ∀ j, heightMass v j≤M) :
    max z.1 z.2≤denominator v hv z ∧
      denominator v hv z≤2*max z.1 z.2+2*M ∧
      2*max z.1 z.2-2*M≤denominator v hv z := by
  have hh := maximum_in_height_interval v hv hz
  have hs := massBelow_succ v (rootHeight v hv z)
  have hb := hmesh (rootHeight v hv z)
  have hM : 0≤M := (heightMass_nonneg v 0).trans (hmesh 0)
  have hlow := massBelow_nonneg v (rootHeight v hv z)
  unfold denominator
  exact ⟨by linarith [hh.2],by linarith [hh.1],by linarith [hh.2]⟩

theorem actual_denominator_bounds (v : Space 2) (hv : ‖v‖=1) :
    ∀ᵐ z ∂unitMeasure.prod unitMeasure,
      max z.1 z.2≤denominator v hv z ∧
      denominator v hv z≤2*max z.1 z.2+2*meshBound v ∧
      2*max z.1 z.2-2*meshBound v≤denominator v hv z := by
  filter_upwards [product_ae_interior] with z hz
  exact denominator_bounds v hv hz (height_mesh_bound v hv)

end SphericalAging.CoherentRootSampling
