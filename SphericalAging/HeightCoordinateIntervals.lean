module

public import SphericalAging.UniversalRootInterval
public import SphericalAging.TreeCoherentRoot

public section

/-! Consecutive interval indicators carrying the actual height masses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace SphericalAging.HeightCoordinateIntervals
open CausalTree TreeCeilings TreeCoherentRoot UniversalRootInterval
local instance (α : Type*) : DecidableEq α := Classical.decEq α

@[expose] def intervalIndicator (a b : ℝ) : IntervalL2 :=
  indicatorConstLp 2 (s:=Ioc a b) measurableSet_Ioc (measure_ne_top _ _) (1 : ℝ)

theorem intervalIndicator_coe (a b : ℝ) :
    (intervalIndicator a b : ℝ → ℝ)=ᵐ[unitMeasure] (Ioc a b).indicator (fun _ => (1:ℝ)) :=
  indicatorConstLp_coeFn (p:=2) (μ:=unitMeasure) (hs:=measurableSet_Ioc)
    (hμs:=measure_ne_top _ _) (c:=(1:ℝ))

theorem intervalIndicator_inner (a b c d : ℝ) :
    inner ℝ (intervalIndicator a b) (intervalIndicator c d)=unitMeasure.real (Ioc a b∩Ioc c d) :=
  L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
    (μ:=unitMeasure) measurableSet_Ioc measurableSet_Ioc (measure_ne_top _ _) (measure_ne_top _ _)

theorem interval_measure {a b : ℝ} (ha : 0≤a) (hab : a≤b) (hb : b≤1) :
    unitMeasure.real (Ioc a b)=b-a := by
  have hs : Ioc a b⊆Ioc (0:ℝ) 1 := by intro x hx; exact ⟨ha.trans_lt hx.1,hx.2.trans hb⟩
  rw [measureReal_def,unitMeasure,Measure.restrict_apply measurableSet_Ioc,
    inter_eq_left.mpr hs,←measureReal_def,Real.volume_real_Ioc_of_le hab]

theorem intervalIndicator_norm_sq {a b : ℝ} (ha : 0≤a) (hab : a≤b) (hb : b≤1) :
    ‖intervalIndicator a b‖^2=b-a := by
  rw [←real_inner_self_eq_norm_sq,intervalIndicator_inner,inter_self,interval_measure ha hab hb]

theorem intervalIndicator_empty (a : ℝ) : intervalIndicator a a=0 := by
  simp [intervalIndicator]

theorem intervalIndicator_add {a b c : ℝ} (hab : a≤b) (hbc : b≤c) :
    intervalIndicator a b+intervalIndicator b c=intervalIndicator a c := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (intervalIndicator a b) (intervalIndicator b c),
    intervalIndicator_coe a b,intervalIndicator_coe b c,intervalIndicator_coe a c]
    with x hadd hx hy hz
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hx,hy,hz]
  simp only [Pi.add_apply,Set.indicator,mem_Ioc]
  split_ifs <;> simp_all <;> linarith

@[expose] def heightInterval (v : Space 2) (j : ℕ) : Set ℝ := Ioc (massBelow v j) (massBelow v (j+1))

@[expose] def heightIndicator (v : Space 2) (j : ℕ) : IntervalL2 :=
  intervalIndicator (massBelow v j) (massBelow v (j+1))

theorem heightIndicator_norm_sq (v : Space 2) (hv : ‖v‖=1) (j : ℕ) :
    ‖heightIndicator v j‖^2=heightMass v j := by
  unfold heightIndicator
  rw [intervalIndicator_norm_sq (massBelow_nonneg v j) (massBelow_monotone v (by omega))
    (by simpa only [hv,one_pow] using massBelow_le_norm_sq v (j+1)),massBelow_succ]
  ring

theorem heightInterval_disjoint (v : Space 2) {i j : ℕ} (hij : i≠j) :
    Disjoint (heightInterval v i) (heightInterval v j) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hm := massBelow_monotone v (show i+1 ≤ j by omega)
    exact (hy.1.trans_le (hx.2.trans hm)).false
  · have hm := massBelow_monotone v (show j+1 ≤ i by omega)
    exact (hx.1.trans_le (hy.2.trans hm)).false

theorem heightIndicator_orthogonal (v : Space 2) {i j : ℕ} (hij : i≠j) :
    inner ℝ (heightIndicator v i) (heightIndicator v j)=0 := by
  rw [heightIndicator,heightIndicator,intervalIndicator_inner]
  change unitMeasure.real (heightInterval v i∩heightInterval v j)=0
  rw [Set.disjoint_iff_inter_eq_empty.mp (heightInterval_disjoint v hij)]
  simp

theorem initialIndicator_tendsto (v : Space 2) (hv : ‖v‖=1) :
    Tendsto (fun n : ℕ => intervalIndicator 0 (massBelow v (n+1))) atTop (𝓝 one) := by
  have hm (n : ℕ) : massBelow v (n+1)≤1 := by
    simpa only [hv,one_pow] using massBelow_le_norm_sq v (n+1)
  have he (n : ℕ) : ‖intervalIndicator 0 (massBelow v (n+1))-one‖^2=1-massBelow v (n+1) := by
    have hi : inner ℝ (intervalIndicator 0 (massBelow v (n+1))) one=massBelow v (n+1) := by
      rw [one,intervalIndicator]
      rw [L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
        (μ:=unitMeasure) measurableSet_Ioc MeasurableSet.univ (measure_ne_top _ _) (measure_ne_top _ _)]
      simp only [inter_univ]
      rw [interval_measure le_rfl (massBelow_nonneg v (n+1)) (hm n),sub_zero]
    rw [norm_sub_sq_real,intervalIndicator_norm_sq le_rfl (massBelow_nonneg v (n+1)) (hm n),
      one_norm,one_pow,sub_zero,hi]
    ring
  have ht : Tendsto (fun n : ℕ => massBelow v (n+1)) atTop (𝓝 (1:ℝ)) :=
    (massBelow_tendsto v hv).comp (tendsto_add_atTop_nat 1)
  have hs := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub ht).sqrt
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  convert hs using 1
  · funext n
    rw [←he,Real.sqrt_sq (norm_nonneg _)]
  · norm_num

end SphericalAging.HeightCoordinateIntervals
