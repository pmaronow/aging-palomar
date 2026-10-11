module

public import SphericalAging.BrownianVectorMoments
public import SphericalAging.VectorIto
public import StochasticCalculus.ItoMaximal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Probability.ConditionalExpectation

public section

/-! True scalar Brownian compact supremum and fourth-power Doob tails. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.BrownianCompactSupTail
open VectorBrownian BrownianVectorMoments
variable {N : ℕ}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

@[expose] def compactCoordinatePath (i : Fin N) (T : ℝ≥0) (ω : Space N) : C(Icc (0 : ℝ≥0) T,ℝ) :=
  (ω i).comp ⟨Subtype.val,continuous_subtype_val⟩

@[expose] def coordinateSup (i : Fin N) (T : ℝ≥0) (ω : Space N) : ℝ :=
  ‖compactCoordinatePath i T ω‖

theorem coordinateSup_measurable (i : Fin N) (T : ℝ≥0) : Measurable (coordinateSup i T) := by
  apply Continuous.measurable
  apply Continuous.norm
  exact (ContinuousMap.continuous_precomp ⟨Subtype.val,continuous_subtype_val⟩).comp (continuous_apply i)

theorem coordinate_le_sup (i : Fin N) (T s : ℝ≥0) (hs : s≤T) (ω : Space N) :
    |coordinate i s ω|≤coordinateSup i T ω :=
  (compactCoordinatePath i T ω).norm_coe_le_norm ⟨s,bot_le,hs⟩

theorem coordinate_martingale (i : Fin N) : Martingale (coordinate i) (filtration N) (law N) := by
  refine ⟨coordinate_stronglyAdapted i,?_⟩
  intro s t hst
  let Z : Space N→ℝ := fun ω => coordinate i t ω-coordinate i s ω
  have hZm : Measurable Z := (coordinate_measurable i t).sub (coordinate_measurable i s)
  have hZc := condExp_indep_eq hZm.comap_le ((filtration N).le s)
    ((measurable_iff_comap_le.mpr le_rfl : Measurable[MeasurableSpace.comap Z inferInstance] Z).stronglyMeasurable)
    ((coordinate_isFilteredPreBrownian i).indep s t hst)
  have hzi : (∫ω,Z ω ∂law N)=0 := VectorIto.increment_integral (driver N) i s t
  have he : coordinate i t=fun ω => Z ω+coordinate i s ω := by funext ω; dsimp [Z];ring
  rw [he]
  have hZint := ((coordinate_memLp i t (q:=2) (by norm_num)).sub
    (coordinate_memLp i s (q:=2) (by norm_num))).integrable (by norm_num)
  have hSi := (coordinate_isPreBrownian i).integrable_eval s
  filter_upwards [condExp_add hZint hSi (m:=filtration N s),hZc] with ω ha hz
  change (law N)[fun ω => Z ω+coordinate i s ω | filtration N s] ω=
    (law N)[Z | filtration N s] ω+(law N)[coordinate i s | filtration N s] ω at ha
  rw [ha,hz,hzi,zero_add]
  exact congrFun (condExp_of_stronglyMeasurable ((filtration N).le s) (coordinate_stronglyAdapted i s) hSi) ω

theorem coordinate_grid_fourth_tail (i : Fin N) (T : ℝ≥0) (a : ℝ≥0) (n : ℕ) :
    a*(law N) {ω | (a:ℝ)≤dyadicPartitionSqMax (fun t ω => (coordinate i t ω)^2) T n ω}
      ≤ENNReal.ofReal (3*(T:ℝ)^2) := by
  let u : ℕ→ℝ≥0 := uniformPartitionTime T (2^n)
  have hu : Monotone u := monotone_uniformPartitionTime_general T (2^n)
  have hM := martingale_comp_monotone (coordinate_martingale i) u hu
  have h4 k : Integrable (fun ω => (coordinate i (u k) ω)^4) (law N) := by
    simpa only [Real.norm_eq_abs,show (4:ℕ)=2*2 from rfl,pow_mul,sq_abs] using
      (coordinate_memLp i (u k) (q:=4) (by norm_num)).integrable_norm_pow'
  have hh := martingale_maximal_pow_four_ineq hM h4 a (2^n)
  have ht : u (2^n)=T := by
    dsimp [u,uniformPartitionTime]
    exact mul_div_cancel_right₀ T (by positivity : ((2^n:ℕ):ℝ≥0)≠0)
  simpa only [dyadicPartitionSqMax,u,Function.comp_def,←pow_mul,show (2*2:ℕ)=4 from rfl,ht,
    coordinate_fourthMoment] using hh

theorem coordinate_union_fourth_tail (i : Fin N) (T : ℝ≥0) (a : ℝ≥0) :
    a*(law N) (⋃n : ℕ,{ω | (a:ℝ)≤dyadicPartitionSqMax (fun t ω => (coordinate i t ω)^2) T n ω})
      ≤ENNReal.ofReal (3*(T:ℝ)^2) := by
  let S : ℕ→Set (Space N) := fun n => {ω | (a:ℝ)≤dyadicPartitionSqMax (fun t ω => (coordinate i t ω)^2) T n ω}
  have hS : Monotone S := by
    intro n m hnm ω hω
    exact hω.trans (monotone_dyadicPartitionSqMax (fun t ω => (coordinate i t ω)^2) T ω hnm)
  rw [show (⋃n : ℕ,{ω | (a:ℝ)≤dyadicPartitionSqMax (fun t ω => (coordinate i t ω)^2) T n ω})=⋃n,S n from rfl,
    hS.measure_iUnion,ENNReal.mul_iSup]
  exact iSup_le fun n => coordinate_grid_fourth_tail i T a n

theorem coordinateSup_sq_exceedance_subset (i : Fin N) (T : ℝ≥0) (a : ℝ) (ha : 0<a) :
    {ω | a<(coordinateSup i T ω)^2} ⊆
      ⋃n : ℕ,{ω | a^2≤dyadicPartitionSqMax (fun t ω => (coordinate i t ω)^2) T n ω} := by
  intro ω hω
  have hn : ¬coordinateSup i T ω≤Real.sqrt a := by
    intro h
    have hh := (sq_le_sq₀ (norm_nonneg (compactCoordinatePath i T ω)) (Real.sqrt_nonneg a)).mpr h
    rw [Real.sq_sqrt ha.le] at hh
    exact not_le.mpr hω hh
  have hnall : ¬∀s : Icc (0:ℝ≥0) T,‖compactCoordinatePath i T ω s‖≤Real.sqrt a := by
    intro hall
    exact hn ((ContinuousMap.norm_le _ (Real.sqrt_nonneg a)).mpr hall)
  push_neg at hnall
  obtain ⟨s,hs⟩ := hnall
  change Real.sqrt a < |coordinate i s.val ω| at hs
  have hs2 : a<(coordinate i s.val ω)^2 := by
    have hh := (sq_lt_sq₀ (Real.sqrt_nonneg a) (abs_nonneg _)).mpr hs
    simpa only [Real.sq_sqrt ha.le,sq_abs] using hh
  have hs4 : a^2<(coordinate i s.val ω)^4 := by nlinarith [sq_nonneg (coordinate i s.val ω)]
  have ht : Tendsto (fun n => (coordinate i (uniformPartitionTime T (2^n) (dyadicApproxIndex s.val T n)) ω)^4)
      atTop (𝓝 ((coordinate i s.val ω)^4)) :=
    (((ω i).continuous.pow 4).continuousAt.tendsto).comp (tendsto_uniformPartitionTime_dyadicApproxIndex s.property.2)
  obtain ⟨n,hn⟩ := ((tendsto_order.mp ht).1 _ hs4).exists
  apply mem_iUnion.mpr
  refine ⟨n,hn.le.trans ?_⟩
  unfold dyadicPartitionSqMax
  have hk : dyadicApproxIndex s.val T n∈Finset.range (2^n+1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (dyadicApproxIndex_le_pow s.property.2 n))
  rw [show (4:ℕ)=2*2 from rfl,pow_mul]
  exact Finset.le_sup' (fun k => ((coordinate i (uniformPartitionTime T (2^n) k) ω)^2)^2) hk

theorem coordinateSup_square_tail (i : Fin N) (T : ℝ≥0) (a : ℝ) (ha : 0<a) :
    (law N) {ω | a<(coordinateSup i T ω)^2}≤ENNReal.ofReal (3*(T:ℝ)^2*a^(-2:ℝ)) := by
  let A : ℝ≥0 := ⟨a^2,sq_nonneg a⟩
  have hh := coordinate_union_fourth_tail i T A
  have he : (law N) {ω | a<(coordinateSup i T ω)^2}≤
      (law N) (⋃n : ℕ,{ω | (A:ℝ)≤dyadicPartitionSqMax (fun t ω => (coordinate i t ω)^2) T n ω}) :=
    measure_mono (coordinateSup_sq_exceedance_subset i T a ha)
  have hA0 : (A:ℝ≥0∞)≠0 := by
    apply ENNReal.coe_ne_zero.mpr
    apply ne_of_gt
    change 0<a^2
    positivity
  have hbound : (law N) {ω | a<(coordinateSup i T ω)^2}≤ENNReal.ofReal (3*(T:ℝ)^2)/(A:ℝ≥0∞) := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hA0) (Or.inl ENNReal.coe_ne_top)).mpr
    calc
      _≤(law N) (⋃n : ℕ,{ω | (A:ℝ)≤dyadicPartitionSqMax (fun t ω => (coordinate i t ω)^2) T n ω})*(A:ℝ≥0∞) := by gcongr
      _≤ENNReal.ofReal (3*(T:ℝ)^2) := by simpa only [mul_comm] using hh
  refine hbound.trans_eq ?_
  rw [ENNReal.coe_nnreal_eq,←ENNReal.ofReal_div_of_pos (by change 0<a^2;positivity),Real.rpow_neg ha.le,
    div_eq_mul_inv]
  rw [show (A:ℝ)=a^2 from rfl]
  norm_num

end SphericalAging.BrownianCompactSupTail
