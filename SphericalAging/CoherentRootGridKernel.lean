module

public import SphericalAging.CoherentRootFiniteGrid
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

/-! Actual L² rectangle sums converge to the literal coherent denominator kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.CoherentRootGridKernel
open CausalTree TreeCeilings TreeCoherentRoot UniversalRootInterval UniversalRootKernel
open HeightCoordinateIntervals HeightMassSampling CoherentRootSampling CoherentRootFiniteGrid
open UniversalRootDenominatorConvergence
local instance (α : Type*) : DecidableEq α := Classical.decEq α

@[expose] def stepFunction (v : Space 2) (hv : ‖v‖=1) : ℝ × ℝ → ℝ := denominatorKernel (denominator v hv)

theorem stepFunction_memLp (v : Space 2) (hv : ‖v‖=1) :
    MemLp (stepFunction v hv) 2 (unitMeasure.prod unitMeasure) := by
  apply (kernel_memLp.const_mul 2).of_le
    (denominatorKernel_measurable (denominator_measurable v hv)).aestronglyMeasurable
  have hb := denominatorKernel_bounds ((actual_denominator_bounds v hv).mono (fun _ h => h.1))
  filter_upwards [hb] with z hz
  change ‖denominatorKernel (denominator v hv) z‖≤‖2*kernel z‖
  rw [Real.norm_eq_abs,abs_of_nonneg hz.1,Real.norm_eq_abs,
    abs_of_nonneg (le_trans hz.1 hz.2)]
  exact hz.2

@[expose] def stepKernel (v : Space 2) (hv : ‖v‖=1) : KernelL2 := (stepFunction_memLp v hv).toLp (stepFunction v hv)

@[expose] def truncatedFunction (v : Space 2) (hv : ‖v‖=1) (n : ℕ) (z : ℝ × ℝ) : ℝ :=
  if heightIndex v hv z.1≤n ∧ heightIndex v hv z.2≤n then stepFunction v hv z else 0

theorem stepFunction_coefficient (v : Space 2) (hv : ‖v‖=1) (z : ℝ × ℝ) :
    stepFunction v hv z=coefficient v (heightIndex v hv z.1) (heightIndex v hv z.2) := by
  unfold stepFunction denominatorKernel denominator rootHeight coefficient
  rw [cubicWeight]
  congr 2
  ring

theorem heightIndicator_value (v : Space 2) (hv : ‖v‖=1) {x : ℝ}
    (hx : x∈Ioo (0:ℝ) 1) (i : ℕ) :
    (heightInterval v i).indicator (fun _ => (1:ℝ)) x=
      if i=heightIndex v hv x then 1 else 0 := by
  simp only [Set.indicator]
  have hi := heightIndex_eq_iff v hv hx i
  by_cases he : i=heightIndex v hv x
  · rw [if_pos (hi.mp he.symm),if_pos he]
  · rw [if_neg (by intro hh; exact he (hi.mpr hh).symm),if_neg he]

theorem finite_grid_selection (a : ℕ → ℕ → ℝ) (n i j : ℕ) :
    (∑ k ∈ Finset.range (n+1),∑ l ∈ Finset.range (n+1),
      a k l*(if k=i then 1 else 0)*(if l=j then 1 else 0))=
      if i≤n ∧ j≤n then a i j else 0 := by
  simp only [mul_ite,ite_mul,mul_one,mul_zero]
  simp only [Finset.sum_ite_irrel,Finset.sum_ite_eq',Finset.mem_range,Nat.lt_succ_iff]
  by_cases hi : i≤n <;> by_cases hj : j≤n <;> simp [hi,hj]

theorem gridKernel_coe (v : Space 2) (hv : ‖v‖=1) (n : ℕ) :
    (gridKernel v n : ℝ × ℝ → ℝ)=ᵐ[unitMeasure.prod unitMeasure] truncatedFunction v hv n := by
  have hblock (i j : ℕ) :
      ((coefficient v i j • LpProductTensor.product (heightIndicator v i) (heightIndicator v j) : KernelL2) : ℝ × ℝ → ℝ)=ᵐ[unitMeasure.prod unitMeasure]
        (fun z => coefficient v i j*
          ((heightInterval v i).indicator (fun _ => (1:ℝ)) z.1)*
          ((heightInterval v j).indicator (fun _ => (1:ℝ)) z.2)) := by
    filter_upwards [Lp.coeFn_smul (coefficient v i j) (LpProductTensor.product (heightIndicator v i) (heightIndicator v j)),
      LpProductTensor.product_coe (heightIndicator v i) (heightIndicator v j),
      Measure.quasiMeasurePreserving_fst.ae (intervalIndicator_coe (massBelow v i) (massBelow v (i+1))),
      Measure.quasiMeasurePreserving_snd.ae (intervalIndicator_coe (massBelow v j) (massBelow v (j+1)))]
      with z hs hp hi hj
    simp only [Pi.smul_apply,smul_eq_mul] at hs
    rw [hs,hp]
    change coefficient v i j*(heightIndicator v i z.1*heightIndicator v j z.2)=_
    change heightIndicator v i z.1=(heightInterval v i).indicator (fun _ => (1:ℝ)) z.1 at hi
    change heightIndicator v j z.2=(heightInterval v j).indicator (fun _ => (1:ℝ)) z.2 at hj
    rw [hi,hj]
    ring
  have hrow (i : ℕ) :
      ((∑ j ∈ Finset.range (n+1),coefficient v i j • LpProductTensor.product (heightIndicator v i) (heightIndicator v j) : KernelL2) : ℝ × ℝ → ℝ)=ᵐ[unitMeasure.prod unitMeasure]
        (fun z => ∑ j ∈ Finset.range (n+1),coefficient v i j*
          ((heightInterval v i).indicator (fun _ => (1:ℝ)) z.1)*
          ((heightInterval v j).indicator (fun _ => (1:ℝ)) z.2)) := by
    have hb : ∀ᵐ z ∂unitMeasure.prod unitMeasure, ∀ j,
        (coefficient v i j • LpProductTensor.product (heightIndicator v i) (heightIndicator v j) : KernelL2) z=
          coefficient v i j*(heightInterval v i).indicator (fun _ => (1:ℝ)) z.1*
            (heightInterval v j).indicator (fun _ => (1:ℝ)) z.2 := ae_all_iff.mpr (hblock i)
    filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range (n+1))
      (fun j => coefficient v i j • LpProductTensor.product (heightIndicator v i) (heightIndicator v j)),hb] with z hs hb
    rw [hs]
    exact Finset.sum_congr rfl (fun j _ => hb j)
  have hall : (gridKernel v n : ℝ × ℝ → ℝ)=ᵐ[unitMeasure.prod unitMeasure]
      (fun z => ∑ i ∈ Finset.range (n+1),∑ j ∈ Finset.range (n+1),coefficient v i j*
        ((heightInterval v i).indicator (fun _ => (1:ℝ)) z.1)*
        ((heightInterval v j).indicator (fun _ => (1:ℝ)) z.2)) := by
    have hr := ae_all_iff.mpr hrow
    filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range (n+1))
      (fun i => ∑ j ∈ Finset.range (n+1),coefficient v i j •
        LpProductTensor.product (heightIndicator v i) (heightIndicator v j)),hr] with z hs hr
    unfold gridKernel
    rw [hs]
    exact Finset.sum_congr rfl (fun i _ => hr i)
  filter_upwards [hall,product_ae_interior] with z he hz
  rw [he]
  simp only [heightIndicator_value v hv hz.1,heightIndicator_value v hv hz.2]
  rw [finite_grid_selection]
  simp only [truncatedFunction,stepFunction_coefficient]

theorem gridKernel_tendsto (v : Space 2) (hv : ‖v‖=1) :
    Tendsto (gridKernel v) atTop (𝓝 (stepKernel v hv)) := by
  have hpoint (z : ℝ × ℝ) : Tendsto (fun n => truncatedFunction v hv n z) atTop (𝓝 (stepFunction v hv z)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (heightIndex v hv z.1),eventually_ge_atTop (heightIndex v hv z.2)] with n hx hy
    simp [truncatedFunction,hx,hy]
  have hm (n : ℕ) : Measurable (truncatedFunction v hv n) := by
    exact (denominatorKernel_measurable (denominator_measurable v hv)).ite
      ((measurableSet_le ((heightIndex_measurable v hv).comp measurable_fst) measurable_const).inter
        (measurableSet_le ((heightIndex_measurable v hv).comp measurable_snd) measurable_const)) measurable_const
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ z ∂unitMeasure.prod unitMeasure,
      ‖(truncatedFunction v hv n z-stepFunction v hv z)^2‖≤4*kernel z^2 := by
    exact Eventually.of_forall (fun n => by
      filter_upwards [denominatorKernel_bounds ((actual_denominator_bounds v hv).mono (fun _ h => h.1))] with z hz
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      unfold truncatedFunction stepFunction
      split_ifs <;> nlinarith [sq_nonneg (denominatorKernel (denominator v hv) z),
        mul_nonneg hz.1 (sub_nonneg.mpr hz.2)])
  have hint : Integrable (fun z => 4*kernel z^2) (unitMeasure.prod unitMeasure) := kernel_square_integrable.const_mul 4
  have hs := tendsto_integral_filter_of_dominated_convergence
    (F:=fun n z => (truncatedFunction v hv n z-stepFunction v hv z)^2)
    (f:=fun _ => (0:ℝ)) (fun z => 4*kernel z^2)
    (Eventually.of_forall (fun n => ((hm n).sub (denominatorKernel_measurable (denominator_measurable v hv))).pow_const 2 |>.aestronglyMeasurable))
    hbound hint (Eventually.of_forall (fun z => by
      have hc : Tendsto (fun _ : ℕ => stepFunction v hv z) atTop (𝓝 (stepFunction v hv z)) := tendsto_const_nhds
      simpa only [sub_self,zero_pow (by decide : 2≠0)] using ((hpoint z).sub hc).pow 2))
  have he (n : ℕ) : ‖gridKernel v n-stepKernel v hv‖^2=
      ∫ z, (truncatedFunction v hv n z-stepFunction v hv z)^2 ∂unitMeasure.prod unitMeasure := by
    rw [UniversalRootKernelConvergence.lp_norm_square]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (gridKernel v n) (stepKernel v hv),gridKernel_coe v hv n,
      MemLp.coeFn_toLp (stepFunction_memLp v hv)] with z hd hg hk
    simp only [Pi.sub_apply] at hd
    change stepKernel v hv z=stepFunction v hv z at hk
    rw [hd,hg,hk]
  have ht : Tendsto (fun n => ‖gridKernel v n-stepKernel v hv‖^2) atTop (𝓝 (0:ℝ)) := by
    simpa only [he,integral_zero] using hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr := ht.sqrt
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hr

end SphericalAging.CoherentRootGridKernel
