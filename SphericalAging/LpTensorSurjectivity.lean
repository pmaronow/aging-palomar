module

public import SphericalAging.LpProductTensor
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

public section

/-! Surjectivity of the canonical completed L² product isometry. Orthogonality
against actual rectangle indicators forces a function to vanish, first on
finite rectangles, and then on the sigma-finite product space. -/

noncomputable section
open Set MeasureTheory Filter UniformSpace MeasurableSpace
open scoped TensorProduct InnerProductSpace ENNReal Topology

namespace SphericalAging.LpTensorSurjectivity
open LpProductTensor
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

theorem rectangle_measure_ne_top {s : Set X} {t : Set Y}
    (hs : μ s ≠ ∞) (ht : ν t ≠ ∞) : (μ.prod ν) (s ×ˢ t) ≠ ∞ := by
  rw [Measure.prod_prod]
  exact ENNReal.mul_ne_top hs ht

theorem product_indicator {s : Set X} {t : Set Y}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hμ : μ s ≠ ∞) (hν : ν t ≠ ∞) :
    product (indicatorConstLp 2 hs hμ (1 : ℝ)) (indicatorConstLp 2 ht hν (1 : ℝ)) =
      indicatorConstLp 2 (hs.prod ht) (rectangle_measure_ne_top hμ hν) (1 : ℝ) := by
  apply Lp.ext
  filter_upwards [product_coe (indicatorConstLp 2 hs hμ (1 : ℝ))
      (indicatorConstLp 2 ht hν (1 : ℝ)),
    Measure.quasiMeasurePreserving_fst.ae
      (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμ) (c := (1 : ℝ))),
    Measure.quasiMeasurePreserving_snd.ae
      (indicatorConstLp_coeFn (p := 2) (hs := ht) (hμs := hν) (c := (1 : ℝ))),
    indicatorConstLp_coeFn (p := 2) (hs := hs.prod ht)
      (hμs := rectangle_measure_ne_top hμ hν) (c := (1 : ℝ))]
      with z hz hf hg hi
  rw [hz,hf,hg,hi]
  by_cases hzs : z.1 ∈ s <;> by_cases hzt : z.2 ∈ t <;> simp [Set.indicator,hzs,hzt]

/-- Rectangle tests determine an actual integrable function on a product
measurable space, by the pi-lambda induction and uniqueness of set integrals. -/
theorem ae_zero_of_rectangle_integrals {η : Measure (X × Y)} {f : X × Y → ℝ}
    (hf : Integrable f η)
    (hrect : ∀ s : Set X, MeasurableSet s → ∀ t : Set Y, MeasurableSet t →
      ∫ z in s ×ˢ t, f z ∂η = 0) : f =ᵐ[η] 0 := by
  have hall : ∀ s : Set (X × Y), MeasurableSet s → ∫ z in s, f z ∂η = 0 := by
    intro s hs
    induction s,hs using MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
    | empty => simp
    | basic s hs =>
      obtain ⟨s,hs,t,ht,rfl⟩ := hs
      exact hrect s hs t ht
    | compl s hs ih =>
      have huniv : ∫ z, f z ∂η = 0 := by
        simpa only [univ_prod_univ,setIntegral_univ] using hrect univ .univ univ .univ
      have h := integral_add_compl hs hf
      rw [ih,huniv,zero_add] at h
      exact h
    | iUnion s hd hs ih =>
      rw [integral_iUnion hs hd hf.integrableOn]
      simp only [ih,tsum_zero]
  exact hf.ae_eq_zero_of_forall_setIntegral_eq_zero (fun s hs _ => hall s hs)

@[expose] def completedRange : Submodule ℝ (Lp ℝ 2 (μ.prod ν)) :=
  LinearMap.range (completedIsometry (μ := μ) (ν := ν)).toLinearMap

theorem completedRange_isClosed : IsClosed (completedRange (μ := μ) (ν := ν) :
    Set (Lp ℝ 2 (μ.prod ν))) :=
  (completedIsometry (μ := μ) (ν := ν)).isometry.isUniformInducing.isComplete_range.isClosed

theorem rectangle_integral_zero_of_orthogonal {z : Lp ℝ 2 (μ.prod ν)}
    (hz : z ∈ (completedRange (μ := μ) (ν := ν))ᗮ) {s : Set X} {t : Set Y}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hμ : μ s ≠ ∞) (hν : ν t ≠ ∞) :
    ∫ w in s ×ˢ t, z w ∂μ.prod ν = 0 := by
  let f := indicatorConstLp 2 hs hμ (1 : ℝ)
  let g := indicatorConstLp 2 ht hν (1 : ℝ)
  have hm : indicatorConstLp 2 (hs.prod ht) (rectangle_measure_ne_top hμ hν) (1 : ℝ) ∈
      completedRange (μ := μ) (ν := ν) := by
    refine ⟨((f ⊗ₜ[ℝ] g : Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) : Completion _), ?_⟩
    exact (completedIsometry_tmul f g).trans (product_indicator hs ht hμ hν)
  rw [← L2.inner_indicatorConstLp_one (hs.prod ht) (rectangle_measure_ne_top hμ hν) z]
  exact Submodule.inner_right_of_mem_orthogonal hm hz

section SigmaFinite
variable [SigmaFinite μ] [SigmaFinite ν]

theorem orthogonal_eq_zero {z : Lp ℝ 2 (μ.prod ν)}
    (hz : z ∈ (completedRange (μ := μ) (ν := ν))ᗮ) : z = 0 := by
  have hzero (n : ℕ) : (z : X × Y → ℝ) =ᵐ[(μ.prod ν).restrict
      (spanningSets μ n ×ˢ spanningSets ν n)] 0 := by
    let s := spanningSets μ n
    let t := spanningSets ν n
    let η := (μ.restrict s).prod (ν.restrict t)
    have hs : MeasurableSet s := measurableSet_spanningSets μ n
    have ht : MeasurableSet t := measurableSet_spanningSets ν n
    have hμ : μ s ≠ ∞ := (measure_spanningSets_lt_top μ n).ne
    have hν : ν t ≠ ∞ := (measure_spanningSets_lt_top ν n).ne
    have hint : Integrable (z : X × Y → ℝ) η := by
      dsimp only [η]
      rw [Measure.prod_restrict]
      exact integrableOn_Lp_of_measure_ne_top z (by norm_num) (rectangle_measure_ne_top hμ hν)
    have haezero : (z : X × Y → ℝ) =ᵐ[η] 0 := by
      apply ae_zero_of_rectangle_integrals hint
      intro A hA B hB
      dsimp only [η]
      rw [Measure.prod_restrict,Measure.restrict_restrict (hA.prod hB),prod_inter_prod]
      exact rectangle_integral_zero_of_orthogonal hz (hA.inter hs) (hB.inter ht)
        (ne_top_of_le_ne_top hμ (measure_mono inter_subset_right))
        (ne_top_of_le_ne_top hν (measure_mono inter_subset_right))
    simpa only [η,Measure.prod_restrict] using haezero
  have hcover : (⋃ n : ℕ, spanningSets μ n ×ˢ spanningSets ν n) = univ := by
    apply eq_univ_of_forall
    intro w
    obtain ⟨i,hi⟩ := mem_iUnion.mp (show w.1 ∈ ⋃ n, spanningSets μ n by
      rw [iUnion_spanningSets]; trivial)
    obtain ⟨j,hj⟩ := mem_iUnion.mp (show w.2 ∈ ⋃ n, spanningSets ν n by
      rw [iUnion_spanningSets]; trivial)
    exact mem_iUnion.mpr ⟨max i j,
      ⟨spanningSets_mono (le_max_left _ _) hi,spanningSets_mono (le_max_right _ _) hj⟩⟩
  apply Lp.ext
  have hall : (z : X × Y → ℝ) =ᵐ[μ.prod ν] 0 := by
    have hall' := (ae_restrict_iUnion_iff _ _).mpr hzero
    simpa only [EventuallyEq,hcover,Measure.restrict_univ,Pi.zero_apply] using hall'
  exact hall.trans (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ.prod ν)).symm

theorem completedIsometry_surjective :
    Function.Surjective (completedIsometry (μ := μ) (ν := ν)) := by
  let K : Submodule ℝ (Lp ℝ 2 (μ.prod ν)) := completedRange
  letI : CompleteSpace K := completeSpace_coe_iff_isComplete.mpr completedRange_isClosed.isComplete
  have hbot : Kᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro z hz
    change z = 0
    exact orthogonal_eq_zero hz
  have htop : K = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.mp hbot
  intro z
  have hz : z ∈ K := by rw [htop]; trivial
  exact hz

@[expose] def completedEquiv : Completion (Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) ≃ₗᵢ[ℝ]
    Lp ℝ 2 (μ.prod ν) :=
  LinearIsometryEquiv.ofSurjective completedIsometry completedIsometry_surjective

end SigmaFinite
end SphericalAging.LpTensorSurjectivity
