module

public import SphericalAging.TreeThresholdProduct

public section

/-! The exact supremum formulation of the positive threshold product theorem. -/
noncomputable section
open scoped InnerProductSpace Topology
open Set Filter
namespace SphericalAging.TreeThresholdProductSup
open CausalTree TreeCeilings TreePairDeficit TreeThresholdProduct ProductTransfer

/-- Actual admissible cubic tree triple at a deficit tolerance. -/
structure AdmissibleTriple (δ : ℝ) where
  first : Space 2
  second : Space 2
  third : Space 2
  first_unit : ‖first‖=1
  second_unit : ‖second‖=1
  third_unit : ‖third‖=1
  first_second_positive : ∀ j,0≤crossMass first second j
  first_third_positive : ∀ j,0≤crossMass first third j
  second_third_positive : ∀ j,0≤crossMass second third j
  first_deficit : cubicCeiling-functional first≤δ
  second_deficit : cubicCeiling-functional second≤δ
  third_deficit : cubicCeiling-functional third≤δ

@[expose] def productValue {δ : ℝ} (a : AdmissibleTriple δ) : ℝ :=
  positivePart (inner ℝ a.first a.third*inner ℝ a.second a.third-inner ℝ a.first a.second)

@[expose] def productValues (δ : ℝ) : Set ℝ := Set.range (productValue (δ:=δ))

/-- The literal supremum in thm:geometry-threshold-product. -/
@[expose] def productSup (δ : ℝ) : ℝ := sSup (productValues δ)

theorem productValue_nonneg {δ : ℝ} (a : AdmissibleTriple δ) : 0≤productValue a :=
  positivePart_nonneg _

theorem productValue_le {δ : ℝ} (hδ : 0<δ) (hδ1 : δ≤1) (a : AdmissibleTriple δ) :
    productValue a≤thresholdModulus δ :=
  threshold_product a.first a.second a.third a.first_unit a.second_unit a.third_unit
    a.first_second_positive a.first_third_positive a.second_third_positive hδ hδ1
    a.first_deficit a.second_deficit a.third_deficit

theorem productValues_bddAbove {δ : ℝ} (hδ : 0<δ) (hδ1 : δ≤1) : BddAbove (productValues δ) := by
  refine ⟨thresholdModulus δ,?_⟩
  rintro x ⟨a,rfl⟩
  exact productValue_le hδ hδ1 a

theorem productSup_bounds {δ : ℝ} (hδ : 0<δ) (hδ1 : δ≤1) :
    0≤productSup δ ∧ productSup δ≤thresholdModulus δ := by
  by_cases hne : (productValues δ).Nonempty
  · have hne' := hne
    obtain ⟨x,hx⟩ := hne'
    refine ⟨?_,csSup_le hne ?_⟩
    · rcases hx with ⟨a,rfl⟩
      exact (productValue_nonneg a).trans (le_csSup (productValues_bddAbove hδ hδ1) ⟨a,rfl⟩)
    · rintro x ⟨a,rfl⟩
      exact productValue_le hδ hδ1 a
  · have he : productValues δ=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp only [productSup,he,Real.sSup_empty,le_refl,true_and]
    exact thresholdModulus_nonneg δ

/-- Every actual admissible triple obeys the inequality with the literal
supremum modulus, and that modulus tends to zero as δ decreases to zero. -/
theorem threshold_product_supremum {δ : ℝ} (hδ : 0<δ) (hδ1 : δ≤1) (a : AdmissibleTriple δ) :
    productValue a≤productSup δ :=
  le_csSup (productValues_bddAbove hδ hδ1) ⟨a,rfl⟩

theorem productSup_tendsto : Tendsto productSup (𝓝[Ioc (0:ℝ) 1] 0) (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (productSup_bounds hδ.1 hδ.2).1
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (productSup_bounds hδ.1 hδ.2).2
  · exact thresholdModulus_tendsto.mono_left nhdsWithin_le_nhds

/-- Complete source theorem, with its actual supremum and vanishing modulus. -/
theorem positive_threshold_states :
    Tendsto productSup (𝓝[Ioc (0:ℝ) 1] 0) (𝓝 0) ∧
    (∀ δ,0<δ→δ≤1→∀ a : AdmissibleTriple δ,productValue a≤productSup δ) :=
  ⟨productSup_tendsto,fun _ hδ hδ1 a=>threshold_product_supremum hδ hδ1 a⟩

end SphericalAging.TreeThresholdProductSup
