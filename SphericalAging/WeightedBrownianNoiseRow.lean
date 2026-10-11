module

public import SphericalAging.VectorIto

public section

/-! Exact second moment for a finite row of predictable weights multiplied
by a single genuine Brownian increment. Weights may use the whole past. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.WeightedBrownianNoiseRow
open HardSphereDynamics VectorIto
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- The actual square-integrable weight in the past-measurable L² subspace. -/
@[expose] def knownWeight (r : ℝ≥0) (Z : Ω→ℝ) (hZ : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[F r] Z P) : lpMeas ℝ ℝ (F r) 2 P :=
  ⟨hZ.toLp Z,hZm.congr hZ.coeFn_toLp.symm⟩

theorem knownWeight_ae (r : ℝ≥0) (Z : Ω→ℝ) (hZ : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[F r] Z P) :
    (knownWeight r Z hZ hZm : Ω→ℝ)=ᵐ[P] Z := hZ.coeFn_toLp

theorem weighted_increment_memLp (D : BrownianDriver N P F) (i : Fin N)
    {r q : ℝ≥0} (hrq : r≤q) (Z : Ω→ℝ) (hZ : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[F r] Z P) :
    MemLp (fun ω => Z ω*increment D i r q ω) 2 P := by
  let W := knownWeight r Z hZ hZm
  apply MemLp.ae_eq (hf_Lp := Lp.memLp (elementaryValue D i hrq W))
  filter_upwards [elementaryValue_coe D i hrq W,knownWeight_ae r Z hZ hZm] with ω he hw
  rw [he,hw]

theorem weighted_increment_product_integrable (D : BrownianDriver N P F)
    (i j : Fin N) {r q : ℝ≥0} (hrq : r≤q)
    (Z Y : Ω→ℝ) (hZ : MemLp Z 2 P) (hY : MemLp Y 2 P)
    (hZm : AEStronglyMeasurable[F r] Z P) (hYm : AEStronglyMeasurable[F r] Y P) :
    Integrable (fun ω => (Z ω*increment D i r q ω)*(Y ω*increment D j r q ω)) P :=
  (weighted_increment_memLp D i hrq Z hZ hZm).integrable_mul
    (weighted_increment_memLp D j hrq Y hY hYm)

theorem weighted_increment_square_integral (D : BrownianDriver N P F) (i : Fin N)
    {r q : ℝ≥0} (hrq : r≤q) (Z : Ω→ℝ) (hZ : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[F r] Z P) :
    (∫ ω,(Z ω*increment D i r q ω)^2 ∂P)=((q : ℝ)-(r : ℝ))*(∫ ω,(Z ω)^2 ∂P) := by
  have hi := increment_product_indep_adapted D i i hrq (hZm.mul hZm)
  calc
    _=∫ ω,(increment D i r q ω*increment D i r q ω)*(Z ω*Z ω) ∂P := by
      apply integral_congr_ae
      exact .of_forall (fun _ => by ring)
    _=(∫ ω,increment D i r q ω*increment D i r q ω ∂P)*(∫ ω,Z ω*Z ω ∂P) :=
      hi.integral_fun_mul_eq_mul_integral
        ((increment_memLp_two D i r q).aestronglyMeasurable.mul
          (increment_memLp_two D i r q).aestronglyMeasurable)
        ((hZm.mul hZm).mono (F.le r))
    _=_ := by simp only [←pow_two,increment_integral_sq D i hrq]

theorem weighted_increment_cross_integral (D : BrownianDriver N P F) {i j : Fin N}
    (hij : i≠j) {r q : ℝ≥0} (hrq : r≤q)
    (Z Y : Ω→ℝ) (hZ : MemLp Z 2 P) (hY : MemLp Y 2 P)
    (hZm : AEStronglyMeasurable[F r] Z P) (hYm : AEStronglyMeasurable[F r] Y P) :
    (∫ ω,(Z ω*increment D i r q ω)*(Y ω*increment D j r q ω) ∂P)=0 := by
  have hh := weighted_cross_increment_integral D hij hrq
    (knownWeight r Z hZ hZm) (knownWeight r Y hY hYm)
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [knownWeight_ae r Z hZ hZm,knownWeight_ae r Y hY hYm] with ω hz hy
  rw [hz,hy]

/-- Genuine finite-dimensional conditional Itô isometry for one increment. -/
theorem row_secondMoment (D : BrownianDriver N P F) {r q : ℝ≥0} (hrq : r≤q)
    (Z : Fin N→Ω→ℝ) (hZ : ∀j,MemLp (Z j) 2 P)
    (hZm : ∀j,AEStronglyMeasurable[F r] (Z j) P) :
    MemLp (fun ω => ∑j : Fin N,Z j ω*increment D j r q ω) 2 P ∧
      (∫ ω,(∑j : Fin N,Z j ω*increment D j r q ω)^2 ∂P)=
        ((q : ℝ)-(r : ℝ))*(∫ ω,∑j : Fin N,(Z j ω)^2 ∂P) := by
  have hV (j : Fin N) := weighted_increment_memLp D j hrq (Z j) (hZ j) (hZm j)
  refine ⟨memLp_finset_sum _ (fun j _ => hV j),?_⟩
  have hp (i j : Fin N) := weighted_increment_product_integrable D i j hrq
    (Z i) (Z j) (hZ i) (hZ j) (hZm i) (hZm j)
  have he : (fun ω => (∑j : Fin N,Z j ω*increment D j r q ω)^2)=
      fun ω => ∑i : Fin N,∑j : Fin N,(Z i ω*increment D i r q ω)*(Z j ω*increment D j r q ω) := by
    funext ω
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.mul_sum _ _ _
  rw [he,integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hp i j))]
  simp_rw [integral_finset_sum _ (fun j _ => hp _ j)]
  have hdiag (i : Fin N) :
      (∑j : Fin N,∫ ω,(Z i ω*increment D i r q ω)*(Z j ω*increment D j r q ω) ∂P)=
        ((q : ℝ)-(r : ℝ))*(∫ ω,(Z i ω)^2 ∂P) := by
    rw [Finset.sum_eq_single i]
    · simpa only [←pow_two] using weighted_increment_square_integral D i hrq (Z i) (hZ i) (hZm i)
    · intro j _ hji
      exact weighted_increment_cross_integral D hji.symm hrq (Z i) (Z j) (hZ i) (hZ j) (hZm i) (hZm j)
    · simp
  simp_rw [hdiag]
  rw [←Finset.mul_sum,integral_finset_sum]
  intro j _
  convert (hZ j).integrable_mul (hZ j) using 1
  funext ω
  simp only [Pi.mul_apply,pow_two]

end SphericalAging.WeightedBrownianNoiseRow
