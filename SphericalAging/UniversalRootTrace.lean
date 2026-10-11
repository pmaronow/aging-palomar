module

public import SphericalAging.UniversalRootFrame
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Topology.Bases

public section

/-! The basis-independent positive operator trace of the actual universal root. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter UniformSpace
open scoped ENNReal InnerProductSpace TensorProduct Topology
namespace SphericalAging.UniversalRootTrace
open UniversalRootInterval UniversalRootKernel UniversalRootPrefix UniversalRootFrame
open CausalTree CausalTree.HilbertDatum
local instance (α : Type*) : DecidableEq α := Classical.decEq α
local instance : Fact ((2:ℝ≥0∞)≠∞) := ⟨by norm_num⟩

theorem orthonormal_countable {ι : Type*} {f : ι → IntervalL2}
    (hf : Orthonormal ℝ f) : Countable ι := by
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (f i) (1/2:ℝ))
      (Metric.ball (f j) (1/2:ℝ))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hn : ‖f i-f j‖^2=2 := by
      rw [norm_sub_sq_real,hf.norm_eq_one i,hf.norm_eq_one j,hf.inner_eq_zero hij]
      norm_num
    have hb : ‖f i-f j‖<1 := by
      change dist x (f i)<1/2 at hx
      change dist x (f j)<1/2 at hy
      have ht := dist_triangle (f i) x (f j)
      rw [dist_comm (f i) x,dist_eq_norm (f i) (f j)] at ht
      exact lt_of_le_of_lt ht (by linarith [hx,hy])
    nlinarith [norm_nonneg (f i-f j)]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨f i,Metric.mem_ball_self (by norm_num)⟩)

theorem universalOperator_quadratic (f : IntervalL2) :
    inner ℝ f (universalOperator f) =
      (Real.sqrt 2)⁻¹ * (inner ℝ one f)^2 +
        (2*Real.sqrt 2)⁻¹ * ∫ z, z^(-3/2:ℝ)*(inner ℝ (clippedPrefix z) f)^2 ∂unitMeasure := by
  have h := frameOperator_quadratic f
  simpa only [frameOperator,frameRoot_eq,universalOperator,operatorOfKernel,universalRoot] using h

theorem frame_diagonal_integrable (f : IntervalL2) :
    Integrable (fun z => z^(-3/2:ℝ)*(inner ℝ (clippedPrefix z) f)^2) unitMeasure := by
  have h := weightedPrefix_integrable.const_inner (𝕜:=ℝ) (pure intervalDatum intervalDatum f f)
  apply h.congr
  exact Eventually.of_forall (fun z => by
    simp only [weightedPrefix,real_inner_smul_right,prefixRankOne]
    rw [CausalTree.HilbertDatum.inner_pure intervalDatum intervalDatum f (clippedPrefix z) f (clippedPrefix z)]
    rw [real_inner_comm f (clippedPrefix z),pow_two])

theorem finite_trace_formula {ι : Type*} (f : ι → IntervalL2) (s : Finset ι) :
    ∑ i ∈ s, inner ℝ (f i) (universalOperator (f i)) =
      (Real.sqrt 2)⁻¹ * (∑ i ∈ s, (inner ℝ one (f i))^2) +
        (2*Real.sqrt 2)⁻¹ * ∫ z, z^(-3/2:ℝ)*(∑ i ∈ s,(inner ℝ (clippedPrefix z) (f i))^2) ∂unitMeasure := by
  simp_rw [universalOperator_quadratic]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
  congr 1
  congr 1
  rw [←integral_finsetSum s (fun i _ => frame_diagonal_integrable (f i))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => (Finset.mul_sum s _ _).symm)

theorem basis_square_hasSum {ι : Type*} (b : HilbertBasis ι ℝ IntervalL2) (x : IntervalL2) :
    HasSum (fun i => (inner ℝ x (b i))^2) (‖x‖^2) := by
  simpa only [real_inner_comm (b _),←pow_two,real_inner_self_eq_norm_sq] using
    b.hasSum_inner_mul_inner x x

theorem basis_square_bessel {ι : Type*} (b : HilbertBasis ι ℝ IntervalL2)
    (s : Finset ι) (x : IntervalL2) :
    (∑ i ∈ s, (inner ℝ x (b i))^2) ≤ ‖x‖^2 := by
  have h := b.orthonormal.sum_inner_products_le (s:=s) x
  simpa only [Real.norm_eq_abs,sq_abs,real_inner_comm (b _)] using h

theorem universalOperator_trace {ι : Type*} (b : HilbertBasis ι ℝ IntervalL2) :
    HasSum (fun i => inner ℝ (b i) (universalOperator (b i))) (Real.sqrt 2) := by
  letI : Countable ι := orthonormal_countable b.orthonormal
  change Tendsto (fun s : Finset ι => ∑ i ∈ s,inner ℝ (b i) (universalOperator (b i))) atTop (𝓝 (Real.sqrt 2))
  have hc : Tendsto (fun s : Finset ι => ∑ i ∈ s,(inner ℝ one (b i))^2) atTop (𝓝 1) := by
    simpa only [HasSum,SummationFilter.unconditional_filter,one_norm,one_pow] using (basis_square_hasSum b one)
  have hi : Tendsto
      (fun s : Finset ι => ∫ z, z^(-3/2:ℝ)*(∑ i ∈ s,(inner ℝ (clippedPrefix z) (b i))^2) ∂unitMeasure)
      atTop (𝓝 2) := by
    have hr : Integrable (fun z : ℝ => z^(-1/2:ℝ)) unitMeasure :=
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ)< -1/2)).1
    have he : (∫ z, z^(-1/2:ℝ) ∂unitMeasure)=2 := by
      have h := weightedPrefix_norm_integral
      calc
        _ = ∫ z, ‖weightedPrefix z‖ ∂unitMeasure := by
          apply integral_congr_ae
          filter_upwards [unit_ae] with z hz
          exact (weightedPrefix_norm hz.1 hz.2).symm
        _ = 2 := h
    conv_rhs => rw [←he]
    apply tendsto_integral_filter_of_dominated_convergence (fun z => z^(-1/2:ℝ))
    · exact Eventually.of_forall (fun s => (integrable_finsetSum s
        (fun i _ => frame_diagonal_integrable (b i))).aestronglyMeasurable.congr
        (Eventually.of_forall (fun z => (Finset.mul_sum s _ _).symm)))
    · apply Eventually.of_forall
      intro s
      filter_upwards [unit_ae] with z hz
      have hn : 0 ≤ ∑ i ∈ s,(inner ℝ (clippedPrefix z) (b i))^2 :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hp : ‖clippedPrefix z‖^2=z := by
        rw [clippedPrefix,clamp_eq ⟨hz.1.le,hz.2⟩,prefix_norm_sq ⟨hz.1.le,hz.2⟩]
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hz.1.le _) hn)]
      calc
        _ ≤ z^(-3/2:ℝ)*z := by
          apply mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hz.1.le _)
          exact (basis_square_bessel b s (clippedPrefix z)).trans_eq hp
        _ = z^(-1/2:ℝ) := by
          calc
            _ = z^(-3/2:ℝ)*z^(1:ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [←Real.rpow_add hz.1]; norm_num
    · exact hr
    · filter_upwards [unit_ae] with z hz
      have h := (basis_square_hasSum b (clippedPrefix z)).const_mul (z^(-3/2:ℝ))
      have hp : ‖clippedPrefix z‖^2=z := by
        rw [clippedPrefix,clamp_eq ⟨hz.1.le,hz.2⟩,prefix_norm_sq ⟨hz.1.le,hz.2⟩]
      have he : z^(-3/2:ℝ)*z=z^(-1/2:ℝ) := by
        calc
          _ = z^(-3/2:ℝ)*z^(1:ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [←Real.rpow_add hz.1]; norm_num
      simpa only [HasSum,SummationFilter.unconditional_filter,hp,he] using h
  have h := (hc.const_mul (Real.sqrt 2)⁻¹).add (hi.const_mul (2*Real.sqrt 2)⁻¹)
  have hv : (Real.sqrt 2)⁻¹*1+(2*Real.sqrt 2)⁻¹*2=Real.sqrt 2 := by
    have h2 : Real.sqrt 2≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  simpa only [←finite_trace_formula,hv] using h

theorem universalOperator_trace_sum {ι : Type*} (b : HilbertBasis ι ℝ IntervalL2) :
    Summable (fun i => inner ℝ (b i) (universalOperator (b i))) ∧
      (∑' i, inner ℝ (b i) (universalOperator (b i)))=Real.sqrt 2 :=
  ⟨(universalOperator_trace b).summable,(universalOperator_trace b).tsum_eq⟩

/-- The positive operator has absolutely summable diagonal in every actual Hilbert
basis; the value is independent of the basis. This is the positive trace-class
criterion and proves the actual trace, rather than supplying it as a premise. -/
theorem universalOperator_absolute_trace {ι : Type*} (b : HilbertBasis ι ℝ IntervalL2) :
    HasSum (fun i => |inner ℝ (b i) (universalOperator (b i))|) (Real.sqrt 2) := by
  simpa only [abs_of_nonneg (universalOperator_positive _)] using universalOperator_trace b

/-- A concrete Hilbert basis exists, and its positive operator diagonal is
summable with the literal trace value. -/
theorem universalOperator_traceClass :
    ∃ (s : Set IntervalL2) (b : HilbertBasis s ℝ IntervalL2),
      Summable (fun i => |inner ℝ (b i) (universalOperator (b i))|) ∧
        (∑' i,inner ℝ (b i) (universalOperator (b i)))=Real.sqrt 2 := by
  obtain ⟨s,b,hb⟩ := exists_hilbertBasis (𝕜:=ℝ) (E:=IntervalL2)
  exact ⟨s,b,(universalOperator_absolute_trace b).summable,(universalOperator_trace b).tsum_eq⟩

end SphericalAging.UniversalRootTrace
