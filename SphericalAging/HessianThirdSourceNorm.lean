module

public import SphericalAging.HessianThirdSourceError
public import SphericalAging.LpFiniteDomination

public section

/-! Actual L² bounds for the third derivative of the Hessian forcing.
The two fixed-field products are kept literal for truncation. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.HessianThirdSourceNorm
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment
open LpThreeProductBounds LpProductBounds HessianThirdSourceError
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
local instance : NormedAddCommGroup (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance

/-- A generic literal field bound is used only inside the proved actual
flow estimate. All higher-moment hypotheses are discharged there. -/
theorem eight_field_norm_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (R : α→ℝ) (hR : MemLp R 2 μ)
    (I E D U V X Y DU DV RU RV QU : α→State N)
    (hI : MemLp I 8 μ) (hE : MemLp E 4 μ) (hD : MemLp D 8 μ)
    (hU : MemLp U 8 μ) (hV : MemLp V 8 μ) (hX : MemLp X 8 μ) (hY : MemLp Y 4 μ)
    (hDU : MemLp DU 4 μ) (hDV : MemLp DV 4 μ)
    (hRU : MemLp RU 4 μ) (hRV : MemLp RV 4 μ) (hQU : MemLp QU 4 μ)
    (A M L : ℝ) (hA : 0≤A) (hM : 0≤M) (hL : 0≤L)
    (hX4 : MemLp X 4 μ)
    (hb : ∀ᵐq∂μ,‖R q‖≤
      A*‖I q‖^2*‖U q‖*‖V q‖+M*‖E q‖*‖U q‖*‖V q‖+
      M*‖D q‖*‖DU q‖*‖V q‖+M*‖D q‖*‖X q‖*‖DV q‖+
      L*‖RU q‖*‖Y q‖+L*‖RU q‖*‖DV q‖+
      L*‖QU q‖*‖DV q‖+L*‖X q‖*‖RV q‖) :
    lpNorm R 2 μ≤
      A*(lpNorm I 8 μ)^2*lpNorm U 8 μ*lpNorm V 8 μ+
      M*lpNorm E 4 μ*lpNorm U 8 μ*lpNorm V 8 μ+
      M*lpNorm D 8 μ*lpNorm DU 4 μ*lpNorm V 8 μ+
      M*lpNorm D 8 μ*lpNorm X 8 μ*lpNorm DV 4 μ+
      L*lpNorm (fun q => ‖RU q‖*‖Y q‖) 2 μ+
      L*lpNorm RU 4 μ*lpNorm DV 4 μ+
      L*lpNorm QU 4 μ*lpNorm DV 4 μ+
      L*lpNorm (fun q => ‖RV q‖*‖X q‖) 2 μ := by
  let T₁ : α→ℝ := fun q => A*(‖I q‖^2*‖U q‖*‖V q‖)
  let T₂ : α→ℝ := fun q => M*(‖E q‖*‖U q‖*‖V q‖)
  let T₃ : α→ℝ := fun q => M*(‖DU q‖*‖D q‖*‖V q‖)
  let T₄ : α→ℝ := fun q => M*(‖DV q‖*‖D q‖*‖X q‖)
  let T₅ : α→ℝ := fun q => L*(‖RU q‖*‖Y q‖)
  let T₆ : α→ℝ := fun q => L*(‖RU q‖*‖DV q‖)
  let T₇ : α→ℝ := fun q => L*(‖QU q‖*‖DV q‖)
  let T₈ : α→ℝ := fun q => L*(‖RV q‖*‖X q‖)
  have hUV : MemLp (fun q => ‖U q‖*‖V q‖) 4 μ := hU.norm.fun_mul hV.norm
  have hDV8 : MemLp (fun q => ‖D q‖*‖V q‖) 4 μ := hD.norm.fun_mul hV.norm
  have hDX8 : MemLp (fun q => ‖D q‖*‖X q‖) 4 μ := hD.norm.fun_mul hX.norm
  have hm₁ : MemLp T₁ 2 μ := by
    simpa only [T₁,mul_assoc] using ((squared_memLp_four hI).fun_mul hUV).const_mul A
  have hm₂ : MemLp T₂ 2 μ := by
    simpa only [T₂,mul_assoc] using (hE.norm.fun_mul hUV).const_mul M
  have hm₃ : MemLp T₃ 2 μ := by
    simpa only [T₃,mul_assoc] using (hDU.norm.fun_mul hDV8).const_mul M
  have hm₄ : MemLp T₄ 2 μ := by
    simpa only [T₄,mul_assoc] using (hDV.norm.fun_mul hDX8).const_mul M
  have hm₅ : MemLp T₅ 2 μ := (hRU.norm.fun_mul hY.norm).const_mul L
  have hm₆ : MemLp T₆ 2 μ := (hRU.norm.fun_mul hDV.norm).const_mul L
  have hm₇ : MemLp T₇ 2 μ := (hQU.norm.fun_mul hDV.norm).const_mul L
  have hm₈ : MemLp T₈ 2 μ := (hRV.norm.fun_mul hX4.norm).const_mul L
  let B := T₁+T₂+T₃+T₄+T₅+T₆+T₇+T₈
  have hB : MemLp B 2 μ := ((((((hm₁.add hm₂).add hm₃).add hm₄).add hm₅).add hm₆).add hm₇).add hm₈
  have hRB : lpNorm R 2 μ≤lpNorm B 2 μ := by
    apply ENNReal.toReal_mono hB.eLpNorm_ne_top
    apply eLpNorm_mono_ae hR.aestronglyMeasurable
    filter_upwards [hb] with q hq
    have hpos : 0≤B q := by dsimp [B,T₁,T₂,T₃,T₄,T₅,T₆,T₇,T₈];positivity
    rw [Real.norm_of_nonneg hpos]
    convert hq using 1 <;> dsimp [B,T₁,T₂,T₃,T₄,T₅,T₆,T₇,T₈] <;> ring
  have hn2 : lpNorm (T₁+T₂) 2 μ≤lpNorm T₁ 2 μ+lpNorm T₂ 2 μ := lpNorm_add_le hm₁ (by norm_num)
  have hn3 : lpNorm (T₁+T₂+T₃) 2 μ≤lpNorm T₁ 2 μ+lpNorm T₂ 2 μ+lpNorm T₃ 2 μ :=
    (lpNorm_add_le (hm₁.add hm₂) (by norm_num)).trans (add_le_add hn2 (le_refl _))
  have hn4 : lpNorm (T₁+T₂+T₃+T₄) 2 μ≤lpNorm T₁ 2 μ+lpNorm T₂ 2 μ+lpNorm T₃ 2 μ+lpNorm T₄ 2 μ :=
    (lpNorm_add_le ((hm₁.add hm₂).add hm₃) (by norm_num)).trans (add_le_add hn3 (le_refl _))
  have hn5 : lpNorm (T₁+T₂+T₃+T₄+T₅) 2 μ≤lpNorm T₁ 2 μ+lpNorm T₂ 2 μ+lpNorm T₃ 2 μ+lpNorm T₄ 2 μ+lpNorm T₅ 2 μ :=
    (lpNorm_add_le (((hm₁.add hm₂).add hm₃).add hm₄) (by norm_num)).trans (add_le_add hn4 (le_refl _))
  have hn6 : lpNorm (T₁+T₂+T₃+T₄+T₅+T₆) 2 μ≤lpNorm T₁ 2 μ+lpNorm T₂ 2 μ+lpNorm T₃ 2 μ+lpNorm T₄ 2 μ+lpNorm T₅ 2 μ+lpNorm T₆ 2 μ :=
    (lpNorm_add_le ((((hm₁.add hm₂).add hm₃).add hm₄).add hm₅) (by norm_num)).trans (add_le_add hn5 (le_refl _))
  have hn7 : lpNorm (T₁+T₂+T₃+T₄+T₅+T₆+T₇) 2 μ≤lpNorm T₁ 2 μ+lpNorm T₂ 2 μ+lpNorm T₃ 2 μ+lpNorm T₄ 2 μ+lpNorm T₅ 2 μ+lpNorm T₆ 2 μ+lpNorm T₇ 2 μ :=
    (lpNorm_add_le (((((hm₁.add hm₂).add hm₃).add hm₄).add hm₅).add hm₆) (by norm_num)).trans (add_le_add hn6 (le_refl _))
  have hn8 : lpNorm (T₁+T₂+T₃+T₄+T₅+T₆+T₇+T₈) 2 μ≤lpNorm T₁ 2 μ+lpNorm T₂ 2 μ+lpNorm T₃ 2 μ+lpNorm T₄ 2 μ+lpNorm T₅ 2 μ+lpNorm T₆ 2 μ+lpNorm T₇ 2 μ+lpNorm T₈ 2 μ :=
    (lpNorm_add_le ((((((hm₁.add hm₂).add hm₃).add hm₄).add hm₅).add hm₆).add hm₇) (by norm_num)).trans (add_le_add hn7 (le_refl _))
  have hn := hRB.trans hn8
  have hn₁ : lpNorm T₁ 2 μ≤A*(lpNorm I 8 μ)^2*lpNorm U 8 μ*lpNorm V 8 μ := by
    dsimp [T₁]
    rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg hA]
    have hp := lpNorm_product_le (squared_memLp_four hI) hUV
    simp only [Real.norm_of_nonneg (sq_nonneg _),Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)),lpNorm_squared_four hI,mul_assoc] at hp
    have hh := mul_le_mul_of_nonneg_left (lpNorm_eight_product_le hU hV) (mul_nonneg hA (sq_nonneg (lpNorm I 8 μ)))
    have hh' : A*(lpNorm I 8 μ)^2*lpNorm (fun q => ‖U q‖*‖V q‖) 4 μ≤A*(lpNorm I 8 μ)^2*lpNorm U 8 μ*lpNorm V 8 μ := by
      simpa only [mul_assoc] using hh
    simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hp hA).trans (by simpa only [mul_assoc] using hh')
  have hn₂ : lpNorm T₂ 2 μ≤M*lpNorm E 4 μ*lpNorm U 8 μ*lpNorm V 8 μ := by
    dsimp [T₂];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg hM]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (lpNorm_triple_le hE hU hV) hM
  have hn₃ : lpNorm T₃ 2 μ≤M*lpNorm D 8 μ*lpNorm DU 4 μ*lpNorm V 8 μ := by
    dsimp [T₃];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg hM]
    simpa only [mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_left (lpNorm_triple_le hDU hD hV) hM
  have hn₄ : lpNorm T₄ 2 μ≤M*lpNorm D 8 μ*lpNorm X 8 μ*lpNorm DV 4 μ := by
    dsimp [T₄];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg hM]
    simpa only [mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_left (lpNorm_triple_le hDV hD hX) hM
  have hn₅ : lpNorm T₅ 2 μ=L*lpNorm (fun q => ‖RU q‖*‖Y q‖) 2 μ := by
    dsimp [T₅];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg hL]
  have hn₆ : lpNorm T₆ 2 μ≤L*lpNorm RU 4 μ*lpNorm DV 4 μ := by
    dsimp [T₆];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg hL]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (lpNorm_product_le hRU hDV) hL
  have hn₇ : lpNorm T₇ 2 μ≤L*lpNorm QU 4 μ*lpNorm DV 4 μ := by
    dsimp [T₇];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg hL]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (lpNorm_product_le hQU hDV) hL
  have hn₈ : lpNorm T₈ 2 μ=L*lpNorm (fun q => ‖RV q‖*‖X q‖) 2 μ := by
    dsimp [T₈];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg hL]
  apply hn.trans
  rw [hn₅,hn₈]
  simpa only [add_assoc] using add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add (add_le_add hn₁ hn₂) hn₃) hn₄) (le_refl _)) hn₆) hn₇) (le_refl _)

end SphericalAging.HessianThirdSourceNorm
