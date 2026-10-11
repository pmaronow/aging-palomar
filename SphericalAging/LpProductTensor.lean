module


/-
Modified for this project: compatibility adaptations and source-comment cleanup.
Apache-2.0: vendor/LICENSE. Provenance: vendor/PROVENANCE.json.
-/

public import SphericalAging.CausalTree
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.Convex.Integral

public section

/-! A completed Hilbert tensor product realized as actual functions in
L² of the product measure. Pure-product proofs adapt the real version of
OAI/Dynamics/MultipleMixing/Tensors.lean at openai/math commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The linear completed isometry is
constructed here; no tensor/L² identification is assumed. -/

noncomputable section
open MeasureTheory UniformSpace Filter
open scoped TensorProduct InnerProductSpace ENNReal

namespace SphericalAging.LpProductTensor

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

theorem product_memLp (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    MemLp (fun z : X × Y => f z.1 * g z.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq_norm
    ((f.1.stronglyMeasurable.comp_measurable measurable_fst).mul
      (g.1.stronglyMeasurable.comp_measurable measurable_snd)).aestronglyMeasurable).mpr
  change Integrable (fun z : X × Y => ‖f z.1*g z.2‖ ^ 2) (μ.prod ν)
  simp only [norm_mul,mul_pow]
  exact ((Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).mul_prod
    ((Lp.memLp g).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))

@[expose] def product (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) : Lp ℝ 2 (μ.prod ν) :=
  (product_memLp f g).toLp _

theorem product_coe (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    (product f g : X × Y → ℝ) =ᵐ[μ.prod ν] (fun z => f z.1 * g z.2) :=
  MemLp.coeFn_toLp _

theorem product_inner (f f' : Lp ℝ 2 μ) (g g' : Lp ℝ 2 ν) :
    inner ℝ (product f g) (product f' g') = inner ℝ f f' * inner ℝ g g' := by
  rw [L2.inner_def,L2.inner_def f f',L2.inner_def g g',← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [product_coe f g,product_coe f' g'] with z hz hz'
  rw [hz,hz']
  simp only [RCLike.inner_apply,map_mul]
  ring

theorem product_add_left (f f' : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    product (f+f') g = product f g + product f' g := by
  apply Lp.ext
  filter_upwards [product_coe (f+f') g,product_coe f g,product_coe f' g,
    Lp.coeFn_add (product f g) (product f' g),
    Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_add f f')] with z ha hb hc hd he
  simp only [Pi.add_apply] at hd he
  rw [ha,hd,hb,hc,he,add_mul]

theorem product_smul_left (c : ℝ) (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    product (c • f) g = c • product f g := by
  apply Lp.ext
  filter_upwards [product_coe (c • f) g,product_coe f g,
    Lp.coeFn_smul c (product f g),
    Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_smul c f)] with z ha hb hc hd
  simp only [Pi.smul_apply] at hc hd
  rw [ha,hc,hb,hd]
  simp only [smul_eq_mul,mul_assoc]

theorem product_add_right (f : Lp ℝ 2 μ) (g g' : Lp ℝ 2 ν) :
    product f (g+g') = product f g + product f g' := by
  apply Lp.ext
  filter_upwards [product_coe f (g+g'),product_coe f g,product_coe f g',
    Lp.coeFn_add (product f g) (product f g'),
    Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_add g g')] with z ha hb hc hd he
  simp only [Pi.add_apply] at hd he
  rw [ha,hd,hb,hc,he,mul_add]

theorem product_smul_right (c : ℝ) (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    product f (c • g) = c • product f g := by
  apply Lp.ext
  filter_upwards [product_coe f (c • g),product_coe f g,
    Lp.coeFn_smul c (product f g),
    Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_smul c g)] with z ha hb hc hd
  simp only [Pi.smul_apply] at hc hd
  rw [ha,hc,hb,hd]
  simp only [smul_eq_mul]
  ring

@[expose] def productBilinear : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 (μ.prod ν) where
  toFun f := {
    toFun := product f
    map_add' := product_add_right f
    map_smul' := fun c g => product_smul_right c f g }
  map_add' f f' := by
    apply LinearMap.ext
    intro g
    exact product_add_left f f' g
  map_smul' c f := by
    apply LinearMap.ext
    intro g
    exact product_smul_left c f g

@[expose] def tensorMap : (Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) →ₗ[ℝ] Lp ℝ 2 (μ.prod ν) :=
  TensorProduct.lift productBilinear

@[simp] theorem tensorMap_tmul (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    tensorMap (f ⊗ₜ[ℝ] g) = product f g := rfl

theorem tensorMap_inner (u v : Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) :
    inner ℝ (tensorMap u) (tensorMap v) = inner ℝ u v := by
  induction u using TensorProduct.inductionOn with
  | tmul f g =>
    induction v using TensorProduct.inductionOn with
    | tmul f' g' => simp only [tensorMap_tmul,product_inner,TensorProduct.inner_tmul]
    | add v w hv hw => simp only [map_add,inner_add_right,hv,hw]
  | add u w hu hw => simp only [map_add,inner_add_left,hu,hw]

@[expose] def tensorIsometry : (Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) →ₗᵢ[ℝ] Lp ℝ 2 (μ.prod ν) :=
  { tensorMap with
    norm_map' := fun u => by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      change ‖tensorMap u‖ ^ 2 = ‖u‖ ^ 2
      rw [← real_inner_self_eq_norm_sq (tensorMap u),← real_inner_self_eq_norm_sq u]
      exact tensorMap_inner u u }

@[expose] def completedIsometry : Completion (Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) →ₗᵢ[ℝ]
    Lp ℝ 2 (μ.prod ν) := tensorIsometry.fromCompletion

@[simp] theorem completedIsometry_tmul (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    completedIsometry ((f ⊗ₜ[ℝ] g : Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) : Completion _) =
      product f g := by
  rw [completedIsometry,LinearIsometry.fromCompletion_apply_coe]
  rfl

@[expose] def Nonnegative {Z : Type*} [MeasurableSpace Z] {η : Measure Z} (f : Lp ℝ 2 η) : Prop :=
  ∀ᵐ z ∂η, 0 ≤ f z

theorem product_nonnegative (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν)
    (hf : Nonnegative f) (hg : Nonnegative g) : Nonnegative (product f g) := by
  filter_upwards [product_coe f g,Measure.quasiMeasurePreserving_fst.ae hf,
    Measure.quasiMeasurePreserving_snd.ae hg] with z hz hzf hzg
  rw [hz]
  exact mul_nonneg hzf hzg

/-- The cone of actual nonnegative functions is norm-closed, including on
infinite measure spaces. An L² limit has an almost everywhere convergent
subsequence, so no pointwise representative continuity is assumed. -/
theorem nonnegative_isClosed {Z : Type*} [MeasurableSpace Z] (η : Measure Z) :
    IsClosed {f : Lp ℝ 2 η | Nonnegative f} := by
  apply IsSeqClosed.isClosed
  intro f g hf hfg
  obtain ⟨ns,_,hns⟩ := (tendstoInMeasure_of_tendsto_Lp hfg).exists_seq_tendsto_ae
  have hall : ∀ᵐ z ∂η, ∀ n : ℕ, 0 ≤ f n z := ae_all_iff.mpr hf
  filter_upwards [hns,hall] with z hz hzf
  exact ge_of_tendsto hz (Eventually.of_forall (fun n => hzf (ns n)))

theorem nonnegative_add {Z : Type*} [MeasurableSpace Z] {η : Measure Z}
    {f g : Lp ℝ 2 η} (hf : Nonnegative f) (hg : Nonnegative g) : Nonnegative (f+g) := by
  filter_upwards [Lp.coeFn_add f g,hf,hg] with z hz hzf hzg
  change (f+g) z = f z+g z at hz
  rw [hz]
  exact add_nonneg hzf hzg

theorem nonnegative_smul {Z : Type*} [MeasurableSpace Z] {η : Measure Z}
    {f : Lp ℝ 2 η} {a : ℝ} (ha : 0 ≤ a) (hf : Nonnegative f) : Nonnegative (a • f) := by
  filter_upwards [Lp.coeFn_smul a f,hf] with z hz hzf
  change (a • f) z = a*f z at hz
  rw [hz]
  exact mul_nonneg ha hzf

theorem nonnegative_convex {Z : Type*} [MeasurableSpace Z] (η : Measure Z) :
    Convex ℝ {f : Lp ℝ 2 η | Nonnegative f} := by
  intro f hf g hg a b ha hb _
  exact nonnegative_add (nonnegative_smul ha hf) (nonnegative_smul hb hg)

theorem nonnegative_zero {Z : Type*} [MeasurableSpace Z] (η : Measure Z) :
    Nonnegative (0 : Lp ℝ 2 η) := by
  filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := η)] with z hz
  simpa only [hz,Pi.zero_apply] using (le_refl (0 : ℝ))

/-- Actual Bochner integration preserves the cone; this is used for the tree
Volterra integral on a finite time interval. -/
theorem nonnegative_integral {Z A : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    {η : Measure Z} {σ : Measure A} [IsFiniteMeasure σ]
    {f : A → Lp ℝ 2 η} (hf : ∀ᵐ a ∂σ, Nonnegative (f a)) (hfi : Integrable f σ) :
    Nonnegative (∫ a, f a ∂σ) := by
  by_cases hσ : σ = 0
  · simp only [hσ,integral_zero_measure]
    exact nonnegative_zero η
  · letI : NeZero σ := ⟨hσ⟩
    have ha := (nonnegative_convex η).average_mem (nonnegative_isClosed η) hf hfi
    rw [← measure_smul_average σ f]
    exact nonnegative_smul ENNReal.toReal_nonneg ha

end SphericalAging.LpProductTensor
