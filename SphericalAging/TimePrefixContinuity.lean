module

public import SphericalAging.TreePolynomialDrift
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Topology.Sequences
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

/-! Strong continuity of the actual Brownian-time prefix, including its
completed tensor and Hilbert direct-sum extensions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory UniformSpace
open scoped Topology InnerProductSpace
namespace SphericalAging.TimePrefixContinuity
open CausalTree CausalTree.HilbertDatum TreePolynomialDrift

/-- Continuous parameter orbits form a closed set for any family of linear
contractions. The proof uses uniform approximation in the parameter. -/
theorem parameter_continuity_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ℝ→E→L[ℝ] E) (hP : ∀T x,‖P T x‖≤‖x‖) :
    IsClosed {x : E | Continuous (fun T => P T x)} := by
  apply IsSeqClosed.isClosed
  intro f x hf hfx
  have hu : TendstoUniformly (fun n T => P T (f n)) (fun T => P T x) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have he : ∀ᶠ n in atTop, dist (f n) x<ε := (Metric.tendsto_nhds.mp hfx) ε hε
    filter_upwards [he] with n hn T
    rw [dist_eq_norm,←map_sub]
    exact (hP T (x-f n)).trans_lt (by simpa only [←dist_eq_norm,dist_comm] using hn)
  exact hu.continuous (Frequently.of_forall hf)

theorem noisePrefix_parameter_continuous (f : NoiseSpace) :
    Continuous (fun T : ℝ => noisePrefix T f) := by
  apply continuous_iff_continuousAt.mpr
  intro S
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hsq : Integrable (fun v : ℝ => (f v)^2) μ :=
    (memLp_two_iff_integrable_sq (Lp.memLp f).aestronglyMeasurable).mp (Lp.memLp f)
  have hm (T : ℝ) : AEStronglyMeasurable
      (fun v : ℝ => (((Iic T).indicator f v)-((Iic S).indicator f v))^2) μ := by
    exact (((Lp.memLp f).aestronglyMeasurable.indicator measurableSet_Iic).sub
      ((Lp.memLp f).aestronglyMeasurable.indicator measurableSet_Iic)).pow 2
  have hb : ∀ᶠ T : ℝ in 𝓝 S, ∀ᵐ v : ℝ ∂μ,
      ‖(((Iic T).indicator f v)-((Iic S).indicator f v))^2‖≤4*(f v)^2 := by
    filter_upwards with T
    filter_upwards with v
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    by_cases hvT : v≤T <;> by_cases hvS : v≤S <;>
      simp only [indicator,mem_Iic,hvT,hvS,ite_true,ite_false] <;> nlinarith [sq_nonneg (f v)]
  have hl : ∀ᵐ v : ℝ ∂μ, Tendsto
      (fun T : ℝ => (((Iic T).indicator f v)-((Iic S).indicator f v))^2) (𝓝 S) (𝓝 0) := by
    filter_upwards [μ.ae_ne S] with v hv
    rcases lt_or_gt_of_ne hv with hvs | hsv
    · apply tendsto_const_nhds.congr'
      filter_upwards [Ioi_mem_nhds hvs] with T hT
      change v<T at hT
      simp [indicator_of_mem (show v∈Iic T from hT.le),indicator_of_mem (show v∈Iic S from hvs.le)]
    · apply tendsto_const_nhds.congr'
      filter_upwards [Iio_mem_nhds hsv] with T hT
      change T<v at hT
      simp [indicator_of_notMem (show v∉Iic T from not_le.mpr hT),
        indicator_of_notMem (show v∉Iic S from not_le.mpr hsv)]
  have hd := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (F := fun T v => (((Iic T).indicator f v)-((Iic S).indicator f v))^2)
    (f := fun _ => (0 : ℝ)) (fun v => 4*(f v)^2)
    (Eventually.of_forall hm) hb (hsq.const_mul 4) hl
  simp only [integral_zero] at hd
  have he (T : ℝ) : ‖noisePrefix T f-noisePrefix S f‖^2=
      ∫v : ℝ,(((Iic T).indicator f v)-((Iic S).indicator f v))^2 ∂μ := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (noisePrefix T f) (noisePrefix S f),
      noisePrefix_coe T f,noisePrefix_coe S f] with v hsub hT hS
    simp only [hsub,Pi.sub_apply,hT,hS,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  have hh : Tendsto (fun T : ℝ => ‖noisePrefix T f-noisePrefix S f‖^2) (𝓝 S) (𝓝 0) := hd.congr' (Eventually.of_forall fun T => (he T).symm)
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh.sqrt

theorem leafPrefix_parameter_continuous (x : LeafSpace) :
    Continuous (fun T : ℝ => leafPrefix T x) := by
  have h := (continuous_const : Continuous (fun _ : ℝ => x.fst)).prodMk (noisePrefix_parameter_continuous x.snd)
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ NoiseSpace).symm.continuous.comp h

theorem tensorMap_parameter_continuous (A B : HilbertDatum)
    (f : ℝ→A.Carrier→L[ℝ] A.Carrier) (g : ℝ→B.Carrier→L[ℝ] B.Carrier)
    (hf : ∀T x,‖f T x‖≤‖x‖) (hg : ∀T y,‖g T y‖≤‖y‖)
    (hfc : ∀x,Continuous (fun T => f T x)) (hgc : ∀y,Continuous (fun T => g T y))
    (z : (tensor A B).Carrier) : Continuous (fun T => tensorMap A B (f T) (g T) z) := by
  have hclosed := parameter_continuity_closed (fun T => tensorMap A B (f T) (g T))
    (fun T => tensorMap_norm_le A B (f T) (g T) (hf T) (hg T))
  refine Completion.induction_on z hclosed ?_
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    change Continuous (fun T => tensorMap A B (f T) (g T) (pure A B x y))
    convert (pureBilinear A B).isBoundedBilinearMap.continuous.comp
      ((hfc x).prodMk (hgc y)) using 1
    funext T
    exact tensorMap_pure A B (f T) (g T) x y
  | add z w hz hw =>
    convert hz.add hw using 1
    ext T
    simp only [Completion.coe_add,map_add,Pi.add_apply]

theorem finiteTensorMap_parameter_continuous (n : ℕ) (A : Fin n→HilbertDatum)
    (f : ℝ→(i : Fin n)→(A i).Carrier→L[ℝ] (A i).Carrier)
    (hf : ∀T i x,‖f T i x‖≤‖x‖) (hfc : ∀i x,Continuous (fun T => f T i x))
    (z : (finiteTensor n A).Carrier) : Continuous (fun T => finiteTensorMap n A (f T) z) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact tensorMap_parameter_continuous (A 0) (finiteTensor n (fun i => A i.succ))
      (fun T => f T 0) (fun T => finiteTensorMap n (fun i => A i.succ) (fun i => f T i.succ))
      (fun T => hf T 0) (fun T => finiteTensorMap_norm_le n _ _ (fun i => hf T i.succ))
      (hfc 0) (fun w => ih (fun i => A i.succ) (fun T i => f T i.succ)
        (fun T i => hf T i.succ) (fun i => hfc i.succ) w) z

theorem fiberPrefix_parameter_continuous {m : ℕ} (t : Tree m) (x : (fiber t).Carrier) :
    Continuous (fun T : ℝ => fiberPrefix T t x) := by
  induction t with
  | leaf => exact leafPrefix_parameter_continuous x
  | graft ts ih =>
    exact finiteTensorMap_parameter_continuous m (fun i => fiber (ts i))
      (fun T i => fiberPrefix T (ts i)) (fun T i => fiberPrefix_norm_le T (ts i)) ih x

theorem timePrefix_parameter_continuous {m : ℕ} (x : Space m) :
    Continuous (fun T : ℝ => timePrefix T x) := by
  classical
  have hclosed := parameter_continuity_closed (timePrefixL m) (fun T => timePrefix_norm_le T)
  apply hclosed.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ENNReal)≠⊤) x)
  apply Eventually.of_forall
  intro s
  change Continuous (fun T : ℝ => timePrefix T (∑t∈s,lp.single 2 t (x t)))
  have hs (t : Tree m) : Continuous (fun T : ℝ => timePrefix T (lp.single 2 t (x t))) := by
    have he (T : ℝ) : timePrefix T (lp.single 2 t (x t))=lp.single 2 t (fiberPrefix T t (x t)) := by
      ext w
      by_cases hw : w=t
      · subst w
        simp only [timePrefix_apply,lp.single_apply_self]
      · simp only [timePrefix_apply,
          lp.single_apply_ne (E := fun w : Tree m => (fiber w).Carrier) 2 t (x t) hw,
          lp.single_apply_ne (E := fun w : Tree m => (fiber w).Carrier) 2 t (fiberPrefix T t (x t)) hw,map_zero]
    simp_rw [he]
    exact (lp.singleContinuousLinearMap ℝ (fun w : Tree m => (fiber w).Carrier) 2 t).continuous.comp
      (fiberPrefix_parameter_continuous t (x t))
  have he (T : ℝ) : timePrefix T (∑t∈s,lp.single 2 t (x t))=
      ∑t∈s,timePrefix T (lp.single 2 t (x t)) := map_sum (timePrefixL m T) _ _
  simp_rw [he]
  exact continuous_finsetSum s (fun t ht => hs t)

/-- Strongly continuous families of contractions are jointly continuous. -/
theorem parameter_joint_continuity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ℝ→E→L[ℝ] E) (hP : ∀T x,‖P T x‖≤‖x‖)
    (hc : ∀x,Continuous (fun T => P T x)) :
    Continuous (fun z : ℝ×E => P z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  have hx : Tendsto (fun w : ℝ×E => ‖w.2-z.2‖) (𝓝 z) (𝓝 0) := by
    simpa only [sub_self,norm_zero] using
      ((continuous_snd : Continuous (fun w : ℝ×E => w.2)).continuousAt (x := z)).tendsto.sub_const z.2 |>.norm
  have hT : Tendsto (fun w : ℝ×E => ‖P w.1 z.2-P z.1 z.2‖)
      (𝓝 z) (𝓝 0) := by
    simpa only [Function.comp_def,sub_self,norm_zero] using
      ((((hc z.2).comp continuous_fst).continuousAt (x := z)).tendsto.sub_const
        (P z.1 z.2)).norm
  apply squeeze_zero (fun w => norm_nonneg _) _ (by simpa only [zero_add] using hx.add hT)
  intro w
  calc
    _ = ‖P w.1 (w.2-z.2)+(P w.1 z.2-P z.1 z.2)‖ := by
      congr 1
      rw [map_sub]
      abel
    _ ≤ ‖P w.1 (w.2-z.2)‖+‖P w.1 z.2-P z.1 z.2‖ := norm_add_le _ _
    _ ≤ ‖w.2-z.2‖+‖P w.1 z.2-P z.1 z.2‖ := add_le_add (hP _ _) le_rfl

/-- Joint continuity of the actual time cutoff and its vector input. -/
theorem timePrefix_joint_continuous (m : ℕ) :
    Continuous (fun z : ℝ×Space m => timePrefix z.1 z.2) :=
  parameter_joint_continuity (timePrefixL m) (fun T => timePrefix_norm_le T)
    timePrefix_parameter_continuous

end SphericalAging.TimePrefixContinuity
