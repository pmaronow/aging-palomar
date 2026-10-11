module

public import SphericalAging.CenterAverageReal
public import SphericalAging.TreeEnergyHomogeneity

public section

/-! The actual white-leaf identity and deterministic remote response bound. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.WhitePrefixResponse
open CKSpecification CKPhysicalConsequences CausalTree CausalTreeRealization
open PrefixReflection PrefixRectangleStability CenterAverageReal CausalCenterAverage GreenCovariance CKKernelBounds

theorem ckTreeState_height_zero {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0≤t) :
    heightPrefix 0 (ckTreeState h t)=baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) t :=
  treeLimit_heightPrefix (p-1) (β*Real.sqrt p) (clampedResponse d) (clampedResponse_continuous h)
    t (ckTreeIterate_tendsto h (physical_bounds_of_equations h) ht) 0

/-- Exact white-prefix identity including the actual initial-response atom. -/
theorem white_prefix_norm {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T t : ℝ} (hT : 0≤T) (ht : T≤t) :
    ‖heightPrefix 0 (prefixVector h T t)‖^2=(d.R t 0)^2+2*(∫ u in (0:ℝ)..T,(d.R t u)^2) := by
  have he : heightPrefix 0 (prefixVector h T t)=timePrefix T
      (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) t) := by
    unfold prefixVector
    rw [←timePrefix_heightPrefix_commute,ckTreeState_height_zero h (hT.trans ht)]
  rw [he,←real_inner_self_eq_norm_sq,projectedBase_inner h hT ht ht]
  simp only [pow_two]

/-- Source S_2(t,L), defined on the full real ray by a harmless cutoff at zero. -/
@[expose] def remoteTail (d : CKData) (t L : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..max 0 (t-L),(d.R t u)^2

theorem remoteTail_nonneg (d : CKData) (t L : ℝ) : 0≤remoteTail d t L :=
  intervalIntegral.integral_nonneg (le_max_left _ _) (fun _ _ => sq_nonneg _)

/-- Actual remote response is carried by the constructed white-leaf prefix. -/
theorem remoteTail_le_white {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t L : ℝ} (hL : 0≤L) (ht : L≤t) :
    2*remoteTail d t L≤‖heightPrefix 0 (localCenter h (t-L) L)‖^2 := by
  have hh := white_prefix_norm h (sub_nonneg.mpr ht) (by linarith : t-L≤t)
  unfold remoteTail localCenter
  rw [max_eq_right (sub_nonneg.mpr ht),sub_add_cancel]
  rw [hh]
  nlinarith [sq_nonneg (d.R t 0)]

theorem remoteTail_le_center {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t L : ℝ} (hL : 0≤L) (ht : L≤t) :
    2*remoteTail d t L≤‖localCenter h (t-L) L‖^2 := by
  apply (remoteTail_le_white h hL ht).trans
  apply pow_le_pow_left₀ (norm_nonneg _) (mask_norm_le {τ | τ.height≤0} _) 2

/-- The genuine source basic-tail bound, all p≥3 and all plateaux. -/
theorem basic_remote_tail {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {c : ℝ → ℝ} {L : ℝ} (hL : 0≤L)
    (hQ : TendstoUniformlyOn (fun T => Function.uncurry (futureKernel h T))
      (fun z => c (z.1+z.2)) atTop (square L)) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ t : ℝ in atTop,remoteTail d t L≤c (2*L)/2+ε := by
  have hn := (center_real_norm_limit h hL hQ).pow 2
  have hA : 0≤c (2*L) := by
    have hl := hQ.tendsto_at (x:=(L,L)) ⟨⟨hL,le_rfl⟩,⟨hL,le_rfl⟩⟩
    change Tendsto (fun T => futureKernel h T L L) atTop (nhds (c (L+L))) at hl
    rw [show L+L=2*L by ring] at hl
    apply ge_of_tendsto' hl
    intro T
    change 0 ≤ inner ℝ (localCenter h T L) (localCenter h T L)
    exact real_inner_self_nonneg
  rw [Real.sq_sqrt hA] at hn
  have hs : Tendsto (fun t : ℝ => t-L) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-L) tendsto_id
  have hb := (hn.comp hs).eventually (gt_mem_nhds (by linarith : c (2*L)<c (2*L)+2*ε))
  filter_upwards [eventually_ge_atTop L,hb] with t ht hb
  have htbound := remoteTail_le_center h hL ht
  dsimp only [Function.comp_def] at hb
  linarith

/-- With a zero plateau, no remote squared response mass remains, for every p. -/
theorem zero_plateau_remote_localization {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {c : ℝ → ℝ} (hlim : Tendsto c atTop (nhds 0))
    (hQ : ∀ A : ℝ,0≤A → TendstoUniformlyOn
      (fun T => Function.uncurry (futureKernel h T)) (fun z => c (z.1+z.2)) atTop (square A))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop,0<L ∧ ∀ᶠ t : ℝ in atTop,remoteTail d t L≤ε := by
  have htwo : Tendsto (fun L : ℝ => 2*L) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (show (0:ℝ)<2 by norm_num)).mpr tendsto_id
  have hs := (hlim.comp htwo).eventually (gt_mem_nhds hε)
  filter_upwards [eventually_gt_atTop (0:ℝ),hs] with L hL hs
  refine ⟨hL,?_⟩
  dsimp only [Function.comp_def] at hs
  filter_upwards [basic_remote_tail h hL.le (hQ L hL.le) (by positivity : 0<ε/2)] with t ht
  linarith

end SphericalAging.WhitePrefixResponse
