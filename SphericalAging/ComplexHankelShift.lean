module

public import SphericalAging.ComplexHankelShiftNorm
public import Mathlib.Analysis.Normed.Operator.Extend

public section

/-! Constructed bounded time-shift operators on the actual Hankel RKHS. -/
noncomputable section
open Set Submodule
open scoped InnerProductSpace NNReal ComplexConjugate
namespace SphericalAging.ComplexHankelShift
open HankelReflection (HankelPositive)
open ComplexHankelShiftNorm

@[expose] def rawMap (c : ℝ → ℝ) (hc : HankelPositive c) (t : ℝ≥0) :
    (ℝ≥0 →₀ ℂ) →ₗ[ℂ] Space c hc :=
  Finsupp.linearCombination ℂ (fun a => feature c hc (a+t))

@[simp] theorem rawMap_single (c : ℝ → ℝ) (hc : HankelPositive c)
    (t a : ℝ≥0) (w : ℂ) : rawMap c hc t (Finsupp.single a w)=w • feature c hc (a+t) := by
  simp [rawMap]

theorem rawMap_norm_contracts {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) (t : ℝ≥0) (f : ℝ≥0 →₀ ℂ) :
    ‖rawMap c hc t f‖≤‖rawMap c hc 0 f‖ := by
  classical
  let e := (Fintype.equivFin f.support).symm
  let a : Fin (Fintype.card f.support) → ℝ≥0 := fun i => (e i:ℝ≥0)
  let w : Fin (Fintype.card f.support) → ℂ := fun i => f (a i)
  have he (s : ℝ≥0) : rawMap c hc s f=combination c hc a w s := by
    unfold rawMap
    rw [Finsupp.linearCombination_apply]
    unfold Finsupp.sum combination
    symm
    calc
      _ = ∑ i : f.support,f (i:ℝ≥0) • feature c hc ((i:ℝ≥0)+s) :=
        e.sum_comp (fun i : f.support => f (i:ℝ≥0) • feature c hc ((i:ℝ≥0)+s))
      _ = _ := by
        simpa only using Finset.sum_coe_sort f.support
          (fun i : ℝ≥0 => f i • feature c hc (i+s))
  rw [he t,he 0]
  exact combination_shift_contracts hc hb a w t

theorem feature_span_eq_kernel_span (c : ℝ → ℝ) (hc : HankelPositive c) :
    span ℂ (Set.range (feature c hc))=
      span ℂ {RKHS.kerFun (Space c hc) x v | (x : ℝ≥0) (v : ℂ)} := by
  apply le_antisymm
  · apply span_le.mpr
    rintro v ⟨x,rfl⟩
    apply subset_span
    exact ⟨x,1,rfl⟩
  · apply span_le.mpr
    rintro v ⟨x,w,rfl⟩
    have he : RKHS.kerFun (Space c hc) x w=w • feature c hc x := by
      simpa only [ComplexHankelShiftNorm.feature,ComplexHilbertKernel.feature,smul_eq_mul,mul_one]
        using (RKHS.kerFun (Space c hc) x).map_smul w 1
    rw [he]
    exact smul_mem _ w (subset_span (Set.mem_range_self x))

theorem rawMap_dense (c : ℝ → ℝ) (hc : HankelPositive c) :
    DenseRange (rawMap c hc 0) := by
  change Dense ((LinearMap.range (rawMap c hc 0)):Set (Space c hc))
  apply dense_iff_topologicalClosure_eq_top.mpr
  simp only [rawMap,add_zero,Finsupp.range_linearCombination]
  rw [feature_span_eq_kernel_span]
  exact RKHS.kerFun_dense (Space c hc)

@[expose] def shift (c : ℝ → ℝ) (hc : HankelPositive c) (t : ℝ≥0) :
    Space c hc →L[ℂ] Space c hc :=
  (rawMap c hc t).extendOfNorm (rawMap c hc 0)

theorem shift_rawMap {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) (t : ℝ≥0) (f : ℝ≥0 →₀ ℂ) :
    shift c hc t (rawMap c hc 0 f)=rawMap c hc t f := by
  apply LinearMap.extendOfNorm_eq (rawMap_dense c hc)
  exact ⟨1,fun f => by simpa only [one_mul] using rawMap_norm_contracts hc hb t f⟩

theorem shift_feature {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) (t a : ℝ≥0) :
    shift c hc t (feature c hc a)=feature c hc (a+t) := by
  have h := shift_rawMap hc hb t (Finsupp.single a 1)
  simpa only [rawMap_single,add_zero,one_smul] using h

theorem shift_norm_le {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) (t : ℝ≥0) (v : Space c hc) :
    ‖shift c hc t v‖≤‖v‖ := by
  have h := LinearMap.norm_extendOfNorm_apply_le (rawMap_dense c hc) 1
    (fun f => by simpa only [one_mul] using rawMap_norm_contracts hc hb t f) v
  simpa only [shift,one_mul] using h

theorem ext_features {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {c : ℝ → ℝ} (hc : HankelPositive c) {A B : Space c hc →L[ℂ] E}
    (h : ∀ a : ℝ≥0,A (feature c hc a)=B (feature c hc a)) : A=B := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  refine (rawMap_dense c hc).induction_on (p:=fun v => A v=B v) v
    (isClosed_eq A.continuous B.continuous) ?_
  intro f
  simp only [rawMap,Finsupp.linearCombination_apply,Finsupp.sum,add_zero,
    map_sum,map_smul,h]

@[simp] theorem shift_zero {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) : shift c hc 0=ContinuousLinearMap.id ℂ _ := by
  apply ext_features hc
  intro a
  simp only [shift_feature hc hb,add_zero,ContinuousLinearMap.id_apply]

theorem shift_add {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) (s t : ℝ≥0) :
    shift c hc (s+t)=(shift c hc s).comp (shift c hc t) := by
  apply ext_features hc
  intro a
  simp only [ContinuousLinearMap.comp_apply,shift_feature hc hb]
  congr 1
  ac_rfl

theorem shift_inner_symmetric {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) (t : ℝ≥0) (v w : Space c hc) :
    ⟪shift c hc t v,w⟫_ℂ=⟪v,shift c hc t w⟫_ℂ := by
  classical
  refine (rawMap_dense c hc).induction_on₂
    (p:=fun v w => ⟪shift c hc t v,w⟫_ℂ=⟪v,shift c hc t w⟫_ℂ)
    (isClosed_eq
      ((shift c hc t).continuous.comp continuous_fst |>.inner continuous_snd)
      (continuous_fst.inner ((shift c hc t).continuous.comp continuous_snd)))
    (fun f g => ?_) v w
  change ⟪shift c hc t (rawMap c hc 0 f),rawMap c hc 0 g⟫_ℂ=
    ⟪rawMap c hc 0 f,shift c hc t (rawMap c hc 0 g)⟫_ℂ
  rw [shift_rawMap hc hb,shift_rawMap hc hb]
  simp only [rawMap,Finsupp.linearCombination_apply,Finsupp.sum,add_zero,
    inner_sum,sum_inner,inner_smul_left,inner_smul_right,
    ComplexHankelShiftNorm.feature_inner,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  ring


end SphericalAging.ComplexHankelShift
