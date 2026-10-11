module

public import SphericalAging.CKKernelBounds
public import SphericalAging.UniformMultiplier
public import SphericalAging.CKPhysicalConsequences
public import SphericalAging.GlobalCKExtension
public import SphericalAging.CKDiagonalRegularity
public import SphericalAging.ColoredEnergyRegularity
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.Sequences

public section

/-! Actual response derivative and bounded-lag estimates, and compact
extraction for translated CK kernels. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalAging.ResponseCompactness
open CKSpecification GreenCovariance BackwardResponse CKKernelBounds UniformMultiplier
open CKPhysicalConsequences

/-- A bounded equicontinuous family of continuous real functions on a
locally compact sigma-compact space has a compact set containing its range.
The compact set is derived from the pointwise closure and Arzelà–Ascoli. -/
theorem bounded_equicontinuous_compact {X : Type*} [TopologicalSpace X]
    (F : ℕ → C(X,ℝ)) (B : ℝ)
    (hBound : ∀ n x, |F n x| ≤ B)
    (hEqui : Equicontinuous (fun n x => F n x)) :
    ∃ S : Set C(X,ℝ), IsCompact S ∧ ∀ n, F n ∈ S := by
  let A : Set (X → ℝ) := closure (range (fun n => (F n : X → ℝ)))
  have hEqA : A.Equicontinuous := (equicontinuous_iff_range.mp hEqui).closure
  have hSubset : A ⊆ Set.pi univ (fun _ => Icc (-B) B) := by
    apply closure_minimal
    · rintro f ⟨n,rfl⟩ x _
      exact abs_le.mp (hBound n x)
    · exact isClosed_set_pi (fun _ _ => isClosed_Icc)
  have hCompactA : IsCompact A :=
    (isCompact_univ_pi (fun _ => isCompact_Icc)).of_isClosed_subset isClosed_closure hSubset
  let S : Set C(X,ℝ) := {f | (f : X → ℝ) ∈ A}
  have hImage : ContinuousMap.toFun '' S=A := by
    ext f
    constructor
    · rintro ⟨g,hg,rfl⟩
      exact hg
    · intro hf
      exact ⟨⟨f,hEqA.continuous_of_mem hf⟩,hf,rfl⟩
  have hEquiS : Equicontinuous ((↑) : S → X → ℝ) :=
    hEqA.comp (fun f : S => ⟨(f.1 : X → ℝ),f.2⟩)
  refine ⟨S,ArzelaAscoli.isCompact_of_equicontinuous S (hImage.symm ▸ hCompactA) hEquiS,?_⟩
  intro n
  exact subset_closure (mem_range_self n)

/-- The extraction gives one subsequence converging uniformly on every
compact subset of the domain. -/
theorem bounded_equicontinuous_subsequence {X : Type*} [TopologicalSpace X]
    [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]
    (F : ℕ → C(X,ℝ)) (B : ℝ)
    (hBound : ∀ n x, |F n x| ≤ B)
    (hEqui : Equicontinuous (fun n x => F n x)) :
    ∃ f : C(X,ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ K : Set X, IsCompact K → TendstoUniformlyOn (fun n x => F (φ n) x) f atTop K := by
  obtain ⟨S,hS,hFS⟩ := bounded_equicontinuous_compact F B hBound hEqui
  obtain ⟨f,_,φ,hφ,hconv⟩ := hS.tendsto_subseq hFS
  exact ⟨f,φ,hφ,(ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hconv)⟩

/-- The exact derivative estimate in Proposition 4.6, from the equations
alone: physical bounds and the sharp multiplier ceiling are already proved. -/
theorem response_partial_derivative_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    |responseSlope p β d t s|+|backwardSlope p β d t s| ≤
      2*(multiplierCeiling p β+memoryCoefficient p β*(t-s)) := by
  have hb := physical_bounds_of_equations h
  have hPSD := correlation_psd_of_equations h
  have hmt := multiplier_uniform_bound h hb hPSD (hs.trans hst)
  have hms := multiplier_uniform_bound h hb hPSD hs
  apply CKKernelBounds.response_partial_derivative_bound h hb hs hst
  · rw [abs_of_nonneg (by linarith : 0 ≤ d.multiplier t)]
    exact hmt.2
  · rw [abs_of_nonneg (by linarith : 0 ≤ d.multiplier s)]
    exact hms.2

theorem responseSlope_uniform_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    |responseSlope p β d t s| ≤ multiplierCeiling p β+memoryCoefficient p β*(t-s) := by
  have hb := physical_bounds_of_equations h
  have hmt := multiplier_uniform_bound h hb (correlation_psd_of_equations h) (hs.trans hst)
  apply responseSlope_abs_bound h hb hs hst
  rw [abs_of_nonneg (by linarith : 0 ≤ d.multiplier t)]
  exact hmt.2

theorem backwardSlope_uniform_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    |backwardSlope p β d t s| ≤ multiplierCeiling p β+memoryCoefficient p β*(t-s) := by
  have hb := physical_bounds_of_equations h
  have hms := multiplier_uniform_bound h hb (correlation_psd_of_equations h) hs
  apply backwardSlope_abs_bound h hb hs hst
  rw [abs_of_nonneg (by linarith : 0 ≤ d.multiplier s)]
  exact hms.2

/-- Forward row Lipschitz control on an actual bounded causal interval. -/
theorem response_forward_difference_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a b s : ℝ} (hs : 0 ≤ s) (hsa : s ≤ a) (hab : a ≤ b) :
    |d.R b s-d.R a s| ≤ (multiplierCeiling p β+memoryCoefficient p β*(b-s))*|b-a| := by
  have hh := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x => d.R x s) (f' := fun x => responseSlope p β d x s)
    (C := multiplierCeiling p β+memoryCoefficient p β*(b-s))
    (fun x hx => (h.response_derivative x s hs (hsa.trans hx.1)).mono
      (fun z hz => hsa.trans hz.1))
    (fun x hx => by
      rw [Real.norm_eq_abs]
      exact (responseSlope_uniform_bound h hs (hsa.trans hx.1)).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2 s)
          (memoryCoefficient_nonnegative (β := β) h.spin_ge_three))))
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  simpa only [Real.norm_eq_abs] using hh

/-- Earlier-time row Lipschitz control, including its causal diagonal. -/
theorem response_backward_difference_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a b t : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbt : b ≤ t) :
    |d.R t b-d.R t a| ≤ (multiplierCeiling p β+memoryCoefficient p β*(t-a))*|b-a| := by
  have hh := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x => d.R t x) (f' := fun x => backwardSlope p β d t x)
    (C := multiplierCeiling p β+memoryCoefficient p β*(t-a))
    (fun x hx => (response_backward_hasDerivWithinAt h (ha.trans hx.1) (hx.2.trans hbt)).mono
      (fun z hz => ⟨ha.trans hz.1,hz.2.trans hbt⟩))
    (fun x hx => by
      rw [Real.norm_eq_abs]
      exact (backwardSlope_uniform_bound h (ha.trans hx.1) (hx.2.trans hbt)).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left (sub_le_sub_left hx.1 t)
          (memoryCoefficient_nonnegative (β := β) h.spin_ge_three))))
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  simpa only [Real.norm_eq_abs] using hh

theorem response_forward_pair_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a b s : ℝ} (hs : 0 ≤ s) (hsa : s ≤ a) (hsb : s ≤ b) :
    |d.R b s-d.R a s| ≤
      (multiplierCeiling p β+memoryCoefficient p β*(max a b-s))*|b-a| := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab]
    exact response_forward_difference_bound h hs hsa hab
  · rw [max_eq_left hba,abs_sub_comm (d.R b s) (d.R a s),abs_sub_comm b a]
    exact response_forward_difference_bound h hs hsb hba

theorem response_backward_pair_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hat : a ≤ t) (hbt : b ≤ t) :
    |d.R t b-d.R t a| ≤
      (multiplierCeiling p β+memoryCoefficient p β*(t-min a b))*|b-a| := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    exact response_backward_difference_bound h ha hab hbt
  · rw [min_eq_right hba,abs_sub_comm (d.R t b) (d.R t a),abs_sub_comm b a]
    exact response_backward_difference_bound h hb hba hat

/-- A path staying in the causal triangle gives joint response Lipschitz
control. It goes through the larger row time, so it never crosses causality. -/
theorem response_joint_difference_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s u v : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hv : 0 ≤ v) (hvu : v ≤ u) :
    |d.R t s-d.R u v| ≤
      (multiplierCeiling p β+memoryCoefficient p β*(max t u-min s v))*(|t-u|+|s-v|) := by
  let K := multiplierCeiling p β+memoryCoefficient p β*(max t u-min s v)
  have hM := memoryCoefficient_nonnegative (β := β) h.spin_ge_three
  have h1 := response_forward_difference_bound h hs hst (le_max_left t u)
  have h2 := response_forward_difference_bound h hv hvu (le_max_right t u)
  have h3 := response_backward_pair_bound h hs hv
    (hst.trans (le_max_left t u)) (hvu.trans (le_max_right t u))
  have hb1 : |d.R (max t u) s-d.R t s| ≤ K*|max t u-t| := h1.trans (by
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (sub_le_sub_left (min_le_left s v) (max t u)) hM))
  have hb2 : |d.R (max t u) v-d.R u v| ≤ K*|max t u-u| := h2.trans (by
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (sub_le_sub_left (min_le_right s v) (max t u)) hM))
  have hmax : |max t u-t|+|max t u-u|=|t-u| := by
    rcases le_total t u with htu | hut
    · rw [max_eq_right htu,sub_self,abs_zero,add_zero,abs_sub_comm]
    · rw [max_eq_left hut,sub_self,abs_zero,zero_add]
  calc
    |d.R t s-d.R u v| ≤ |d.R t s-d.R (max t u) s|+
        |d.R (max t u) s-d.R (max t u) v|+|d.R (max t u) v-d.R u v| := by
      exact (abs_sub_le _ _ _).trans (add_le_add_left (abs_sub_le _ _ _) _)
    _ ≤ K*|max t u-t|+K*|s-v|+K*|max t u-u| := by
      rw [abs_sub_comm (d.R t s) (d.R (max t u) s),
        abs_sub_comm (d.R (max t u) s) (d.R (max t u) v),abs_sub_comm s v]
      exact add_le_add (add_le_add hb1 h3) hb2
    _ = K*(|max t u-t|+|max t u-u|+|s-v|) := by ring
    _ = _ := by rw [hmax]

@[expose] abbrev CausalOffsets := {z : ℝ × ℝ // z.2 ≤ z.1}

instance causalOffsets_proper : ProperSpace CausalOffsets :=
  ProperSpace.of_isClosed (isClosed_le continuous_snd continuous_fst)

/-- Causal clamping at a translated point is exactly clamping its two
physical times; their order is preserved. -/
theorem translated_clampedResponse_eq (d : CKData) (T : ℝ) (z : CausalOffsets) :
    clampedResponse d (T+z.1.1) (T+z.1.2)=
      d.R (max 0 (T+z.1.1)) (max 0 (T+z.1.2)) := by
  unfold clampedResponse
  rw [max_comm (0 : ℝ) (T+z.1.2),←max_assoc,
    max_eq_left (add_le_add le_rfl z.2),max_comm (T+z.1.1) 0,
    max_comm (T+z.1.2) 0]

@[expose] def offsetBudget (z w : CausalOffsets) : ℝ := |z.1.1|+|z.1.2|+|w.1.1|+|w.1.2|

theorem positivePart_translated_difference_bound (T a b : ℝ) :
    |max 0 (T+a)-max 0 (T+b)| ≤ |a-b| := by
  simpa only [max_comm (0 : ℝ),add_sub_add_left_eq_sub] using
    abs_max_sub_max_le_abs (T+a) (T+b) 0

theorem translated_lag_bound (T : ℝ) (z w : CausalOffsets) :
    max (max 0 (T+z.1.1)) (max 0 (T+w.1.1))-
      min (max 0 (T+z.1.2)) (max 0 (T+w.1.2)) ≤ offsetBudget z w := by
  have hgap (a b : ℝ) : max 0 (T+a)-max 0 (T+b) ≤ |a|+|b| := by
    exact (le_abs_self _).trans ((positivePart_translated_difference_bound T a b).trans
      (by simpa only [sub_zero,zero_sub,abs_neg] using (abs_sub_le a 0 b)))
  have h1 := hgap z.1.1 z.1.2
  have h2 := hgap z.1.1 w.1.2
  have h3 := hgap w.1.1 z.1.2
  have h4 := hgap w.1.1 w.1.2
  unfold offsetBudget
  rcases le_total (max 0 (T+z.1.1)) (max 0 (T+w.1.1)) with ht | ht <;>
    rcases le_total (max 0 (T+z.1.2)) (max 0 (T+w.1.2)) with hs | hs
  · rw [max_eq_right ht,min_eq_left hs]
    linarith [abs_nonneg z.1.1,abs_nonneg w.1.2]
  · rw [max_eq_right ht,min_eq_right hs]
    linarith [abs_nonneg z.1.1,abs_nonneg z.1.2]
  · rw [max_eq_left ht,min_eq_left hs]
    linarith [abs_nonneg w.1.1,abs_nonneg w.1.2]
  · rw [max_eq_left ht,min_eq_right hs]
    linarith [abs_nonneg z.1.2,abs_nonneg w.1.1]

theorem multiplierCeiling_nonnegative (p : ℕ) (β : ℝ) : 0 ≤ multiplierCeiling p β := by
  unfold multiplierCeiling
  positivity

/-- Actual uniform local Lipschitz modulus of every translated response,
including negative offsets and causal boundary points. -/
theorem translated_response_difference_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℝ) (z w : CausalOffsets) :
    |clampedResponse d (T+z.1.1) (T+z.1.2)-
        clampedResponse d (T+w.1.1) (T+w.1.2)| ≤
      2*(multiplierCeiling p β+memoryCoefficient p β*offsetBudget z w)*dist z w := by
  rw [translated_clampedResponse_eq,translated_clampedResponse_eq]
  have hM := memoryCoefficient_nonnegative (β := β) h.spin_ge_three
  have hL := multiplierCeiling_nonnegative p β
  have hst : max 0 (T+z.1.2) ≤ max 0 (T+z.1.1) := max_le_max le_rfl (add_le_add le_rfl z.2)
  have huv : max 0 (T+w.1.2) ≤ max 0 (T+w.1.1) := max_le_max le_rfl (add_le_add le_rfl w.2)
  have hh := response_joint_difference_bound h (le_max_left 0 _) hst (le_max_left 0 _) huv
  have hK : multiplierCeiling p β+memoryCoefficient p β*
      (max (max 0 (T+z.1.1)) (max 0 (T+w.1.1))-
        min (max 0 (T+z.1.2)) (max 0 (T+w.1.2))) ≤
      multiplierCeiling p β+memoryCoefficient p β*offsetBudget z w :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_left (translated_lag_bound T z w) hM)
  have hBudget : 0 ≤ offsetBudget z w := by unfold offsetBudget; positivity
  have hKnonneg : 0 ≤ multiplierCeiling p β+memoryCoefficient p β*offsetBudget z w :=
    add_nonneg hL (mul_nonneg hM hBudget)
  have hdist : |z.1.1-w.1.1|+|z.1.2-w.1.2| ≤ 2*dist z w := by
    rw [Subtype.dist_eq,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    linarith [le_max_left |z.1.1-w.1.1| |z.1.2-w.1.2|,
      le_max_right |z.1.1-w.1.1| |z.1.2-w.1.2|]
  calc
    _ ≤ _ := hh
    _ ≤ (multiplierCeiling p β+memoryCoefficient p β*offsetBudget z w)*
        (|z.1.1-w.1.1|+|z.1.2-w.1.2|) :=
      mul_le_mul hK (add_le_add (positivePart_translated_difference_bound T z.1.1 w.1.1)
        (positivePart_translated_difference_bound T z.1.2 w.1.2))
        (add_nonneg (abs_nonneg _) (abs_nonneg _)) hKnonneg
    _ ≤ (multiplierCeiling p β+memoryCoefficient p β*offsetBudget z w)*(2*dist z w) :=
      mul_le_mul_of_nonneg_left hdist hKnonneg
    _ = _ := by ring

@[expose] def translatedResponseMap {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℝ) : C(CausalOffsets,ℝ) where
  toFun z := clampedResponse d (T+z.1.1) (T+z.1.2)
  continuous_toFun := (clampedResponse_continuous h).comp
    ((continuous_const.add continuous_subtype_val.fst).prodMk
      (continuous_const.add continuous_subtype_val.snd))

theorem translated_response_equicontinuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℕ → ℝ) :
    Equicontinuous (fun n z => translatedResponseMap h (T n) z) := by
  intro z
  let b : CausalOffsets → ℝ := fun w =>
    2*(multiplierCeiling p β+memoryCoefficient p β*offsetBudget z w)*dist z w
  have hb : Continuous b := by unfold b offsetBudget; fun_prop
  apply Metric.equicontinuousAt_of_continuity_modulus b
    (by simpa only [b,dist_self,mul_zero] using hb.tendsto z)
    (fun n w => translatedResponseMap h (T n) w)
  exact Eventually.of_forall (fun w n => by
    rw [Real.dist_eq]
    exact translated_response_difference_bound h (T n) z w)

/-- One subsequence of translated responses converges uniformly on every
compact causal set. This is actual Arzelà–Ascoli, with no compactness premise. -/
theorem translated_response_subsequence {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℕ → ℝ) :
    ∃ r : C(CausalOffsets,ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ K : Set CausalOffsets, IsCompact K →
        TendstoUniformlyOn (fun n z => clampedResponse d
          (T (φ n)+z.1.1) (T (φ n)+z.1.2)) r atTop K := by
  apply bounded_equicontinuous_subsequence (translatedResponseMap h ∘ T) 1
  · intro n z
    exact clampedResponse_abs_le_one h (physical_bounds_of_equations h) _ _
  · exact translated_response_equicontinuous h T

theorem correlation_left_pair_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s) :
    |d.C b s-d.C a s| ≤ Real.sqrt (2*multiplierCeiling p β*|b-a|) := by
  rcases le_total a b with hab | hba
  · have hh := CKDiagonalRegularity.correlation_coordinate_modulus h ha hs (sub_nonneg.mpr hab)
    rw [add_sub_cancel] at hh
    rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    exact hh
  · have hh := CKDiagonalRegularity.correlation_coordinate_modulus h hb hs (sub_nonneg.mpr hba)
    rw [add_sub_cancel] at hh
    rw [abs_sub_comm (d.C b s) (d.C a s),abs_sub_comm b a,
      abs_of_nonneg (sub_nonneg.mpr hba)]
    exact hh

theorem correlation_right_pair_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t) :
    |d.C t b-d.C t a| ≤ Real.sqrt (2*multiplierCeiling p β*|b-a|) := by
  rw [h.correlation_symmetric t b ht hb,h.correlation_symmetric t a ht ha]
  exact correlation_left_pair_bound h ha hb ht

/-- A common global Hölder modulus for every translated covariance. -/
theorem translated_correlation_difference_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℝ) (z w : ℝ × ℝ) :
    |clampedCorrelation d (T+z.1) (T+z.2)-clampedCorrelation d (T+w.1) (T+w.2)| ≤
      2*Real.sqrt (2*multiplierCeiling p β*dist z w) := by
  have hL := multiplierCeiling_nonnegative p β
  have hc1 := correlation_left_pair_bound h (le_max_left 0 (T+w.1))
    (le_max_left 0 (T+z.1)) (le_max_left 0 (T+z.2))
  have hc2 := correlation_right_pair_bound h (le_max_left 0 (T+w.2))
    (le_max_left 0 (T+z.2)) (le_max_left 0 (T+w.1))
  have hd1 : |max 0 (T+z.1)-max 0 (T+w.1)| ≤ dist z w :=
    (positivePart_translated_difference_bound T z.1 w.1).trans (by
      rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
      exact le_max_left _ _)
  have hd2 : |max 0 (T+z.2)-max 0 (T+w.2)| ≤ dist z w :=
    (positivePart_translated_difference_bound T z.2 w.2).trans (by
      rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
      exact le_max_right _ _)
  have hb1 := hc1.trans (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hd1
    (mul_nonneg (by norm_num) hL)))
  have hb2 := hc2.trans (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hd2
    (mul_nonneg (by norm_num) hL)))
  unfold clampedCorrelation
  exact (abs_sub_le _ _ _).trans (by linarith only [hb1,hb2])

@[expose] def translatedCorrelationMap {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℝ) : C(ℝ × ℝ,ℝ) where
  toFun z := clampedCorrelation d (T+z.1) (T+z.2)
  continuous_toFun := (clampedCorrelation_continuous h).comp
    ((continuous_const.add continuous_fst).prodMk (continuous_const.add continuous_snd))

theorem translated_correlation_equicontinuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℕ → ℝ) :
    Equicontinuous (fun n z => translatedCorrelationMap h (T n) z) := by
  have hb : Continuous (fun r : ℝ => 2*Real.sqrt (2*multiplierCeiling p β*r)) := by fun_prop
  apply (Metric.uniformEquicontinuous_of_continuity_modulus
    (fun r : ℝ => 2*Real.sqrt (2*multiplierCeiling p β*r))
    (by simpa using hb.tendsto 0) (fun n z => translatedCorrelationMap h (T n) z)
    (fun z w n => by
      rw [Real.dist_eq]
      exact translated_correlation_difference_bound h (T n) z w)).equicontinuous

theorem translated_correlation_subsequence {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℕ → ℝ) :
    ∃ c : C(ℝ × ℝ,ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ K : Set (ℝ × ℝ), IsCompact K →
        TendstoUniformlyOn (fun n z => clampedCorrelation d
          (T (φ n)+z.1) (T (φ n)+z.2)) c atTop K := by
  apply bounded_equicontinuous_subsequence (translatedCorrelationMap h ∘ T) 1
  · intro n z
    change |clampedCorrelation d (T n+z.1) (T n+z.2)| ≤ 1
    rw [abs_of_nonneg (clampedCorrelation_nonnegative (physical_bounds_of_equations h) _ _)]
    exact ((physical_bounds_of_equations h).1 _ _ (le_max_left _ _) (le_max_left _ _)).2
  · exact translated_correlation_equicontinuous h T

theorem uniformlyOn_subsequence {X : Type*} {F : ℕ → X → ℝ} {f : X → ℝ} {K : Set X}
    {φ : ℕ → ℕ} (hf : TendstoUniformlyOn F f atTop K) (hφ : Tendsto φ atTop atTop) :
    TendstoUniformlyOn (fun n x => F (φ n) x) f atTop K := by
  rw [Metric.tendstoUniformlyOn_iff] at hf ⊢
  intro ε hε
  exact hφ.eventually (hf ε hε)

/-- The same subsequence works for correlation and response, uniformly on
every compact square or causal set respectively. -/
theorem translated_covariance_response_subsequence {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℕ → ℝ) :
    ∃ c : C(ℝ × ℝ,ℝ), ∃ r : C(CausalOffsets,ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ K : Set (ℝ × ℝ), IsCompact K →
        TendstoUniformlyOn (fun n z => clampedCorrelation d
          (T (φ n)+z.1) (T (φ n)+z.2)) c atTop K) ∧
      (∀ K : Set CausalOffsets, IsCompact K →
        TendstoUniformlyOn (fun n z => clampedResponse d
          (T (φ n)+z.1.1) (T (φ n)+z.1.2)) r atTop K) := by
  obtain ⟨c,φC,hφC,hC⟩ := translated_correlation_subsequence h T
  obtain ⟨r,φR,hφR,hR⟩ := translated_response_subsequence h (T ∘ φC)
  refine ⟨c,r,φC ∘ φR,hφC.comp hφR,?_,hR⟩
  intro K hK
  exact uniformlyOn_subsequence (hC K hK) hφR.tendsto_atTop

/-- Negative offsets are harmless: on any fixed compact square the
translated clamped and original correlations are eventually identical. -/
theorem translated_correlation_eventually_eq {d : CKData} {T : ℕ → ℝ}
    (hT : Tendsto T atTop atTop) (K : Set (ℝ × ℝ)) (hK : IsCompact K) :
    ∀ᶠ n in atTop, EqOn (fun z => clampedCorrelation d (T n+z.1) (T n+z.2))
      (fun z => d.C (T n+z.1) (T n+z.2)) K := by
  obtain ⟨M₁,hM₁⟩ := hK.exists_bound_of_continuousOn continuous_fst.continuousOn
  obtain ⟨M₂,hM₂⟩ := hK.exists_bound_of_continuousOn continuous_snd.continuousOn
  filter_upwards [hT.eventually_ge_atTop (max M₁ M₂)] with n hn z hz
  have h1 := hM₁ z hz
  have h2 := hM₂ z hz
  rw [Real.norm_eq_abs] at h1 h2
  have ht : 0 ≤ T n+z.1 := by linarith [le_max_left M₁ M₂,neg_abs_le z.1]
  have hs : 0 ≤ T n+z.2 := by linarith [le_max_right M₁ M₂,neg_abs_le z.2]
  exact clampedCorrelation_eq ht hs

theorem translated_response_eventually_eq {d : CKData} {T : ℕ → ℝ}
    (hT : Tendsto T atTop atTop) (K : Set CausalOffsets) (hK : IsCompact K) :
    ∀ᶠ n in atTop, EqOn (fun z => clampedResponse d (T n+z.1.1) (T n+z.1.2))
      (fun z => d.R (T n+z.1.1) (T n+z.1.2)) K := by
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn continuous_subtype_val.snd.continuousOn
  filter_upwards [hT.eventually_ge_atTop M] with n hn z hz
  have hs := hM z hz
  rw [Real.norm_eq_abs] at hs
  exact clampedResponse_eq (by linarith [neg_abs_le z.1.2]) (add_le_add le_rfl z.2)

/-- Unconditional locally uniform precompactness of the original physical
correlation and response, with the SAME subsequence and arbitrary negative
offsets. No hypothesis of compactness or equicontinuity is inserted. -/
theorem covariance_response_precompact {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    ∃ c : C(ℝ × ℝ,ℝ), ∃ r : C(CausalOffsets,ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ K : Set (ℝ × ℝ), IsCompact K →
        TendstoUniformlyOn (fun n z => d.C
          (T (φ n)+z.1) (T (φ n)+z.2)) c atTop K) ∧
      (∀ K : Set CausalOffsets, IsCompact K →
        TendstoUniformlyOn (fun n z => d.R
          (T (φ n)+z.1.1) (T (φ n)+z.1.2)) r atTop K) := by
  obtain ⟨c,r,φ,hφ,hC,hR⟩ := translated_covariance_response_subsequence h T
  have hTφ := hT.comp hφ.tendsto_atTop
  exact ⟨c,r,φ,hφ,fun K hK => (hC K hK).congr
    (translated_correlation_eventually_eq hTφ K hK),
    fun K hK => (hR K hK).congr (translated_response_eventually_eq hTφ K hK)⟩

/-- A common uniform Hölder modulus for every translated multiplier,
proved from the actual colored-noise Gram decomposition. -/
theorem translated_multiplier_difference_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T a b : ℝ) :
    |clampedMultiplier d (T+a)-clampedMultiplier d (T+b)| ≤
      2*ColoredEnergyRegularity.multiplierHolderFactor p β*
        Real.sqrt (2*(p : ℝ)*multiplierCeiling p β*|a-b|) := by
  have hh := ColoredEnergyRegularity.multiplier_uniform_holder h
    (le_max_left 0 (T+a)) (le_max_left 0 (T+b))
  unfold clampedMultiplier
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
      (positivePart_translated_difference_bound T a b) (by
        have hL := multiplierCeiling_nonnegative p β
        positivity))) (by
      have hk := ColoredEnergyRegularity.multiplierHolderFactor_nonnegative p β
      positivity))

@[expose] def translatedMultiplierMap {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℝ) : C(ℝ,ℝ) where
  toFun a := clampedMultiplier d (T+a)
  continuous_toFun := (clampedMultiplier_continuous h).comp (continuous_const.add continuous_id)

theorem translated_multiplier_equicontinuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℕ → ℝ) :
    Equicontinuous (fun n a => translatedMultiplierMap h (T n) a) := by
  let b : ℝ → ℝ := fun r => 2*ColoredEnergyRegularity.multiplierHolderFactor p β*
    Real.sqrt (2*(p : ℝ)*multiplierCeiling p β*r)
  have hb : Continuous b := by unfold b; fun_prop
  apply (Metric.uniformEquicontinuous_of_continuity_modulus b
    (by simpa [b] using hb.tendsto 0) (fun n a => translatedMultiplierMap h (T n) a)
    (fun a c n => by
      rw [Real.dist_eq]
      exact translated_multiplier_difference_bound h (T n) a c)).equicontinuous

theorem translated_multiplier_subsequence {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℕ → ℝ) :
    ∃ ell : C(ℝ,ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ K : Set ℝ, IsCompact K →
        TendstoUniformlyOn (fun n a => clampedMultiplier d (T (φ n)+a)) ell atTop K := by
  apply bounded_equicontinuous_subsequence (translatedMultiplierMap h ∘ T) (multiplierCeiling p β)
  · intro n a
    have hh := multiplier_uniform_bound h (physical_bounds_of_equations h)
      (correlation_psd_of_equations h) (le_max_left 0 (T n+a))
    change |d.multiplier (max 0 (T n+a))| ≤ multiplierCeiling p β
    rw [abs_of_nonneg (by linarith : 0 ≤ d.multiplier (max 0 (T n+a)))]
    exact hh.2
  · exact translated_multiplier_equicontinuous h T

theorem translated_multiplier_eventually_eq {d : CKData} {T : ℕ → ℝ}
    (hT : Tendsto T atTop atTop) (K : Set ℝ) (hK : IsCompact K) :
    ∀ᶠ n in atTop, EqOn (fun a => clampedMultiplier d (T n+a))
      (fun a => d.multiplier (T n+a)) K := by
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  filter_upwards [hT.eventually_ge_atTop M] with n hn a ha
  have hs := hM a ha
  rw [Real.norm_eq_abs] at hs
  change |a| ≤ M at hs
  change d.multiplier (max 0 (T n+a))=d.multiplier (T n+a)
  rw [max_eq_right (by linarith [neg_abs_le a] : 0 ≤ T n+a)]

/-- Every sequence of waiting times tending to infinity admits a single
strict subsequence for all THREE original CK kernels. Convergence is uniform
on every compact subset of the exact offset domains, including negative
offsets. All regularity and compactness are derived from CK equations. -/
theorem translated_triple_precompact {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    ∃ c : C(ℝ × ℝ,ℝ), ∃ r : C(CausalOffsets,ℝ), ∃ ell : C(ℝ,ℝ),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ K : Set (ℝ × ℝ), IsCompact K →
        TendstoUniformlyOn (fun n z => d.C
          (T (φ n)+z.1) (T (φ n)+z.2)) c atTop K) ∧
      (∀ K : Set CausalOffsets, IsCompact K →
        TendstoUniformlyOn (fun n z => d.R
          (T (φ n)+z.1.1) (T (φ n)+z.1.2)) r atTop K) ∧
      (∀ K : Set ℝ, IsCompact K →
        TendstoUniformlyOn (fun n a => d.multiplier (T (φ n)+a)) ell atTop K) := by
  obtain ⟨c,r,φCR,hφCR,hC,hR⟩ := covariance_response_precompact h hT
  obtain ⟨ell,φL,hφL,hLam⟩ := translated_multiplier_subsequence h (T ∘ φCR)
  have hTφ := hT.comp (hφCR.comp hφL).tendsto_atTop
  refine ⟨c,r,ell,φCR ∘ φL,hφCR.comp hφL,
    (fun K hK => uniformlyOn_subsequence (hC K hK) hφL.tendsto_atTop),
    (fun K hK => uniformlyOn_subsequence (hR K hK) hφL.tendsto_atTop),?_⟩
  intro K hK
  exact (hLam K hK).congr (translated_multiplier_eventually_eq hTφ K hK)

/-- The exact bounded-window Lipschitz constant used in the manuscript's
Arzelà–Ascoli argument. -/
theorem translated_response_window_lipschitz {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T m : ℝ} (hm : 0 ≤ m) (hTm : m ≤ T)
    (z w : CausalOffsets) (hz : z.1 ∈ Icc (-m) m ×ˢ Icc (-m) m)
    (hw : w.1 ∈ Icc (-m) m ×ˢ Icc (-m) m) :
    |d.R (T+z.1.1) (T+z.1.2)-d.R (T+w.1.1) (T+w.1.2)| ≤
      2*(multiplierCeiling p β+2*memoryCoefficient p β*m)*dist z w := by
  have hz1 := hz.1
  have hz2 := hz.2
  have hw1 := hw.1
  have hw2 := hw.2
  have hs : 0 ≤ T+z.1.2 := by linarith [hz2.1]
  have hv : 0 ≤ T+w.1.2 := by linarith [hw2.1]
  have hh := response_joint_difference_bound h hs (add_le_add le_rfl z.2)
    hv (add_le_add le_rfl w.2)
  have hrow : max (T+z.1.1) (T+w.1.1) ≤ T+m := max_le
    (by linarith [hz1.2]) (by linarith [hw1.2])
  have hearly : T-m ≤ min (T+z.1.2) (T+w.1.2) := le_min
    (by linarith [hz2.1]) (by linarith [hw2.1])
  have hlag : max (T+z.1.1) (T+w.1.1)-min (T+z.1.2) (T+w.1.2) ≤ 2*m := by linarith
  have hM := memoryCoefficient_nonnegative (β := β) h.spin_ge_three
  have hcoef : multiplierCeiling p β+memoryCoefficient p β*
      (max (T+z.1.1) (T+w.1.1)-min (T+z.1.2) (T+w.1.2)) ≤
      multiplierCeiling p β+2*memoryCoefficient p β*m := by
    have hi := mul_le_mul_of_nonneg_left hlag hM
    nlinarith only [hi]
  have hdist : |(T+z.1.1)-(T+w.1.1)|+|(T+z.1.2)-(T+w.1.2)| ≤ 2*dist z w := by
    rw [Subtype.dist_eq,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    simp only [add_sub_add_left_eq_sub]
    linarith [le_max_left |z.1.1-w.1.1| |z.1.2-w.1.2|,
      le_max_right |z.1.1-w.1.1| |z.1.2-w.1.2|]
  have hnonneg : 0 ≤ multiplierCeiling p β+2*memoryCoefficient p β*m := by
    have hL := multiplierCeiling_nonnegative p β
    positivity
  have hi := hh.trans (mul_le_mul hcoef hdist
    (add_nonneg (abs_nonneg _) (abs_nonneg _)) hnonneg)
  nlinarith only [hi]

/-- The entire statement of manuscript Proposition 4.6. -/
theorem response_compactness_proposition {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) :
    (∀ t s : ℝ, 0 ≤ s → s ≤ t →
      (0 ≤ d.R t s ∧ d.R t s ≤ d.C t s ∧ d.C t s ≤ 1) ∧
      |responseSlope p β d t s|+|backwardSlope p β d t s| ≤
        2*(multiplierCeiling p β+memoryCoefficient p β*(t-s))) ∧
    (∀ T : ℕ → ℝ, Tendsto T atTop atTop →
      ∃ c : C(ℝ × ℝ,ℝ), ∃ r : C(CausalOffsets,ℝ), ∃ ell : C(ℝ,ℝ),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ K : Set (ℝ × ℝ), IsCompact K →
        TendstoUniformlyOn (fun n z => d.C
          (T (φ n)+z.1) (T (φ n)+z.2)) c atTop K) ∧
      (∀ K : Set CausalOffsets, IsCompact K →
        TendstoUniformlyOn (fun n z => d.R
          (T (φ n)+z.1.1) (T (φ n)+z.1.2)) r atTop K) ∧
      (∀ K : Set ℝ, IsCompact K →
        TendstoUniformlyOn (fun n a => d.multiplier (T (φ n)+a)) ell atTop K)) := by
  constructor
  · intro t s hs hst
    exact ⟨BackwardResponse.response_correlation_bounds h (physical_bounds_of_equations h) hs hst,
      response_partial_derivative_bound h hs hst⟩
  · intro T hT
    exact translated_triple_precompact h hT

end SphericalAging.ResponseCompactness
