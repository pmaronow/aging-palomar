module

public import SphericalAging.FiniteGreenCovarianceClosure
public import SphericalAging.ScalarHilbertKernel
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Algebra.Order.Floor

public section

/-! Genuine covariance Picard iterates below a finite-horizon CK correlation.
They start from the initial and white-noise covariance and converge to the
actual CK correlation. PSD propagation is kept separate from entrywise order. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalAging.CovarianceIteration
open CKSpecification GreenCovariance CKLocalExistence FiniteGreenCovarianceClosure

@[expose] def PSDOnHorizon (T : ℝ) (H : ℝ → ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (times weights : Fin n → ℝ), (∀ i, times i ∈ Icc 0 T) →
    0 ≤ ∑ i, ∑ j, weights i*weights j*H (times i) (times j)

@[expose] def baseCovariance (d : CKData) (t s : ℝ) : ℝ := initialTerm d t s + whiteTerm d t s

@[expose] def coloredCovariance (p : ℕ) (β : ℝ) (d : CKData) (H : ℝ → ℝ → ℝ) (t s : ℝ) : ℝ :=
  β^2*(p : ℝ)*∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s,
    clampedResponse d t u * clampedResponse d s v * H u v^(p-1)

@[expose] def covarianceMap (p : ℕ) (β : ℝ) (d : CKData) (H : ℝ → ℝ → ℝ) (t s : ℝ) : ℝ :=
  baseCovariance d t s + coloredCovariance p β d H t s

@[expose] def covarianceIterate (p : ℕ) (β : ℝ) (d : CKData) : ℕ → ℝ → ℝ → ℝ
  | 0 => baseCovariance d
  | n+1 => covarianceMap p β d (covarianceIterate p β d n)

theorem baseCovariance_continuous {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) : Continuous (Function.uncurry (baseCovariance d)) :=
  (FiniteGreenCovariance.initialTerm_joint_continuous h).add
    (FiniteGreenCovariance.whiteTerm_joint_continuous h)

theorem coloredCovariance_continuous {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) {H : ℝ → ℝ → ℝ} (hH : Continuous (Function.uncurry H)) :
    Continuous (Function.uncurry (coloredCovariance p β d H)) := by
  have hR := FiniteGreenCovariance.clampedResponse_continuous h
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · exact (((hR.comp (continuous_fst.fst.fst.prodMk continuous_fst.snd)).mul
        (hR.comp (continuous_fst.fst.snd.prodMk continuous_snd))).mul
        ((hH.comp (continuous_fst.snd.prodMk continuous_snd)).pow _))
    · exact continuous_fst.snd
  · exact continuous_fst

theorem covarianceMap_continuous {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) {H : ℝ → ℝ → ℝ} (hH : Continuous (Function.uncurry H)) :
    Continuous (Function.uncurry (covarianceMap p β d H)) :=
  (baseCovariance_continuous h).add (coloredCovariance_continuous h hH)

theorem covarianceIterate_continuous {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (n : ℕ) :
    Continuous (Function.uncurry (covarianceIterate p β d n)) := by
  induction n with
  | zero => exact baseCovariance_continuous h
  | succ n ih => exact covarianceMap_continuous h ih

/-- Compact rectangular integral monotonicity, deriving all integrability
requirements from actual continuity. -/
theorem rectangle_integral_mono {F G : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) (hG : Continuous (Function.uncurry G))
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hle : ∀ u ∈ Icc 0 t, ∀ v ∈ Icc 0 s, F u v ≤ G u v) :
    (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, F u v) ≤
      ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, G u v := by
  have hFi : Continuous (fun u => ∫ v in (0 : ℝ)..s, F u v) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF 0 s
  have hGi : Continuous (fun u => ∫ v in (0 : ℝ)..s, G u v) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG 0 s
  apply intervalIntegral.integral_mono_on ht (hFi.intervalIntegrable 0 t) (hGi.intervalIntegrable 0 t)
  intro u hu
  exact intervalIntegral.integral_mono_on hs
    ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 s)
    ((hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 s) (hle u hu)

theorem baseCovariance_nonnegative {d : CKData} {T t s : ℝ}
    (hb : NonnegativeOnHorizon T d) (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 T) :
    0 ≤ baseCovariance d t s := by
  unfold baseCovariance initialTerm whiteTerm
  rw [clampedResponse_eq (le_refl 0) ht.1,clampedResponse_eq (le_refl 0) hs.1]
  apply add_nonneg
  · exact mul_nonneg (hb.2 t ht 0 ⟨le_refl 0,ht.1⟩) (hb.2 s hs 0 ⟨le_refl 0,hs.1⟩)
  · apply mul_nonneg (by norm_num)
    apply intervalIntegral.integral_nonneg (le_min ht.1 hs.1)
    intro u hu
    rw [clampedResponse_eq hu.1 (hu.2.trans (min_le_left _ _)),
      clampedResponse_eq hu.1 (hu.2.trans (min_le_right _ _))]
    exact mul_nonneg (hb.2 t ht u ⟨hu.1,hu.2.trans (min_le_left _ _)⟩)
      (hb.2 s hs u ⟨hu.1,hu.2.trans (min_le_right _ _)⟩)

theorem coloredCovariance_nonnegative {p : ℕ} {β T : ℝ} {d : CKData}
    {H : ℝ → ℝ → ℝ} (hb : NonnegativeOnHorizon T d)
    (hH : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, 0 ≤ H t s)
    {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 T) :
    0 ≤ coloredCovariance p β d H t s := by
  unfold coloredCovariance
  apply mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  apply intervalIntegral.integral_nonneg ht.1
  intro u hu
  apply intervalIntegral.integral_nonneg hs.1
  intro v hv
  rw [clampedResponse_eq hu.1 hu.2,clampedResponse_eq hv.1 hv.2]
  exact mul_nonneg (mul_nonneg (hb.2 t ht u hu) (hb.2 s hs v hv))
    (pow_nonneg (hH u ⟨hu.1,hu.2.trans ht.2⟩ v ⟨hv.1,hv.2.trans hs.2⟩) _)

/-- Covariance monotonicity on the actual finite horizon. -/
theorem covarianceMap_mono {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (hb : NonnegativeOnHorizon T d)
    {H J : ℝ → ℝ → ℝ} (hH : Continuous (Function.uncurry H))
    (hJ : Continuous (Function.uncurry J))
    (hH0 : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, 0 ≤ H t s)
    (hHJ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, H t s ≤ J t s)
    {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 T) :
    covarianceMap p β d H t s ≤ covarianceMap p β d J t s := by
  have hR := FiniteGreenCovariance.clampedResponse_continuous h
  unfold covarianceMap coloredCovariance
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  apply rectangle_integral_mono
    ((((hR.comp (continuous_const.prodMk continuous_fst)).mul
      (hR.comp (continuous_const.prodMk continuous_snd))).mul (hH.pow _)))
    ((((hR.comp (continuous_const.prodMk continuous_fst)).mul
      (hR.comp (continuous_const.prodMk continuous_snd))).mul (hJ.pow _))) ht.1 hs.1
  intro u hu v hv
  have huT : u ∈ Icc 0 T := ⟨hu.1,hu.2.trans ht.2⟩
  have hvT : v ∈ Icc 0 T := ⟨hv.1,hv.2.trans hs.2⟩
  rw [clampedResponse_eq hu.1 hu.2,clampedResponse_eq hv.1 hv.2]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (hH0 u huT v hvT) (hHJ u huT v hvT) _)
    (mul_nonneg (hb.2 t ht u hu) (hb.2 s hs v hv))

/-- The actual finite CK correlation is a fixed point of the explicit
covariance map, by the proved Green identity. -/
theorem correlation_covariance_fixed {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 T) :
    covarianceMap p β d d.C t s = d.C t s := by
  rw [green_covariance_identity h ht hs]
  unfold covarianceMap coloredCovariance baseCovariance initialTerm whiteTerm greenCovariance
  rw [clampedResponse_eq (le_refl 0) ht.1,clampedResponse_eq (le_refl 0) hs.1]
  congr 1
  · congr 1
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (le_min ht.1 hs.1)] at hu
    dsimp
    rw [clampedResponse_eq hu.1 (hu.2.trans (min_le_left _ _)),
      clampedResponse_eq hu.1 (hu.2.trans (min_le_right _ _))]
  · congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    dsimp
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hs.1] at hv
    dsimp
    rw [clampedResponse_eq hu.1 hu.2,clampedResponse_eq hv.1 hv.2]

/-- Every covariance iterate is nonnegative and lies below the actual CK
correlation. The correlation upper bound one and PSD are not assumptions. -/
theorem covarianceIterate_bounds {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (hb : NonnegativeOnHorizon T d) (n : ℕ) :
    ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T,
      0 ≤ covarianceIterate p β d n t s ∧ covarianceIterate p β d n t s ≤ d.C t s := by
  induction n with
  | zero =>
    intro t ht s hs
    have hcol := coloredCovariance_nonnegative (p := p) (β := β) hb hb.1 ht hs
    have hfixed := correlation_covariance_fixed h ht hs
    constructor
    · exact baseCovariance_nonnegative hb ht hs
    · change baseCovariance d t s ≤ d.C t s
      unfold covarianceMap at hfixed
      linarith
  | succ n ih =>
    intro t ht s hs
    constructor
    · exact add_nonneg (baseCovariance_nonnegative hb ht hs)
        (coloredCovariance_nonnegative hb (fun _ ht _ hs => (ih _ ht _ hs).1) ht hs)
    · change covarianceMap p β d (covarianceIterate p β d n) t s ≤ d.C t s
      rw [← correlation_covariance_fixed h ht hs]
      exact covarianceMap_mono h hb (covarianceIterate_continuous h n) h.correlation_continuous
        (fun _ ht _ hs => (ih _ ht _ hs).1) (fun _ ht _ hs => (ih _ ht _ hs).2) ht hs


@[expose] def iterationError (p : ℕ) (β : ℝ) (d : CKData) (n : ℕ) (t s : ℝ) : ℝ :=
  d.C t s-covarianceIterate p β d n t s

theorem iterationError_continuous {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (n : ℕ) :
    Continuous (Function.uncurry (iterationError p β d n)) :=
  h.correlation_continuous.sub (covarianceIterate_continuous h n)

theorem power_difference_bound {x y M : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x)
    (hxM : x ≤ M) (k : ℕ) :
    x^k-y^k ≤ (k : ℝ)*M^(k-1)*(x-y) := by
  have hx : 0 ≤ x := hy.trans hyx
  have hh := abs_pow_sub_pow_le (a := x) (b := y) (n := k)
  rw [abs_of_nonneg hx,abs_of_nonneg hy,max_eq_left hyx,
    abs_of_nonneg (sub_nonneg.mpr hyx)] at hh
  have hp := pow_le_pow_left₀ hx hxM (k-1)
  calc
    x^k-y^k ≤ |x^k-y^k| := le_abs_self _
    _ ≤ (x-y)*(k : ℝ)*x^(k-1) := hh
    _ ≤ (x-y)*(k : ℝ)*M^(k-1) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (sub_nonneg.mpr hyx) (Nat.cast_nonneg _))
    _ = _ := by ring

theorem rectangle_integral_sub {F G : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) (hG : Continuous (Function.uncurry G)) (t s : ℝ) :
    (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, F u v-G u v) =
      (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, F u v) -
        ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, G u v := by
  have hi (u : ℝ) : (∫ v in (0 : ℝ)..s, F u v-G u v) =
      (∫ v in (0 : ℝ)..s, F u v)-(∫ v in (0 : ℝ)..s, G u v) :=
    intervalIntegral.integral_sub (f := F u) (g := G u)
      ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 s)
      ((hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 s)
  simp_rw [hi]
  have hFi : Continuous (fun u => ∫ v in (0 : ℝ)..s, F u v) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF 0 s
  have hGi : Continuous (fun u => ∫ v in (0 : ℝ)..s, G u v) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG 0 s
  exact intervalIntegral.integral_sub
    (f := fun u => ∫ v in (0 : ℝ)..s, F u v)
    (g := fun u => ∫ v in (0 : ℝ)..s, G u v)
    (hFi.intervalIntegrable 0 t) (hGi.intervalIntegrable 0 t)

theorem iterationError_succ_eq {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (n : ℕ) {t s : ℝ}
    (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 T) :
    iterationError p β d (n+1) t s =
      β^2*(p : ℝ)*∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s,
        clampedResponse d t u*clampedResponse d s v*
          (d.C u v^(p-1)-covarianceIterate p β d n u v^(p-1)) := by
  have hR := FiniteGreenCovariance.clampedResponse_continuous h
  have hRR : Continuous (fun z : ℝ × ℝ => clampedResponse d t z.1*clampedResponse d s z.2) :=
    (hR.comp (continuous_const.prodMk continuous_fst)).mul
      (hR.comp (continuous_const.prodMk continuous_snd))
  have hh := rectangle_integral_sub
    (F := fun u v => clampedResponse d t u*clampedResponse d s v*d.C u v^(p-1))
    (G := fun u v => clampedResponse d t u*clampedResponse d s v*covarianceIterate p β d n u v^(p-1))
    (hRR.mul (h.correlation_continuous.pow (p-1)))
    (hRR.mul ((covarianceIterate_continuous h n).pow (p-1))) t s
  rw [iterationError,← correlation_covariance_fixed h ht hs]
  change covarianceMap p β d d.C t s-
    covarianceMap p β d (covarianceIterate p β d n) t s=_
  unfold covarianceMap coloredCovariance
  simp only [mul_sub]
  rw [hh]
  ring

@[expose] def iterationCoefficient (p : ℕ) (β M L : ℝ) : ℝ :=
  β^2*(p : ℝ)*L^2*((p-1 : ℕ) : ℝ)*M^(p-2)

theorem iterationCoefficient_nonnegative (p : ℕ) (β M L : ℝ) (hM : 0 ≤ M) :
    0 ≤ iterationCoefficient p β M L := by
  unfold iterationCoefficient
  positivity

/-- The actual error recurrence, with constants supplied only by compact
bounds on the actual CK functions. -/
theorem iterationError_step_bound {p : ℕ} {β T M L : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (hb : NonnegativeOnHorizon T d)
    (hL : 0 ≤ L)
    (hC : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, d.C t s ≤ M)
    (hR : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t, d.R t s ≤ L)
    (n : ℕ) {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 T) :
    iterationError p β d (n+1) t s ≤ iterationCoefficient p β M L *
      ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, iterationError p β d n u v := by
  have hcR := FiniteGreenCovariance.clampedResponse_continuous h
  have hRR : Continuous (fun z : ℝ × ℝ => clampedResponse d t z.1*clampedResponse d s z.2) :=
    (hcR.comp (continuous_const.prodMk continuous_fst)).mul
      (hcR.comp (continuous_const.prodMk continuous_snd))
  have hErr := iterationError_continuous h n
  have hpow : Continuous (fun z : ℝ × ℝ => d.C z.1 z.2^(p-1)-
      covarianceIterate p β d n z.1 z.2^(p-1)) :=
    (h.correlation_continuous.pow _).sub ((covarianceIterate_continuous h n).pow _)
  have hexp : (p-1)-1=p-2 := by omega
  have hLip : 0 ≤ ((p-1 : ℕ) : ℝ)*M^(p-2) := by
    have hM : 0 ≤ M := (hb.1 0 ⟨le_refl 0,h.horizon_pos.le⟩ 0 ⟨le_refl 0,h.horizon_pos.le⟩).trans
      (hC 0 ⟨le_refl 0,h.horizon_pos.le⟩ 0 ⟨le_refl 0,h.horizon_pos.le⟩)
    positivity
  rw [iterationError_succ_eq h n ht hs]
  have hm := rectangle_integral_mono
    (F := fun u v => clampedResponse d t u*clampedResponse d s v*
      (d.C u v^(p-1)-covarianceIterate p β d n u v^(p-1)))
    (G := fun u v => L^2*(((p-1 : ℕ) : ℝ)*M^(p-2)*iterationError p β d n u v))
    (hRR.mul hpow)
    ((hErr.const_mul (((p-1 : ℕ) : ℝ)*M^(p-2))).const_mul (L^2)) ht.1 hs.1
    (fun u hu v hv => by
      have huT : u ∈ Icc 0 T := ⟨hu.1,hu.2.trans ht.2⟩
      have hvT : v ∈ Icc 0 T := ⟨hv.1,hv.2.trans hs.2⟩
      have hbnd := covarianceIterate_bounds h hb n u huT v hvT
      have hp := power_difference_bound hbnd.1 hbnd.2 (hC u huT v hvT) (p-1)
      rw [hexp] at hp
      have hp0 := sub_nonneg.mpr (pow_le_pow_left₀ hbnd.1 hbnd.2 (p-1))
      have hRRb : clampedResponse d t u*clampedResponse d s v ≤ L^2 := by
        rw [clampedResponse_eq hu.1 hu.2,clampedResponse_eq hv.1 hv.2,pow_two]
        exact mul_le_mul (hR t ht u hu) (hR s hs v hv) (hb.2 s hs v hv) hL
      change clampedResponse d t u*clampedResponse d s v*
        (d.C u v^(p-1)-covarianceIterate p β d n u v^(p-1)) ≤
          L^2*(((p-1 : ℕ) : ℝ)*M^(p-2)*iterationError p β d n u v)
      exact mul_le_mul hRRb hp hp0 (sq_nonneg L))
  calc
    β^2*(p : ℝ)*(∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s,
        clampedResponse d t u*clampedResponse d s v*
          (d.C u v^(p-1)-covarianceIterate p β d n u v^(p-1))) ≤
      β^2*(p : ℝ)*(∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s,
        L^2*(((p-1 : ℕ) : ℝ)*M^(p-2)*iterationError p β d n u v)) :=
        mul_le_mul_of_nonneg_left hm (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    _ = _ := by
      simp only [intervalIntegral.integral_const_mul]
      unfold iterationCoefficient
      ring


/-- Rectangular Volterra iterates have two factorial denominators. -/
@[expose] def boxMonomial (n : ℕ) (t s : ℝ) : ℝ := t^n*s^n/(n.factorial : ℝ)^2

theorem boxMonomial_continuous (n : ℕ) : Continuous (Function.uncurry (boxMonomial n)) :=
  ((continuous_fst.pow n).mul (continuous_snd.pow n)).div_const _

theorem boxMonomial_nonnegative (n : ℕ) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    0 ≤ boxMonomial n t s :=
  div_nonneg (mul_nonneg (pow_nonneg ht _) (pow_nonneg hs _)) (sq_nonneg _)

theorem boxMonomial_integral (n : ℕ) (t s : ℝ) :
    (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, boxMonomial n u v) = boxMonomial (n+1) t s := by
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  have hfact : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp_rw [boxMonomial,intervalIntegral.integral_div,intervalIntegral.integral_const_mul,
    integral_pow,zero_pow (show n+1 ≠ 0 by omega),sub_zero]
  rw [intervalIntegral.integral_mul_const,integral_pow]
  simp only [zero_pow (show n+1 ≠ 0 by omega),sub_zero,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  field_simp

/-- The complete factorial error estimate is derived by integrating the
actual covariance error recurrence, not assumed as a Picard hypothesis. -/
theorem iterationError_factorial_bound {p : ℕ} {β T M L : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (hb : NonnegativeOnHorizon T d)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hC : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, d.C t s ≤ M)
    (hR : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t, d.R t s ≤ L)
    (n : ℕ) : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T,
    iterationError p β d n t s ≤ M*(iterationCoefficient p β M L)^n*boxMonomial n t s := by
  let B := iterationCoefficient p β M L
  have hB : 0 ≤ B := iterationCoefficient_nonnegative p β M L hM
  induction n with
  | zero =>
    intro t ht s hs
    change d.C t s-baseCovariance d t s ≤ M*B^0*boxMonomial 0 t s
    simp only [boxMonomial,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one]
    linarith only [hC t ht s hs,baseCovariance_nonnegative hb ht hs]
  | succ n ih =>
    intro t ht s hs
    have hm := rectangle_integral_mono (F := iterationError p β d n)
      (G := fun u v => M*B^n*boxMonomial n u v) (iterationError_continuous h n)
      ((boxMonomial_continuous n).const_mul (M*B^n)) ht.1 hs.1
      (fun u hu v hv => ih u ⟨hu.1,hu.2.trans ht.2⟩ v ⟨hv.1,hv.2.trans hs.2⟩)
    calc
      iterationError p β d (n+1) t s ≤
          B*(∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, iterationError p β d n u v) :=
        iterationError_step_bound h hb hL hC hR n ht hs
      _ ≤ B*(∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s, M*B^n*boxMonomial n u v) :=
        mul_le_mul_of_nonneg_left hm hB
      _ = M*B^(n+1)*boxMonomial (n+1) t s := by
        simp only [intervalIntegral.integral_const_mul,boxMonomial_integral]
        rw [pow_succ]
        ring


/-- A single-factorial majorant suffices for uniform convergence. -/
theorem iterationError_uniform_majorant {p : ℕ} {β T M L : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (hb : NonnegativeOnHorizon T d)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hC : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, d.C t s ≤ M)
    (hR : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t, d.R t s ≤ L)
    (n : ℕ) {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 T) :
    0 ≤ iterationError p β d n t s ∧
      iterationError p β d n t s ≤
        M*(iterationCoefficient p β M L*T*T)^n/(n.factorial : ℝ) := by
  let B := iterationCoefficient p β M L
  have hB : 0 ≤ B := iterationCoefficient_nonnegative p β M L hM
  have hfact : (1 : ℝ) ≤ (n.factorial : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos n))
  have hfpos : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  constructor
  · exact sub_nonneg.mpr (covarianceIterate_bounds h hb n t ht s hs).2
  · calc
      iterationError p β d n t s ≤ M*B^n*boxMonomial n t s :=
        iterationError_factorial_bound h hb hM hL hC hR n t ht s hs
      _ ≤ M*B^n*boxMonomial n T T := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hM (pow_nonneg hB _))
        unfold boxMonomial
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul (pow_le_pow_left₀ ht.1 ht.2 n) (pow_le_pow_left₀ hs.1 hs.2 n)
          (pow_nonneg hs.1 _) (pow_nonneg h.horizon_pos.le _)
      _ = M*(B*T*T)^n/(n.factorial : ℝ)^2 := by
        unfold boxMonomial
        simp only [mul_pow]
        ring
      _ ≤ M*(B*T*T)^n/(n.factorial : ℝ) := by
        apply div_le_div_of_nonneg_left (mul_nonneg hM (pow_nonneg
          (mul_nonneg (mul_nonneg hB h.horizon_pos.le) h.horizon_pos.le) _)) hfpos
        nlinarith only [hfact]

/-- All covariance iterates converge uniformly to the actual CK correlation
on its finite horizon. Compactness supplies the bounds; no iteration-error,
PSD, or correlation-upper-bound assertion is assumed. -/
theorem covarianceIterate_tendstoUniformlyOn {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (hb : NonnegativeOnHorizon T d) :
    TendstoUniformlyOn (fun n => Function.uncurry (covarianceIterate p β d n))
      (Function.uncurry d.C) atTop (Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) T) := by
  obtain ⟨M₀,hM₀⟩ :=
    (show IsCompact (Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) T) from
      isCompact_Icc.prod isCompact_Icc).bddAbove_image h.correlation_continuous.norm.continuousOn
  obtain ⟨L₀,hL₀⟩ :=
    (show IsCompact (Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) T) from
      isCompact_Icc.prod isCompact_Icc).bddAbove_image h.response_continuous.norm.continuousOn
  let M := max 0 M₀
  let L := max 0 L₀
  have hM : 0 ≤ M := le_max_left _ _
  have hL : 0 ≤ L := le_max_left _ _
  have hCbound (t : ℝ) (ht : t ∈ Icc 0 T) (s : ℝ) (hs : s ∈ Icc 0 T) : d.C t s ≤ M := by
    have hh := hM₀ ⟨(t,s),⟨ht,hs⟩,rfl⟩
    exact (le_abs_self _).trans ((show |d.C t s| ≤ M₀ by
      simpa only [Function.uncurry_apply_pair,Real.norm_eq_abs] using hh).trans (le_max_right _ _))
  have hRbound (t : ℝ) (ht : t ∈ Icc 0 T) (s : ℝ) (hs : s ∈ Icc 0 t) : d.R t s ≤ L := by
    have hh := hL₀ ⟨(t,s),⟨ht,⟨hs.1,hs.2.trans ht.2⟩⟩,rfl⟩
    exact (le_abs_self _).trans ((show |d.R t s| ≤ L₀ by
      simpa only [Function.uncurry_apply_pair,Real.norm_eq_abs] using hh).trans (le_max_right _ _))
  have hlim : Tendsto (fun n => M*(iterationCoefficient p β M L*T*T)^n/(n.factorial : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero,mul_div_assoc] using
      (FloorSemiring.tendsto_pow_div_factorial_atTop (iterationCoefficient p β M L*T*T)).const_mul M
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn z hz
  have hh := iterationError_uniform_majorant h hb hM hL hCbound hRbound n hz.1 hz.2
  rw [Real.dist_eq]
  change |iterationError p β d n z.1 z.2| < ε
  rw [abs_of_nonneg hh.1]
  exact hh.2.trans_lt hn

/-- Finite Gram positivity passes to the actual correlation limit. The only
PSD input is positivity of the concrete finite-height covariance iterates;
positivity of the limiting CK correlation is the conclusion. -/
theorem correlation_psd_of_iterates {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (hb : NonnegativeOnHorizon T d)
    (hPSD : ∀ n, PSDOnHorizon T (covarianceIterate p β d n)) : PSDOnHorizon T d.C := by
  intro k times weights htimes
  have hc := covarianceIterate_tendstoUniformlyOn h hb
  have hpoint (i j : Fin k) : Tendsto (fun n => covarianceIterate p β d n (times i) (times j))
      atTop (𝓝 (d.C (times i) (times j))) :=
    hc.tendsto_at (show (times i,times j) ∈ Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) T from
      ⟨htimes i,htimes j⟩)
  have hq : Tendsto (fun n => ∑ i, ∑ j, weights i*weights j*
      covarianceIterate p β d n (times i) (times j)) atTop
      (𝓝 (∑ i, ∑ j, weights i*weights j*d.C (times i) (times j))) := by
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact (hpoint i j).const_mul _
  exact ge_of_tendsto' hq (fun n => hPSD n k times weights htimes)


theorem covarianceIterate_step_mono {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (hb : NonnegativeOnHorizon T d) (n : ℕ) :
    ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T,
      covarianceIterate p β d n t s ≤ covarianceIterate p β d (n+1) t s := by
  induction n with
  | zero =>
    intro t ht s hs
    have hh := coloredCovariance_nonnegative (p := p) (β := β) hb
      (fun t ht s hs => baseCovariance_nonnegative hb ht hs) ht hs
    change baseCovariance d t s ≤ baseCovariance d t s+
      coloredCovariance p β d (baseCovariance d) t s
    linarith
  | succ n ih =>
    intro t ht s hs
    exact covarianceMap_mono h hb (covarianceIterate_continuous h n)
      (covarianceIterate_continuous h (n+1))
      (fun _ ht _ hs => (covarianceIterate_bounds h hb n _ ht _ hs).1) ih ht hs

theorem covarianceIterate_tendsto {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (hb : NonnegativeOnHorizon T d) {t s : ℝ}
    (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 T) :
    Tendsto (fun n => covarianceIterate p β d n t s) atTop (𝓝 (d.C t s)) :=
  (covarianceIterate_tendstoUniformlyOn h hb).tendsto_at
    (show (t,s) ∈ Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) T from ⟨ht,hs⟩)

end SphericalAging.CovarianceIteration
