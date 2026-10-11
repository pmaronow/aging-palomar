module

public import SphericalAging.CovarianceIteration
public import SphericalAging.WeightedHilbertKernel
public import SphericalAging.WhiteCovarianceKernel

public section

/-! Positive semidefiniteness of the actual finite CK correlation, proved
from genuine Hilbert features for covariance iterates and their factorial
convergence. Neither PSD of C nor a correlation upper bound is an input. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace SphericalAging.CovariancePSD
open CKSpecification GreenCovariance CKLocalExistence FiniteGreenCovarianceClosure
open CovarianceIteration ScalarHilbertKernel WeightedHilbertKernel WhiteCovarianceKernel

@[expose] def horizonClamp (T t : ℝ) : ℝ := max 0 (min T t)

theorem horizonClamp_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : horizonClamp T t ∈ Icc 0 T :=
  ⟨le_max_left _ _,max_le hT (min_le_left _ _)⟩

theorem horizonClamp_eq {T t : ℝ} (ht : t ∈ Icc 0 T) : horizonClamp T t = t := by
  simp only [horizonClamp,min_eq_right ht.2,max_eq_right ht.1]

/-- A finite-horizon positive kernel has an actual global positive extension
by clamping its two arguments; no extension of the CK equations is asserted. -/
@[expose] def horizonKernel {T : ℝ} {H : ℝ → ℝ → ℝ} (hT : 0 ≤ T)
    (hSym : ∀ t s, H t s=H s t) (hPSD : PSDOnHorizon T H) : PositiveKernel ℝ where
  value t s := H (horizonClamp T t) (horizonClamp T s)
  symmetric _t _s := hSym _ _
  finite_positive n t a := hPSD n (fun i => horizonClamp T (t i)) a
    (fun i => horizonClamp_mem hT (t i))

theorem horizonKernel_continuous {T : ℝ} {H : ℝ → ℝ → ℝ} (hT : 0 ≤ T)
    (hSym : ∀ t s, H t s=H s t) (hPSD : PSDOnHorizon T H)
    (hH : Continuous (Function.uncurry H)) :
    Continuous (Function.uncurry (horizonKernel hT hSym hPSD).value) :=
  hH.comp ((continuous_const.max (continuous_const.min continuous_fst)).prodMk
    (continuous_const.max (continuous_const.min continuous_snd)))

theorem baseCovariance_symmetric (d : CKData) (t s : ℝ) :
    baseCovariance d t s=baseCovariance d s t := by
  unfold baseCovariance initialTerm whiteTerm
  congr 1
  · exact mul_comm _ _
  · rw [min_comm]
    congr 1
    apply intervalIntegral.integral_congr
    intro u _
    dsimp
    ring

theorem coloredCovariance_symmetric {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) {H : ℝ → ℝ → ℝ} (hH : Continuous (Function.uncurry H))
    (hSym : ∀ t s, H t s=H s t) (t s : ℝ) :
    coloredCovariance p β d H t s=coloredCovariance p β d H s t := by
  have hR := FiniteGreenCovariance.clampedResponse_continuous h
  have hf : Continuous (Function.uncurry (fun u v =>
      clampedResponse d t u*clampedResponse d s v*H u v^(p-1))) :=
    (((hR.comp (continuous_const.prodMk continuous_fst)).mul
      (hR.comp (continuous_const.prodMk continuous_snd))).mul (hH.pow _))
  unfold coloredCovariance
  rw [rectangle_integral_swap hf 0 t 0 s]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  dsimp
  apply intervalIntegral.integral_congr
  intro v _
  dsimp
  rw [hSym v u]
  ring

theorem covarianceIterate_symmetric {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (n : ℕ) :
    ∀ t s, covarianceIterate p β d n t s=covarianceIterate p β d n s t := by
  induction n with
  | zero => exact baseCovariance_symmetric d
  | succ n ih =>
    intro t s
    exact congrArg₂ (·+·) (baseCovariance_symmetric d t s)
      (coloredCovariance_symmetric h (covarianceIterate_continuous h n) ih t s)

/-- The initial and white-noise covariance is the actual Gram kernel of
R(t,0)⊕√2 R(t,·)1_(0,t] in ℝ⊕L². -/
theorem baseCovariance_psd {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) : PSDOnHorizon T (baseCovariance d) := by
  intro n times weights htimes
  have hr := FiniteGreenCovariance.clampedResponse_continuous h
  have hh := (baseKernel (clampedResponse d) hr).finite_positive n times weights
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [baseKernel_value _ hr (htimes i).1 (htimes j).1]
  rfl

/-- Covariance propagation preserves PSD through actual completed tensor
powers and weighted Bochner feature vectors. -/
theorem covarianceMap_psd {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) {H : ℝ → ℝ → ℝ}
    (hH : Continuous (Function.uncurry H)) (hSym : ∀ t s, H t s=H s t)
    (hPSD : PSDOnHorizon T H) : PSDOnHorizon T (covarianceMap p β d H) := by
  let K := horizonKernel h.horizon_pos.le hSym hPSD
  have hK : Continuous (Function.uncurry K.value) := horizonKernel_continuous _ hSym hPSD hH
  have hr := FiniteGreenCovariance.clampedResponse_continuous h
  let W := weightedKernel K (p-1) (clampedResponse d)
  have hW (t s : ℝ) (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 T) :
      W.value t s = ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s,
        clampedResponse d t u*clampedResponse d s v*H u v^(p-1) := by
    rw [weightedKernel_value K hK (p-1) (clampedResponse d) hr]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    dsimp
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hs.1] at hv
    dsimp [K,horizonKernel]
    rw [horizonClamp_eq ⟨hu.1,hu.2.trans ht.2⟩,
      horizonClamp_eq ⟨hv.1,hv.2.trans hs.2⟩]
  intro n times weights htimes
  have hbase := baseCovariance_psd h n times weights htimes
  have hcolored := W.finite_positive n times weights
  have hsum : (∑ i, ∑ j, weights i*weights j*covarianceMap p β d H (times i) (times j)) =
      (∑ i, ∑ j, weights i*weights j*baseCovariance d (times i) (times j)) +
        β^2*(p : ℝ)*(∑ i, ∑ j, weights i*weights j*W.value (times i) (times j)) := by
    have he (i j : Fin n) : weights i*weights j*covarianceMap p β d H (times i) (times j) =
        weights i*weights j*baseCovariance d (times i) (times j) +
          β^2*(p : ℝ)*(weights i*weights j*W.value (times i) (times j)) := by
      unfold covarianceMap coloredCovariance
      rw [hW _ _ (htimes i) (htimes j)]
      ring
    simp_rw [he,Finset.sum_add_distrib,← Finset.mul_sum]

  rw [hsum]
  exact add_nonneg hbase (mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) hcolored)

theorem covarianceIterate_psd {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (n : ℕ) : PSDOnHorizon T (covarianceIterate p β d n) := by
  induction n with
  | zero => exact baseCovariance_psd h
  | succ n ih =>
    exact covarianceMap_psd h (covarianceIterate_continuous h n)
      (covarianceIterate_symmetric h n) ih

/-- The actual finite CK correlation is PSD. Entrywise nonnegativity is
sufficient: PSD of C and C≤1 are both conclusions. -/
theorem correlation_psd {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (hb : NonnegativeOnHorizon T d) : PSDOnHorizon T d.C :=
  correlation_psd_of_iterates h hb (covarianceIterate_psd h)


/-- Unit diagonal and genuine Gram positivity give the correlation upper
bound. This upper bound is derived rather than assumed in the CK inputs. -/
theorem correlation_le_one {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (hb : NonnegativeOnHorizon T d) {t s : ℝ}
    (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 T) : d.C t s ≤ 1 := by
  let times : Fin 2 → ℝ := ![t,s]
  let weights : Fin 2 → ℝ := ![1,-1]
  have htimes : ∀ i, times i ∈ Icc 0 T := by
    intro i
    fin_cases i
    · exact ht
    · exact hs
  have hh := correlation_psd h hb 2 times weights htimes
  have hct := h.correlation_diagonal t ht
  have hcs := h.correlation_diagonal s hs
  have hsym := h.correlation_symmetric s t
  norm_num [Fin.sum_univ_two,times,weights,hct,hcs,hsym] at hh
  linarith

/-- All finite-horizon correlation physical bounds from entrywise signs,
the actual equations and covariance iteration; no PSD premise remains. -/
theorem finite_correlation_bounds {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) (hb : NonnegativeOnHorizon T d) {t s : ℝ}
    (ht : t ∈ Icc 0 T) (hs : s ∈ Icc 0 T) : 0 ≤ d.C t s ∧ d.C t s ≤ 1 :=
  ⟨hb.1 t ht s hs,correlation_le_one h hb ht hs⟩

end SphericalAging.CovariancePSD
