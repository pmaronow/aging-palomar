module

public import SphericalAging.NestedMomentBounds

public section

/-! The sharp Brownian covariance modulus in Proposition 4.4, derived from
actual CK equations and Hilbert contraction rather than a stochastic premise. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.CorrelationSharpModulus
open CKSpecification GreenCovariance ColoredEnergyRegularity ScalarHilbertKernel
open WeightedHilbertKernel HilbertTensorContraction MultiplierMomentContraction
open NestedMomentBounds CKPhysicalConsequences UniformMultiplier MultiplierDerivative

/-- The actual unit covariance feature curve. -/
@[expose] def covarianceCurve {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) (t : ℝ) :
    Space (correlationKernel h) := feature (correlationKernel h) t

@[expose] def lowerCurve {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) (t : ℝ) :
    Space (correlationKernel h) := lowerFeature (correlationKernel h) (p-2) (clampedResponse d) t

@[expose] def driftCeiling (p : ℕ) (β : ℝ) := multiplierCeiling p β+(p : ℝ)*Real.sqrt (β^2*(p : ℝ))

theorem covarianceCurve_norm {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) : ‖covarianceCurve h t‖=1 := by
  have hh := feature_norm_sq (correlationKernel h) t
  change ‖covarianceCurve h t‖^2=clampedCorrelation d t t at hh
  rw [clampedCorrelation_eq ht ht,h.correlation_diagonal t ht] at hh
  nlinarith [norm_nonneg (covarianceCurve h t)]

theorem covarianceCurve_inner {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    inner ℝ (covarianceCurve h t) (covarianceCurve h s)=d.C t s := by
  rw [covarianceCurve,covarianceCurve,feature_inner]
  exact clampedCorrelation_eq ht hs

theorem covarianceCurve_increment {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    ‖covarianceCurve h t-covarianceCurve h s‖=Real.sqrt (2*(1-d.C t s)) := by
  rw [←Real.sqrt_sq (norm_nonneg (covarianceCurve h t-covarianceCurve h s)),norm_sub_sq_real,
    covarianceCurve_norm h ht,covarianceCurve_norm h hs,covarianceCurve_inner h ht hs]
  congr 1
  ring

theorem coloredCurve_increment_le {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    ‖ColoredEnergyRegularity.coloredFeature h t-ColoredEnergyRegularity.coloredFeature h s‖ ≤
      Real.sqrt (2*(1-d.C t s)) :=
  (Real.le_sqrt (norm_nonneg _) (mul_nonneg (by norm_num)
    (sub_nonneg.mpr ((physical_bounds_of_equations h).1 t s ht hs).2))).mpr
      (coloredFeature_increment_sq h ht hs)

theorem lowerCurve_budget {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    β^2*(p : ℝ)*‖lowerCurve h t‖ ≤ Real.sqrt (β^2*(p : ℝ)) := by
  have hb := mixedMoment_budget h ht
  rw [mixedMoment_eq_norm_sq h t] at hb
  change β^2*(p : ℝ)*‖lowerCurve h t‖^2 ≤ 1 at hb
  have hn := norm_nonneg (lowerCurve h t)
  have hq := mul_nonneg (sq_nonneg β) (Nat.cast_nonneg p)
  have hs := Real.sqrt_nonneg (β^2*(p : ℝ))
  have he := Real.sq_sqrt hq
  have hh : Real.sqrt (β^2*(p : ℝ))*‖lowerCurve h t‖ ≤ 1 := by nlinarith
  nlinarith

theorem lowerCurve_inner {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    inner ℝ (lowerCurve h t) (covarianceCurve h s)=
      ∫ u in (0 : ℝ)..t,d.R t u*d.C t u^(p-2)*d.C u s := by
  unfold lowerCurve covarianceCurve lowerFeature
  rw [intervalIntegral_inner _ (lowerFeature_integrable (correlationKernel h)
    (clampedCorrelation_continuous h) (p-2) (clampedResponse d) (clampedResponse_continuous h) t 0 t)]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  dsimp only
  rw [real_inner_smul_left,feature_inner]
  change clampedResponse d t u*clampedCorrelation d t u^(p-2)*clampedCorrelation d u s=_
  rw [clampedResponse_eq hu.1 hu.2,clampedCorrelation_eq ht hu.1,clampedCorrelation_eq hu.1 hs]

theorem coloredCurve_power_inner {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Real.sqrt (β^2*(p : ℝ))*inner ℝ (powerCurve h t) (ColoredEnergyRegularity.coloredFeature h s)=
      β^2*(p : ℝ)*∫ u in (0 : ℝ)..s,d.C t u^(p-1)*d.R s u := by
  rw [ColoredEnergyRegularity.coloredFeature,real_inner_smul_right]
  change _*(_*inner ℝ (powerCurve h t) (memoryCurve h s))=_
  rw [←mul_assoc,Real.mul_self_sqrt (mul_nonneg (sq_nonneg β) (Nat.cast_nonneg p)),
    powerCurve_inner_memoryCurve]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hs] at hu
  dsimp only [powerWeight]
  rw [clampedCorrelation_eq ht hu.1,clampedResponse_eq hu.1 hu.2]

/-- The actual forward correlation equation as three genuine Hilbert pairings. -/
theorem correlationSlope_hilbert {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    correlationSlope p β d t s=
      -d.multiplier t*inner ℝ (covarianceCurve h t) (covarianceCurve h s)+
      ((p : ℝ)-1)*(β^2*(p : ℝ))*inner ℝ (lowerCurve h t) (covarianceCurve h s)+
      Real.sqrt (β^2*(p : ℝ))*inner ℝ (powerCurve h t) (ColoredEnergyRegularity.coloredFeature h s) := by
  rw [covarianceCurve_inner h ht hs,lowerCurve_inner h ht hs,coloredCurve_power_inner h ht hs]
  have hfirst : β^2*∫ u in (0 : ℝ)..t,xiDoublePrime p (d.C t u)*d.R t u*d.C u s=
      ((p : ℝ)-1)*(β^2*(p : ℝ))*∫ u in (0 : ℝ)..t,d.R t u*d.C t u^(p-2)*d.C u s := by
    rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only [xiDoublePrime]
    ring
  have hsecond : β^2*∫ u in (0 : ℝ)..s,xiPrime p (d.C t u)*d.R s u=
      β^2*(p : ℝ)*∫ u in (0 : ℝ)..s,d.C t u^(p-1)*d.R s u := by
    rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only [xiPrime]
    ring
  unfold correlationSlope
  rw [hfirst,hsecond]

/-- The forward slope differs from its diagonal value -1 by a bounded
Hilbert drift times the covariance feature increment. -/
theorem correlationSlope_diagonal_difference {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    |correlationSlope p β d t s+1| ≤ driftCeiling p β*Real.sqrt (2*(1-d.C t s)) := by
  have hdiag := CKDiagonal.correlation_diagonal_slope h ht
  have hrep := correlationSlope_hilbert h ht hs
  have hrept := correlationSlope_hilbert h ht ht
  let Z := covarianceCurve h s-covarianceCurve h t
  let Y := ColoredEnergyRegularity.coloredFeature h s-ColoredEnergyRegularity.coloredFeature h t
  let g := Real.sqrt (2*(1-d.C t s))
  have he : correlationSlope p β d t s+1=
      -d.multiplier t*inner ℝ (covarianceCurve h t) Z+
      ((p : ℝ)-1)*(β^2*(p : ℝ))*inner ℝ (lowerCurve h t) Z+
      Real.sqrt (β^2*(p : ℝ))*inner ℝ (powerCurve h t) Y := by
    dsimp only [Z,Y]
    rw [inner_sub_right,inner_sub_right,inner_sub_right]
    rw [hrep] 
    linarith only [hrept,hdiag]
  have hZ : ‖Z‖=g := by
    dsimp only [Z,g]
    rw [norm_sub_rev,covarianceCurve_increment h ht hs]
  have hY : ‖Y‖ ≤ g := by
    dsimp only [Y,g]
    rw [norm_sub_rev]
    exact coloredCurve_increment_le h ht hs
  have hlam := multiplier_uniform_bound h (physical_bounds_of_equations h)
    (correlation_psd_of_equations h) ht
  have hLam0 := zero_le_one.trans hlam.1
  have hpm : 0 ≤ (p : ℝ)-1 := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by have hh := h.spin_ge_three; omega)
    linarith
  have hq := mul_nonneg (sq_nonneg β) (Nat.cast_nonneg p)
  have hsqrt := Real.sqrt_nonneg (β^2*(p : ℝ))
  have hg := Real.sqrt_nonneg (2*(1-d.C t s))
  have h1 : |-d.multiplier t*inner ℝ (covarianceCurve h t) Z| ≤ multiplierCeiling p β*g := by
    rw [abs_mul,abs_neg,abs_of_nonneg hLam0]
    have hh := abs_real_inner_le_norm (covarianceCurve h t) Z
    rw [covarianceCurve_norm h ht,hZ,one_mul] at hh
    exact mul_le_mul hlam.2 hh (abs_nonneg _) (by unfold multiplierCeiling; positivity)
  have h2 : |((p : ℝ)-1)*(β^2*(p : ℝ))*inner ℝ (lowerCurve h t) Z| ≤
      ((p : ℝ)-1)*Real.sqrt (β^2*(p : ℝ))*g := by
    rw [abs_mul,abs_of_nonneg (mul_nonneg hpm hq)]
    have hh := abs_real_inner_le_norm (lowerCurve h t) Z
    rw [hZ] at hh
    have hmul := mul_le_mul_of_nonneg_left hh (mul_nonneg hpm hq)
    have hb := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (lowerCurve_budget h ht) hg) hpm
    nlinarith only [hmul,hb]
  have h3 : |Real.sqrt (β^2*(p : ℝ))*inner ℝ (powerCurve h t) Y| ≤
      Real.sqrt (β^2*(p : ℝ))*g := by
    rw [abs_mul,abs_of_nonneg hsqrt]
    have hh := abs_real_inner_le_norm (powerCurve h t) Y
    rw [powerCurve_norm h ht,one_mul] at hh
    exact mul_le_mul_of_nonneg_left (hh.trans hY) hsqrt
  rw [he]
  have hab := abs_add_le (-d.multiplier t*inner ℝ (covarianceCurve h t) Z)
    (((p : ℝ)-1)*(β^2*(p : ℝ))*inner ℝ (lowerCurve h t) Z)
  have habc := abs_add_le
    (-d.multiplier t*inner ℝ (covarianceCurve h t) Z+
      ((p : ℝ)-1)*(β^2*(p : ℝ))*inner ℝ (lowerCurve h t) Z)
    (Real.sqrt (β^2*(p : ℝ))*inner ℝ (powerCurve h t) Y)
  dsimp only [driftCeiling,g] at h1 h2 h3 hab habc ⊢
  nlinarith only [h1,h2,h3,hab,habc]

theorem driftCeiling_nonnegative (p : ℕ) (β : ℝ) : 0 ≤ driftCeiling p β := by
  unfold driftCeiling multiplierCeiling
  positivity

/-- Elementary quadratic comparison for the maximum of the covariance deficit. -/
theorem sqrt_quadratic_majorant {m a D : ℝ} (hm : 0 ≤ m) (ha : 0 ≤ a) (hD : 0 ≤ D)
    (hh : m ≤ a+D*a*Real.sqrt (2*m)) :
    Real.sqrt (2*m) ≤ 2*D*a+Real.sqrt (2*a) := by
  let r := Real.sqrt (2*m)
  let z := Real.sqrt (2*a)
  let b := D*a
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hb : 0 ≤ b := mul_nonneg hD ha
  have hr2 : r^2=2*m := Real.sq_sqrt (mul_nonneg (by norm_num) hm)
  have hz2 : z^2=2*a := Real.sq_sqrt (mul_nonneg (by norm_num) ha)
  have hbound : r^2 ≤ z^2+2*b*r := by dsimp only [b,r] at *; nlinarith only [hh,hr2,hz2]
  rw [mul_assoc]
  change r ≤ 2*b+z
  by_contra hnot
  have hlt : 2*b+z<r := lt_of_not_ge hnot
  have hrp : 0<r := lt_of_le_of_lt (add_nonneg (mul_nonneg (by norm_num) hb) hz) hlt
  have hx : 2*b*r<(r-z)*r := mul_lt_mul_of_pos_right (by linarith) hrp
  have hy : 0 ≤ z*(r-z) := mul_nonneg hz (by linarith)
  nlinarith only [hbound,hx,hy]

/-- Compact maximum and the actual forward differential equation give a
Brownian-scale covariance feature increment with a linear drift remainder. -/
theorem covariance_increment_sharp {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Real.sqrt (2*(1-d.C t s)) ≤
      (2*driftCeiling p β)*(t-s)+Real.sqrt (2*(t-s)) := by
  let f : ℝ → ℝ := fun u => 1-d.C u s
  have hf : ContinuousOn f (Icc s t) := by
    have hc : Continuous (fun u : ℝ => clampedCorrelation d u s) :=
      (clampedCorrelation_continuous h).comp (continuous_id.prodMk continuous_const)
    apply (continuous_const.sub hc).continuousOn.congr
    intro u hu
    change 1-d.C u s=1-clampedCorrelation d u s
    rw [clampedCorrelation_eq (hs.trans hu.1) hs]
  obtain ⟨x,hx,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hst) hf
  let m := f x
  have hm : 0 ≤ m := sub_nonneg.mpr ((physical_bounds_of_equations h).1 x s (hs.trans hx.1) hs).2
  have hD := driftCeiling_nonnegative p β
  have hK : 0 ≤ 1+driftCeiling p β*Real.sqrt (2*m) := by positivity
  have hrow (u : ℝ) (hu : u ∈ Icc s t) :
      f u ≤ (1+driftCeiling p β*Real.sqrt (2*m))*(u-s) := by
    rcases lt_or_eq_of_le hu.1 with hsu | rfl
    · have hcont : ContinuousOn f (Icc s u) := hf.mono (Icc_subset_Icc le_rfl hu.2)
      have hderiv (v : ℝ) (hv : v ∈ Ioo s u) :
          HasDerivAt f (-correlationSlope p β d v s) v := by
        exact ((h.correlation_derivative v s hs hv.1.le).hasDerivAt (Ici_mem_nhds hv.1)).const_sub 1
      obtain ⟨v,hv,he⟩ := exists_hasDerivAt_eq_slope f (fun v => -correlationSlope p β d v s) hsu hcont hderiv
      have hvst : v ∈ Icc s t := ⟨hv.1.le,hv.2.le.trans hu.2⟩
      have hh := correlationSlope_diagonal_difference h (hs.trans hv.1.le) hs
      have hg := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hmax hvst) (by norm_num : (0 : ℝ) ≤ 2))
      have hbound : -correlationSlope p β d v s ≤ 1+driftCeiling p β*Real.sqrt (2*m) := by
        have hlow := (abs_le.mp hh).1
        have hmul := mul_le_mul_of_nonneg_left hg hD
        change Real.sqrt (2*(1-d.C v s)) ≤ Real.sqrt (2*m) at hg
        linarith
      rw [he] at hbound
      have hs0 : f s=0 := by dsimp only [f]; rw [h.correlation_diagonal s hs]; ring
      rw [hs0,sub_zero] at hbound
      exact (div_le_iff₀ (sub_pos.mpr hsu)).mp hbound
    · dsimp only [f]
      rw [h.correlation_diagonal s hs]
      simp
  have hmx := hrow x hx
  have hlag : x-s ≤ t-s := sub_le_sub_right hx.2 s
  have hbound : m ≤ (t-s)+driftCeiling p β*(t-s)*Real.sqrt (2*m) := by
    have hh := hmx.trans (mul_le_mul_of_nonneg_left hlag hK)
    dsimp only [m] at *
    nlinarith only [hh]
  have hmroot := sqrt_quadratic_majorant hm (sub_nonneg.mpr hst) hD hbound
  have hfinal := Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left (hmax (show t ∈ Icc s t from ⟨hst,le_rfl⟩)) (by norm_num : (0 : ℝ) ≤ 2))
  change Real.sqrt (2*(1-d.C t s)) ≤ Real.sqrt (2*m) at hfinal
  exact hfinal.trans hmroot

/-- The exact covariance coordinate modulus requested in Proposition 4.4. -/
theorem correlation_coordinate_modulus_sharp {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {u v a : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (ha : 0 ≤ a) :
    |d.C (u+a) v-d.C u v| ≤ 2*driftCeiling p β*a+Real.sqrt (2*a) := by
  have hi : inner ℝ (covarianceCurve h (u+a)-covarianceCurve h u) (covarianceCurve h v)=
      d.C (u+a) v-d.C u v := by
    rw [inner_sub_left,covarianceCurve_inner h (add_nonneg hu ha) hv,covarianceCurve_inner h hu hv]
  have hcs := abs_real_inner_le_norm (covarianceCurve h (u+a)-covarianceCurve h u) (covarianceCurve h v)
  rw [hi,covarianceCurve_norm h hv,mul_one,covarianceCurve_increment h (add_nonneg hu ha) hu] at hcs
  have hh := covariance_increment_sharp h hu (show u ≤ u+a by linarith)
  rw [add_sub_cancel_left] at hh
  exact hcs.trans hh

theorem correlation_coordinate_modulus_sharp_right {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {u v a : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (ha : 0 ≤ a) :
    |d.C u (v+a)-d.C u v| ≤ 2*driftCeiling p β*a+Real.sqrt (2*a) := by
  rw [h.correlation_symmetric u (v+a) hu (add_nonneg hv ha),h.correlation_symmetric u v hu hv]
  exact correlation_coordinate_modulus_sharp h hv hu ha

/-- A common finite Lipschitz constant for both multiplier and energy. -/
@[expose] def commonLipschitzCeiling (p : ℕ) (β : ℝ) :=
  max (MultiplierLipschitz.regularityCeiling p β)
    (MultiplierLipschitz.regularityCeiling p β/((p : ℝ)*β))

/-- Full Proposition 4.4 from actual CK equations, with a common finite
Lipschitz constant, both sharp covariance moduli, and the diagonal increment. -/
theorem global_regularity_proposition {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) :
    (∀ a b : ℝ,0 ≤ a → 0 ≤ b →
      |d.multiplier b-d.multiplier a| ≤ commonLipschitzCeiling p β*|b-a|) ∧
    (∀ a b : ℝ,0 ≤ a → 0 ≤ b →
      |energy p β d b-energy p β d a| ≤ commonLipschitzCeiling p β*|b-a|) ∧
    (∀ u v a : ℝ,0 ≤ u → 0 ≤ v → 0 ≤ a →
      |d.C (u+a) v-d.C u v| ≤ 2*driftCeiling p β*a+Real.sqrt (2*a) ∧
      |d.C u (v+a)-d.C u v| ≤ 2*driftCeiling p β*a+Real.sqrt (2*a)) ∧
    (∀ t s : ℝ,0 ≤ s → s ≤ t →
      0 ≤ 1-d.C t s ∧ 1-d.C t s ≤ multiplierCeiling p β*(t-s)) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro a b ha hb
    exact (multiplier_lipschitz h ha hb).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  · intro a b ha hb
    exact (energy_lipschitz h ha hb).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
  · intro u v a hu hv ha
    exact ⟨correlation_coordinate_modulus_sharp h hu hv ha,
      correlation_coordinate_modulus_sharp_right h hu hv ha⟩
  · intro t s hs hst
    exact CKDiagonalRegularity.diagonal_increment h hs hst

end SphericalAging.CorrelationSharpModulus
