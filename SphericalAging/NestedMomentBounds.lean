module

public import SphericalAging.MultiplierLipschitz
public import SphericalAging.MultiplierMomentContraction

public section

/-! Genuine Hilbert control of the nested CK memory moment. Integrating
Green's actual Gram decomposition gives the required Loewner comparison;
there is no assumed contraction, covariance, or moment identity. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.NestedMomentBounds
open CKSpecification GreenCovariance ColoredEnergyRegularity ScalarHilbertKernel
open WeightedHilbertKernel WhiteCovarianceKernel MultiplierDerivative

/-- The physical initial/white Gram kernel, extended at zero only to make
its RKHS curve globally continuous. -/
@[expose] def physicalBaseKernel {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) : PositiveKernel ℝ where
  value u v := (baseKernel (clampedResponse d) (clampedResponse_continuous h)).value (max 0 u) (max 0 v)
  symmetric _u _v := (baseKernel (clampedResponse d) (clampedResponse_continuous h)).symmetric _ _
  finite_positive n times weights :=
    (baseKernel (clampedResponse d) (clampedResponse_continuous h)).finite_positive n
      (fun i => max 0 (times i)) weights

theorem physicalBaseKernel_value {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (u v : ℝ) : (physicalBaseKernel h).value u v=
      initialTerm d (max 0 u) (max 0 v)+whiteTerm d (max 0 u) (max 0 v) :=
  baseKernel_value _ _ (le_max_left 0 u) (le_max_left 0 v)

theorem physicalBaseKernel_continuous {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) :
    Continuous (Function.uncurry (physicalBaseKernel h).value) := by
  have hc := (initialTerm_joint_continuous h).add (whiteTerm_joint_continuous h)
  have he : Function.uncurry (physicalBaseKernel h).value=
      fun z : ℝ × ℝ => initialTerm d (max 0 z.1) (max 0 z.2)+whiteTerm d (max 0 z.1) (max 0 z.2) := by
    funext z
    exact physicalBaseKernel_value h z.1 z.2
  rw [he]
  exact hc.comp ((continuous_const.max continuous_fst).prodMk (continuous_const.max continuous_snd))

@[expose] def weightedCurve {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (w : ℝ → ℝ → ℝ) (t : ℝ) : E := ∫ u in (0 : ℝ)..t,w t u • f u

theorem weightedCurve_norm_sq {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) (hf : Continuous f) (w : ℝ → ℝ → ℝ)
    (hw : Continuous (Function.uncurry w)) (t : ℝ) :
    ‖weightedCurve f w t‖^2=∫ u in (0 : ℝ)..t,∫ v in (0 : ℝ)..t,
      w t u*w t v*inner ℝ (f u) (f v) := by
  have hi : IntervalIntegrable (fun u => w t u • f u) volume 0 t :=
    ((hw.comp (continuous_const.prodMk continuous_id)).smul hf).intervalIntegrable 0 t
  rw [←real_inner_self_eq_norm_sq,weightedCurve,intervalIntegral_inner _ hi]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [inner_intervalIntegral _ hi]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  rw [real_inner_smul_left,real_inner_smul_right]
  ring

@[expose] def memoryCurve {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) (t : ℝ) : ColoredSpace h :=
  weightedFeature (correlationKernel h) (p-1) (clampedResponse d) t

theorem memoryCurve_continuous {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) :
    Continuous (memoryCurve h) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    ((clampedResponse_continuous h).smul
      ((powerFeature_continuous (correlationKernel h) (clampedCorrelation_continuous h) (p-1)).comp
        continuous_snd)) continuous_id

@[expose] def lowerMemoryCurve {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) (t : ℝ) : ColoredSpace h :=
  weightedCurve (memoryCurve h) (lowerWeight p d) t

theorem kernel_decomposition {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (correlationKernel h).value u v=(physicalBaseKernel h).value u v+
      β^2*(p : ℝ)*inner ℝ (memoryCurve h u) (memoryCurve h v) := by
  have hg := covariance_decomposition h hu hv
  change clampedCorrelation d u v=_
  rw [clampedCorrelation_eq hu hv]
  change d.C u v=(baseKernel (clampedResponse d) (clampedResponse_continuous h)).value
    (max 0 u) (max 0 v)+β^2*(p : ℝ)*inner ℝ (memoryCurve h u) (memoryCurve h v)
  rw [max_eq_right hu,max_eq_right hv]
  rw [ColoredEnergyRegularity.coloredFeature,ColoredEnergyRegularity.coloredFeature,
    real_inner_smul_left,real_inner_smul_right] at hg
  have hc := Real.mul_self_sqrt (mul_nonneg (sq_nonneg β) (Nat.cast_nonneg p))
  rw [←mul_assoc,hc] at hg
  exact hg

theorem double_integral_add {F G : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) (hG : Continuous (Function.uncurry G)) (t : ℝ) :
    (∫ u in (0 : ℝ)..t,∫ v in (0 : ℝ)..t,F u v+G u v)=
      (∫ u in (0 : ℝ)..t,∫ v in (0 : ℝ)..t,F u v)+
      (∫ u in (0 : ℝ)..t,∫ v in (0 : ℝ)..t,G u v) := by
  have hrow (u : ℝ) : (∫ v in (0 : ℝ)..t,F u v+G u v)=
      (∫ v in (0 : ℝ)..t,F u v)+(∫ v in (0 : ℝ)..t,G u v) :=
    intervalIntegral.integral_add (f := F u) (g := G u)
      ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t)
      ((hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t)
  simp_rw [hrow]
  exact intervalIntegral.integral_add
    (f := fun u => ∫ v in (0 : ℝ)..t,F u v) (g := fun u => ∫ v in (0 : ℝ)..t,G u v)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF 0 t).intervalIntegrable 0 t)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG 0 t).intervalIntegrable 0 t)

/-- Actual Green Loewner inequality for a weighted colored-memory vector. -/
theorem lowerMemoryCurve_norm_sq_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    β^2*(p : ℝ)*‖lowerMemoryCurve h t‖^2 ≤ mixedMoment p d t := by
  let B := physicalBaseKernel h
  let baseW := weightedFeature B 1 (lowerWeight p d) t
  have hB := physicalBaseKernel_continuous h
  have hW := memoryCurve_continuous h
  have hweight := lowerWeight_continuous h
  have hF : Continuous (Function.uncurry (fun u v =>
      lowerWeight p d t u*lowerWeight p d t v*B.value u v)) :=
    (((hweight.comp (continuous_const.prodMk continuous_fst)).mul
      (hweight.comp (continuous_const.prodMk continuous_snd))).mul hB)
  have hG : Continuous (Function.uncurry (fun u v => β^2*(p : ℝ)*
      (lowerWeight p d t u*lowerWeight p d t v*inner ℝ (memoryCurve h u) (memoryCurve h v)))) :=
    continuous_const.mul (((hweight.comp (continuous_const.prodMk continuous_fst)).mul
      (hweight.comp (continuous_const.prodMk continuous_snd))).mul
        ((hW.comp continuous_fst).inner (hW.comp continuous_snd)))
  have he : mixedMoment p d t=‖baseW‖^2+β^2*(p : ℝ)*‖lowerMemoryCurve h t‖^2 := by
    rw [weightedFeature_norm_sq B hB 1 (lowerWeight p d) hweight t,
      lowerMemoryCurve,weightedCurve_norm_sq _ hW _ hweight t]
    simp only [pow_one]
    unfold mixedMoment
    calc
      _ = ∫ u in (0 : ℝ)..t,∫ v in (0 : ℝ)..t,
          lowerWeight p d t u*lowerWeight p d t v*B.value u v+
            β^2*(p : ℝ)*(lowerWeight p d t u*lowerWeight p d t v*
              inner ℝ (memoryCurve h u) (memoryCurve h v)) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le ht] at hu
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le ht] at hv
        dsimp only
        have hg := kernel_decomposition h hu.1 hv.1
        change clampedCorrelation d u v=B.value u v+
          β^2*(p : ℝ)*inner ℝ (memoryCurve h u) (memoryCurve h v) at hg
        rw [hg]
        unfold lowerWeight
        ring
      _ = _ := by
        rw [double_integral_add hF hG t]
        simp only [intervalIntegral.integral_const_mul]
  linarith only [he,sq_nonneg (‖baseW‖)]

theorem powerCurve_inner_memoryCurve {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t u : ℝ) : inner ℝ (powerCurve h t) (memoryCurve h u)=
      ∫ v in (0 : ℝ)..u,powerWeight p d t v*clampedResponse d u v := by
  unfold memoryCurve weightedFeature powerCurve
  rw [inner_intervalIntegral _ (weightedFeature_integrable (correlationKernel h)
    (clampedCorrelation_continuous h) (p-1) (clampedResponse d) (clampedResponse_continuous h) u 0 u)]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  rw [real_inner_smul_right,powerFeature_inner]
  change clampedResponse d u v*clampedCorrelation d t v^(p-1)=_
  unfold powerWeight
  ring

theorem nestedMoment_inner {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t : ℝ) :
    nestedMoment p d t=inner ℝ (powerCurve h t) (lowerMemoryCurve h t) := by
  have hi : IntervalIntegrable (fun u => lowerWeight p d t u • memoryCurve h u) volume 0 t :=
    (((lowerWeight_continuous h).comp (continuous_const.prodMk continuous_id)).smul
      (memoryCurve_continuous h)).intervalIntegrable 0 t
  unfold lowerMemoryCurve weightedCurve nestedMoment
  rw [inner_intervalIntegral _ hi]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [real_inner_smul_right,powerCurve_inner_memoryCurve]

/-- Stronger unconditional relation: q times the square of the nested
moment is at most the mixed moment. -/
theorem nestedMoment_square_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    β^2*(p : ℝ)*nestedMoment p d t^2 ≤ mixedMoment p d t := by
  have hcs := real_inner_mul_inner_self_le (powerCurve h t) (lowerMemoryCurve h t)
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,powerCurve_norm h ht,one_pow,one_mul,
    ←nestedMoment_inner h t] at hcs
  simpa only [pow_two] using
    (mul_le_mul_of_nonneg_left hcs (mul_nonneg (sq_nonneg β) (Nat.cast_nonneg p))).trans
      (lowerMemoryCurve_norm_sq_bound h ht)

theorem nestedMoment_bound_of_mixed {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t)
    (hA : β^2*(p : ℝ)*mixedMoment p d t ≤ 1) :
    β^2*(p : ℝ)*nestedMoment p d t ≤ 1 := by
  have hs := nestedMoment_square_bound h ht
  have hh := mul_le_mul_of_nonneg_left hs (mul_nonneg (sq_nonneg β) (Nat.cast_nonneg p))
  nlinarith only [hh,hA]

/-- The actual nested moment budget, with no auxiliary moment hypotheses. -/
theorem nestedMoment_budget {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    β^2*(p : ℝ)*nestedMoment p d t ≤ 1 :=
  nestedMoment_bound_of_mixed h ht (MultiplierMomentContraction.mixedMoment_budget h ht)

/-- Global multiplier Lipschitz regularity follows from the actual CK equations
and genuine Hilbert contraction estimates. -/
theorem multiplier_lipschitz {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |d.multiplier b-d.multiplier a| ≤ MultiplierLipschitz.regularityCeiling p β*|b-a| :=
  MultiplierLipschitz.multiplier_lipschitz_of_moment_bounds h
    (fun _ ht => MultiplierMomentContraction.mixedMoment_budget h ht.le)
    (fun _ ht => nestedMoment_budget h ht.le) ha hb

/-- The energy is globally Lipschitz by the exact multiplier/energy identity. -/
theorem energy_lipschitz {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |energy p β d b-energy p β d a| ≤
      (MultiplierLipschitz.regularityCeiling p β/((p : ℝ)*β))*|b-a| :=
  MultiplierLipschitz.energy_lipschitz_of_moment_bounds h
    (fun _ ht => MultiplierMomentContraction.mixedMoment_budget h ht.le)
    (fun _ ht => nestedMoment_budget h ht.le) ha hb

end SphericalAging.NestedMomentBounds
