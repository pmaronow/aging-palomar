module

public import SphericalAging.TreeLeafTensor
public import SphericalAging.ScalarHilbertKernel
public import SphericalAging.WeightedHilbertKernel

public section

/-! Actual bounded partial inner products on completed Hilbert tensors. -/
noncomputable section
open UniformSpace MeasureTheory
open scoped InnerProductSpace TensorProduct
namespace SphericalAging.HilbertTensorContraction
open CausalTree CausalTree.HilbertDatum

@[expose] def contractLeftAlg (A B : HilbertDatum) (z : A.Carrier) :
    (A.Carrier ⊗[ℝ] B.Carrier) →L[ℝ] B.Carrier :=
  (TensorProduct.lidIsometry ℝ B.Carrier).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (TensorProduct.mapL (innerSL ℝ z) (ContinuousLinearMap.id ℝ B.Carrier))

theorem contractLeftAlg_norm_le (A B : HilbertDatum) (z : A.Carrier)
    (u : A.Carrier ⊗[ℝ] B.Carrier) :
    ‖contractLeftAlg A B z u‖ ≤ ‖z‖ * ‖u‖ := by
  change ‖TensorProduct.lidIsometry ℝ B.Carrier
    (TensorProduct.mapL (innerSL ℝ z) (ContinuousLinearMap.id ℝ B.Carrier) u)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  apply le_trans (ContinuousLinearMap.le_opNorm _ u)
  have h := TensorProduct.norm_mapL_le (innerSL ℝ z) (ContinuousLinearMap.id ℝ B.Carrier)
  rw [innerSL_apply_norm] at h
  exact mul_le_mul_of_nonneg_right
    (le_trans h (by simpa using (mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := B.Carrier)) (norm_nonneg z))))
    (norm_nonneg u)

@[expose] def contractLeft (A B : HilbertDatum) (z : A.Carrier) :
    (tensor A B).Carrier →L[ℝ] B.Carrier := (contractLeftAlg A B z).fromCompletion

@[simp] theorem contractLeft_coe (A B : HilbertDatum) (z : A.Carrier)
    (u : A.Carrier ⊗[ℝ] B.Carrier) :
    contractLeft A B z (u : Completion _) = contractLeftAlg A B z u :=
  ContinuousLinearMap.fromCompletion_apply_coe _ _

@[simp] theorem contractLeft_pure (A B : HilbertDatum) (z x : A.Carrier)
    (y : B.Carrier) :
    contractLeft A B z (pure A B x y) = inner ℝ z x • y := by
  rw [CausalTree.HilbertDatum.pure, contractLeft_coe]
  simp [contractLeftAlg, TensorProduct.mapL_tmul]

theorem contractLeft_norm_le (A B : HilbertDatum) (z : A.Carrier)
    (u : (tensor A B).Carrier) : ‖contractLeft A B z u‖ ≤ ‖z‖ * ‖u‖ := by
  refine Completion.induction_on u
    (isClosed_le ((contractLeft A B z).continuous.norm) (continuous_const.mul continuous_norm)) ?_
  intro x
  rw [contractLeft_coe, Completion.norm_coe]
  exact contractLeftAlg_norm_le A B z x

/-- Contract the first `n` factors of an `(n+1)`-fold ordered tensor. -/
@[expose] def partialPower (A : HilbertDatum) : (n : ℕ) → A.Carrier →
    (finiteTensor (n + 1) (fun _ => A)).Carrier →L[ℝ] A.Carrier
  | 0, _ => (tensorRid A).toContinuousLinearEquiv.toContinuousLinearMap
  | n + 1, z => (partialPower A n z).comp
      (contractLeft A (finiteTensor (n + 1) (fun _ => A)) z)

theorem partialPower_norm_le (A : HilbertDatum) (n : ℕ) (z : A.Carrier)
    (u : (finiteTensor (n + 1) (fun _ => A)).Carrier) :
    ‖partialPower A n z u‖ ≤ ‖z‖ ^ n * ‖u‖ := by
  induction n with
  | zero => simpa [partialPower] using (tensorRid A).norm_map u |>.le
  | succ n ih =>
    change ‖partialPower A n z (contractLeft A (finiteTensor (n + 1) (fun _ => A)) z u)‖ ≤ _
    apply le_trans (ih _)
    have h := mul_le_mul_of_nonneg_left
      (contractLeft_norm_le A (finiteTensor (n + 1) (fun _ => A)) z u)
      (pow_nonneg (norm_nonneg z) n)
    simpa only [pow_succ, mul_assoc] using h

@[simp] theorem partialPower_pure (A : HilbertDatum) (n : ℕ) (z x : A.Carrier) :
    partialPower A n z (finitePure (n + 1) (fun _ => A) (fun _ => x)) =
      inner ℝ z x ^ n • x := by
  induction n with
  | zero =>
    change tensorRid A (pure A real x 1) = 1 • x
    rw [tensorRid_pure]
  | succ n ih =>
    change partialPower A n z (contractLeft A (finiteTensor (n + 1) (fun _ => A)) z
      (pure A (finiteTensor (n + 1) (fun _ => A)) x
        (finitePure (n + 1) (fun _ => A) (fun _ => x)))) = _
    rw [contractLeft_pure, map_smul, ih, smul_smul]
    simp only [pow_succ, mul_comm]

theorem partialPower_unit_norm_le (A : HilbertDatum) (n : ℕ) (z : A.Carrier)
    (hz : ‖z‖ = 1) (u : (finiteTensor (n + 1) (fun _ => A)).Carrier) :
    ‖partialPower A n z u‖ ≤ ‖u‖ := by
  simpa [hz] using partialPower_norm_le A n z u

open ScalarHilbertKernel WeightedHilbertKernel

@[expose] def lowerFeature (K : PositiveKernel ℝ) (n : ℕ) (r : ℝ → ℝ → ℝ) (t : ℝ) :
    (datum K).Carrier :=
  ∫ u in (0 : ℝ)..t, (r t u * K.value t u ^ n) • feature K u

theorem partialPower_weightedFeature (K : PositiveKernel ℝ)
    (hK : Continuous (Function.uncurry K.value)) (n : ℕ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t : ℝ) :
    partialPower (datum K) n (feature K t) (weightedFeature K (n + 1) r t) =
      lowerFeature K n r t := by
  unfold weightedFeature lowerFeature
  rw [← (partialPower (datum K) n (feature K t)).intervalIntegral_comp_comm
    (weightedFeature_integrable K hK (n + 1) r hr t 0 t)]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [map_smul]
  change r t u • partialPower (datum K) n (feature K t)
    (finitePure (n + 1) (fun _ => datum K) (fun _ => feature K u)) = _
  rw [partialPower_pure, feature_inner, smul_smul]

theorem lowerFeature_integrable (K : PositiveKernel ℝ)
    (hK : Continuous (Function.uncurry K.value)) (n : ℕ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t a b : ℝ) :
    IntervalIntegrable (fun u => (r t u*K.value t u^n) • feature K u) volume a b :=
  (((hr.comp (continuous_const.prodMk continuous_id)).mul
    ((hK.comp (continuous_const.prodMk continuous_id)).pow n)).smul
    (feature_continuous K hK)).intervalIntegrable a b

theorem lowerFeature_norm_sq (K : PositiveKernel ℝ)
    (hK : Continuous (Function.uncurry K.value)) (n : ℕ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t : ℝ) :
    ‖lowerFeature K n r t‖^2 =
      ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..t,
        r t u*r t v*K.value t u^n*K.value t v^n*K.value u v := by
  rw [← real_inner_self_eq_norm_sq, lowerFeature,
    intervalIntegral_inner _ (lowerFeature_integrable K hK n r hr t 0 t)]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [inner_intervalIntegral _ (lowerFeature_integrable K hK n r hr t 0 t)]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  rw [real_inner_smul_left, real_inner_smul_right, feature_inner]
  ring

theorem lowerFeature_norm_le_weighted (K : PositiveKernel ℝ)
    (hK : Continuous (Function.uncurry K.value)) (n : ℕ) (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t : ℝ) (ht : K.value t t = 1) :
    ‖lowerFeature K n r t‖ ≤ ‖weightedFeature K (n + 1) r t‖ := by
  have hz : ‖feature K t‖ = 1 := by
    have hs := feature_norm_sq K t
    rw [ht] at hs
    nlinarith [norm_nonneg (feature K t)]
  rw [← partialPower_weightedFeature K hK n r hr t]
  exact partialPower_unit_norm_le (datum K) n (feature K t) hz _

end SphericalAging.HilbertTensorContraction
