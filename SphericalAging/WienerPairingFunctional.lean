module

public import SphericalAging.WienerTrunkWeight
public import Mathlib.Algebra.Order.Chebyshev

public section

/-! The genuine vector Wiener map and the normalized sphere/Wiener pairing.
The norm bound is proved from the Itô isometry and the actual sphere radius. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace RealInnerProductSpace
namespace SphericalAging.WienerPairingFunctional
open WienerVectorGaussian FiniteModel VectorBrownian

variable {Ω : Type} [MeasurableSpace Ω] {N : ℕ}
variable (P : Measure Ω) [IsProbabilityMeasure P]

@[expose] def augmentedEval (i : Fin N) (ω : Ω×Space N) : Path := ω.2 i

theorem augmentedEval_preserving (i : Fin N) :
    MeasurePreserving (augmentedEval i) (P.prod (law N)) pathLaw :=
  (measurePreserving_eval (fun _ : Fin N => pathLaw) i).comp measurePreserving_snd

@[expose] def coordinateIntegral (i : Fin N) : TimeL2 →L[ℝ] Lp ℝ 2 (P.prod (law N)) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (augmentedEval i) (augmentedEval_preserving P i)).toContinuousLinearMap.comp
    (wienerIntegral scalar_isPreBrownian)

@[expose] def coordinateEmbedding (i : Fin N) : ℝ →L[ℝ] Vector N :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single i 1)

@[expose] def vectorIntegralL2 : TimeL2 →L[ℝ] Lp (Vector N) 2 (P.prod (law N)) :=
  ∑ i : Fin N,((coordinateEmbedding i).compLpL 2 (P.prod (law N))).comp (coordinateIntegral P i)

theorem coordinateIntegral_coe (i : Fin N) (k : TimeL2) :
    (coordinateIntegral P i k : Ω×Space N → ℝ)=ᵐ[P.prod (law N)]
      (fun ω => scalarIntegral k (ω.2 i)) := by
  have hp := (augmentedEval_preserving P i).quasiMeasurePreserving.ae (scalarIntegral_ae k)
  exact (Lp.coeFn_compMeasurePreserving _ (augmentedEval_preserving P i)).trans hp

theorem vectorIntegralL2_coe (k : TimeL2) :
    (vectorIntegralL2 (N:=N) P k : Ω×Space N → Vector N)=ᵐ[P.prod (law N)]
      (fun ω => vectorIntegral k ω.2) := by
  have hi : ∀ i : Fin N,
      ((coordinateEmbedding i).compLpL 2 (P.prod (law N)) (coordinateIntegral P i k) :
        Ω×Space N → Vector N)=ᵐ[P.prod (law N)]
        (fun ω => scalarIntegral k (ω.2 i) • EuclideanSpace.single i 1) := by
    intro i
    filter_upwards [(coordinateEmbedding i).coeFn_compLpL (coordinateIntegral P i k),
      coordinateIntegral_coe P i k] with ω h1 h2
    simpa only [coordinateEmbedding,ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply,h2] using h1
  have hs := Lp.coeFn_finsetSum (Finset.univ : Finset (Fin N))
    (fun i => (coordinateEmbedding i).compLpL 2 (P.prod (law N)) (coordinateIntegral P i k))
  filter_upwards [hs,ae_all_iff.mpr hi] with ω hω hι
  simp only [vectorIntegralL2,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]
  rw [hω]
  simp only [Finset.sum_apply]
  simp_rw [hι]
  ext j
  simp [vectorIntegral,Pi.single_apply]

theorem vectorIntegralL2_norm_sq (k : TimeL2) :
    ‖vectorIntegralL2 (N:=N) P k‖^2=(N:ℝ)*‖k‖^2 := by
  have hscalar (i : Fin N) :
      (∫ ω,scalarIntegral k (ω.2 i)^2 ∂P.prod (law N))=‖k‖^2 := by
    have hc := coordinateIntegral_coe P i k
    have hh := ProjectedTreeDrift.toLp_norm_sq
      ((Lp.memLp (coordinateIntegral P i k)).ae_eq hc)
    have he : ((Lp.memLp (coordinateIntegral P i k)).ae_eq hc).toLp
        (fun ω => scalarIntegral k (ω.2 i))=coordinateIntegral P i k := by
      apply Lp.ext
      exact ((Lp.memLp (coordinateIntegral P i k)).ae_eq hc).coeFn_toLp.trans hc.symm
    rw [he] at hh
    rw [←hh]
    change ‖Lp.compMeasurePreserving (augmentedEval i) (augmentedEval_preserving P i)
      (wienerIntegral scalar_isPreBrownian k)‖^2=‖k‖^2
    rw [Lp.norm_compMeasurePreserving,norm_wienerIntegral]
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  calc
    _ = ∫ ω,∑ i : Fin N,scalarIntegral k (ω.2 i)^2 ∂P.prod (law N) := by
      apply integral_congr_ae
      filter_upwards [vectorIntegralL2_coe P k] with ω hω
      rw [hω,real_inner_self_eq_norm_sq,EuclideanSpace.real_norm_sq_eq]
      rfl
    _ = ∑ i : Fin N,∫ ω,scalarIntegral k (ω.2 i)^2 ∂P.prod (law N) := by
      apply integral_finsetSum
      intro i _
      exact ((Lp.memLp (coordinateIntegral P i k)).ae_eq (coordinateIntegral_coe P i k)).integrable_sq
    _ = _ := by simp [hscalar]

@[expose] def pairingFunctional (X : Lp (Vector N) 2 (P.prod (law N))) : TimeL2 →L[ℝ] ℝ :=
  (N:ℝ)⁻¹ • (innerSL ℝ X).comp (vectorIntegralL2 P)

theorem pairingFunctional_apply (X : Lp (Vector N) 2 (P.prod (law N))) (k : TimeL2) :
    pairingFunctional P X k=(N:ℝ)⁻¹ *
      ∫ ω,⟪X ω,vectorIntegral k ω.2⟫_ℝ ∂P.prod (law N) := by
  simp only [pairingFunctional,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    innerSL_apply_apply,smul_eq_mul,L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [vectorIntegralL2_coe P k] with ω hω
  rw [hω]

theorem pairingFunctional_bound (X : Lp (Vector N) 2 (P.prod (law N)))
    (hX : ‖X‖^2≤(N:ℝ)) (k : TimeL2) : |pairingFunctional P X k|≤‖k‖ := by
  by_cases hN : N=0
  · simp [pairingFunctional,hN]
  have hNpos : (0:ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hprod : ‖X‖*‖vectorIntegralL2 (N:=N) P k‖≤(N:ℝ)*‖k‖ := by
    apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg hNpos.le (norm_nonneg _))).mp
    calc
      _ = ‖X‖^2*‖vectorIntegralL2 (N:=N) P k‖^2 := by ring
      _ ≤ (N:ℝ)*‖vectorIntegralL2 (N:=N) P k‖^2 :=
        mul_le_mul_of_nonneg_right hX (sq_nonneg _)
      _ = _ := by rw [vectorIntegralL2_norm_sq];ring
  calc
    |pairingFunctional P X k| = (N:ℝ)⁻¹ * |⟪X,vectorIntegralL2 P k⟫_ℝ| := by
      simp [pairingFunctional,abs_mul,abs_of_nonneg hNpos.le]
    _ ≤ (N:ℝ)⁻¹ * (‖X‖*‖vectorIntegralL2 P k‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (inv_nonneg.mpr hNpos.le)
    _ ≤ (N:ℝ)⁻¹ * ((N:ℝ)*‖k‖) :=
      mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr hNpos.le)
    _ = _ := by field_simp

theorem pairingFunctional_norm_le (X : Lp (Vector N) 2 (P.prod (law N)))
    (hX : ‖X‖^2≤(N:ℝ)) : ‖pairingFunctional P X‖≤1 := by
  apply (pairingFunctional P X).opNorm_le_bound (by norm_num)
  intro k
  simpa only [Real.norm_eq_abs,one_mul] using pairingFunctional_bound P X hX k

theorem norm_sq_le_of_sphere_bound (X : Lp (Vector N) 2 (P.prod (law N)))
    (hX : ∀ᵐ ω ∂P.prod (law N),‖X ω‖^2≤(N:ℝ)) : ‖X‖^2≤(N:ℝ) := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  calc
    _ = ∫ ω,‖X ω‖^2 ∂P.prod (law N) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun ω => real_inner_self_eq_norm_sq _)
    _ ≤ ∫ _ : Ω×Space N,(N:ℝ) ∂P.prod (law N) :=
      integral_mono_ae
        ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable X)).mp (Lp.memLp X))
        (integrable_const _) hX
    _ = _ := by simp

theorem scalarIntegral_prefix (u : ℝ≥0) :
    scalarIntegral (intervalIndicator u)=ᵐ[pathLaw] (fun ω : Path => ω u) := by
  have hh := coeFn_brownianLp scalar_isPreBrownian u
  rw [←wienerIntegral_intervalIndicator scalar_isPreBrownian u] at hh
  exact (scalarIntegral_ae (intervalIndicator u)).symm.trans hh

theorem vectorIntegral_prefix (u : ℝ≥0) :
    (fun ω : Ω×Space N => vectorIntegral (intervalIndicator u) ω.2)=ᵐ[P.prod (law N)]
      (fun ω => WithLp.toLp 2 (fun i => ω.2 i u)) := by
  have hi (i : Fin N) := (augmentedEval_preserving P i).quasiMeasurePreserving.ae
    (scalarIntegral_prefix u)
  filter_upwards [ae_all_iff.mpr hi] with ω hω
  ext i
  exact hω i

theorem pairingFunctional_prefix (X : Lp (Vector N) 2 (P.prod (law N))) (u : ℝ≥0) :
    pairingFunctional P X (intervalIndicator u)=(N:ℝ)⁻¹ *
      ∫ ω,⟪X ω,WithLp.toLp 2 (fun i => ω.2 i u)⟫_ℝ ∂P.prod (law N) := by
  rw [pairingFunctional_apply]
  congr 1
  apply integral_congr_ae
  filter_upwards [vectorIntegral_prefix (N:=N) P u] with ω hω
  rw [hω]

end SphericalAging.WienerPairingFunctional
