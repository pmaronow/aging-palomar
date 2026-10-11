module

public import SphericalAging.AlgorithmicOverlapLipschitz
public import SphericalAging.GaussianLipschitzConcentration
public import SphericalAging.GaussianPiLpLaw
public import SphericalAging.OrthogonalGaussianDisclosure

public section

/-! Actual correlated-algorithm overlap concentration under the original
independent ordered Gaussian disorder law. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.AlgorithmicOverlapConcentration
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open AlgorithmicOverlapLipschitz GaussianSmoothConcentration OrthogonalGaussianDisclosure
open scoped NNReal InnerProductSpace
variable {N p : ℕ}

@[expose] def pairLaw (N p : ℕ) : Measure (Fin 2→Disorder N p) :=
  Measure.pi (fun _ => disorderLaw N p)

instance : IsProbabilityMeasure (pairLaw N p) := by unfold pairLaw;infer_instance

@[expose] def tensorInputs (J : Fin 2→Disorder N p) : PairTensor N p :=
  WithLp.toLp 2 (fun i => WithLp.toLp 2 (J i))

theorem tensorInputs_hasLaw :
    HasLaw (tensorInputs (N:=N) (p:=p)) (stdGaussian (PairTensor N p)) (pairLaw N p) := by
  have hm : Measurable (tensorInputs (N:=N) (p:=p)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 2 => TensorSpace N p)).measurable.comp
      (measurable_pi_lambda (fun i =>
        (PiLp.continuous_toLp 2 (fun _ : TensorIndex N p => ℝ)).measurable.comp (measurable_pi_apply i)))
  refine ⟨hm.aemeasurable,?_⟩
  change (Measure.pi (fun _ : Fin 2 => disorderLaw N p)).map
    ((WithLp.toLp 2)∘(fun J i => WithLp.toLp 2 (J i)))=_
  rw [←Measure.map_map (by fun_prop) (by fun_prop),Measure.pi_map_pi
    (fun _ => (ordered_tensor_hasLaw N p).aemeasurable)]
  simp_rw [(ordered_tensor_hasLaw N p).map_eq]
  exact GaussianPiLpLaw.map_pi_stdGaussian

@[expose] def rawOverlap (ρ : ℝ) (A : TensorSpace N p→Vector N) (J : Fin 2→Disorder N p) : ℝ :=
  overlap ρ A (tensorInputs J)

@[expose] def overlapConstant (N : ℕ) (L : ℝ≥0) : ℝ≥0 :=
  ⟨9*(Real.pi/2)^2*(L:ℝ)^2/(N:ℝ),by positivity⟩

theorem overlap_constant_eq (hN : 0<N) (L : ℝ≥0) :
    rotationConstant ⟨3*(L:ℝ)/Real.sqrt (N:ℝ),by positivity⟩=overlapConstant N L := by
  apply NNReal.coe_injective
  change (Real.pi/2)^2*(3*(L:ℝ)/Real.sqrt (N:ℝ))^2=
    9*(Real.pi/2)^2*(L:ℝ)^2/(N:ℝ)
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hs := Real.sq_sqrt hNr.le
  have hsn := (Real.sqrt_pos.mpr hNr).ne'
  field_simp
  nlinarith

theorem rawOverlap_centered_hasSubgaussianMGF (hN : 0<N) (ρ : ℝ)
    (hρ : 0≤ρ) (hρ1 : ρ≤1) {L : ℝ≥0} (A : TensorSpace N p→Vector N)
    (hA : LipschitzWith L A) (hball : ∀J,‖A J‖≤Real.sqrt N) :
    HasSubgaussianMGF (fun J => rawOverlap ρ A J-∫J',rawOverlap ρ A J' ∂pairLaw N p)
      (overlapConstant N L) (pairLaw N p) := by
  have hLip := overlap_lipschitz hN ρ hρ hρ1 A hA hball
  have hG := GaussianLipschitzConcentration.centered_hasSubgaussianMGF (overlap ρ A) hLip
  rw [overlap_constant_eq hN L] at hG
  have hMean : (∫J,rawOverlap ρ A J ∂pairLaw N p)=
      ∫J,overlap ρ A J ∂stdGaussian (PairTensor N p) :=
    tensorInputs_hasLaw.integral_comp hLip.continuous.stronglyMeasurable.aestronglyMeasurable
  rw [←tensorInputs_hasLaw.map_eq] at hG
  have hh := HasSubgaussianMGF.of_map tensorInputs_hasLaw.aemeasurable hG
  rw [tensorInputs_hasLaw.map_eq] at hh
  rw [hMean]
  exact hh

theorem rawOverlap_centered_absolute_tail (hN : 0<N) (ρ : ℝ)
    (hρ : 0≤ρ) (hρ1 : ρ≤1) {L : ℝ≥0} (A : TensorSpace N p→Vector N)
    (hA : LipschitzWith L A) (hball : ∀J,‖A J‖≤Real.sqrt N) (ε : ℝ) (hε : 0≤ε) :
    (pairLaw N p).real {J | ε≤|rawOverlap ρ A J-∫J',rawOverlap ρ A J' ∂pairLaw N p|}≤
      2*Real.exp (-ε^2/(2*(overlapConstant N L:ℝ))) := by
  let X := fun J => rawOverlap ρ A J-∫J',rawOverlap ρ A J' ∂pairLaw N p
  have hG := rawOverlap_centered_hasSubgaussianMGF hN ρ hρ hρ1 A hA hball
  have hs : {J | ε≤|X J|}={J | ε≤X J}∪{J | ε≤-X J} := by
    ext J
    change ε≤|X J| ↔ ε≤X J ∨ ε≤-X J
    exact le_abs
  change (pairLaw N p).real {J | ε≤|X J|}≤_
  rw [hs]
  exact (measureReal_union_le _ _).trans
    (by simpa only [two_mul,Pi.neg_apply] using add_le_add (hG.measure_ge_le hε) (hG.neg.measure_ge_le hε))

end SphericalAging.AlgorithmicOverlapConcentration
