module

public import SphericalAging.CompactCKKernelContinuity
public import SphericalAging.CKResponsePrimitiveKernel

public section

/-! The nonnegative-time memory limits have exactly the printed CK
normalization, after the genuine Γ primitive and correlation symmetry
are identified. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal
namespace SphericalAging.CompactCKPrimitiveSlopeIdentification
open CompactKernelMemoryLimit ActualCompactCKSlopeLimit CompactCKKernelContinuity
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

@[expose]  def realKernel (K : Kernel) (t s : ℝ) : ℝ := K t.toNNReal s.toNNReal

@[expose]  def realCKData (p : ℕ) (β : ℝ≥0) (C R : Kernel) : CKSpecification.CKData where
  C := realKernel C
  R := realKernel R
  multiplier := fun t => effectiveMultiplier p β C R t.toNNReal

 theorem realKernel_continuous {K : Kernel} (hK : Continuous (Function.uncurry K)) :
    Continuous (Function.uncurry (realKernel K)) :=
  hK.comp ((continuous_real_toNNReal.comp continuous_fst).prodMk
    (continuous_real_toNNReal.comp continuous_snd))

 theorem realCKData_multiplier_continuous (p : ℕ) (β : ℝ≥0) {C R : Kernel}
    (hC : Continuous (Function.uncurry C)) (hR : Continuous (Function.uncurry R)) :
    Continuous (realCKData p β C R).multiplier :=
  (effectiveMultiplier_continuous p β hC hR).comp continuous_real_toNNReal

 theorem effectiveMultiplier_eq_printed (p : ℕ) (β : ℝ≥0) {C R : Kernel}
    (hSymm : ∀t s,C t s=C s t) (t : ℝ≥0) :
    (realCKData p β C R).multiplier t=
      1+(β : ℝ)^2*(p : ℝ)^2*CKSpecification.memoryMass p (realCKData p β C R) t := by
  simp only [realCKData,Real.toNNReal_coe,effectiveMultiplier,CKSpecification.memoryMass,realKernel,
    correlationMemory,pow_zero,mul_one]
  congr 2
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [hSymm u.toNNReal t]

 theorem gammaSlope_eq_primitive {p : ℕ} (hp : 1≤p) (β T : ℝ≥0) {C G R : Kernel}
    (hSymm : ∀t≤T,∀s≤T,C t s=C s t)
    (hPrefix : ∀t≤T,∀s≤T,G t s=ResponsePrimitiveInterchange.responsePrimitive (realKernel R) t s)
    (t s : ℝ≥0) (ht : t≤T) (hs : s≤T) :
    gammaSlope p β C G R t s=
      ResponsePrimitiveInterchange.gammaSlope (realCKData p β C R).multiplier
        (CKResponsePrimitiveKernel.memoryKernel p β (realKernel C) (realKernel R))
          (realKernel R) t s := by
  simp only [gammaSlope,ResponsePrimitiveInterchange.gammaSlope,realCKData,Real.toNNReal_coe]
  rw [hPrefix t ht s hs]
  congr 1
  unfold gammaMemory
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp only
  rw [uIcc_of_le t.coe_nonneg] at hu
  have huT : u.toNNReal≤T := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ hu.1]
    exact hu.2.trans (show (t : ℝ)≤T from ht)
  simp only [CKResponsePrimitiveKernel.memoryKernel,realKernel,Real.toNNReal_coe]
  rw [hSymm u.toNNReal huT t ht,hPrefix u.toNNReal huT s hs,
    Nat.cast_sub hp,Nat.cast_one,Real.coe_toNNReal _ hu.1]
  ring

 theorem correlationSlope_eq_printed {p : ℕ} (hp : 1≤p) (β T : ℝ≥0) {C R : Kernel}
    (hSymm : ∀t≤T,∀s≤T,C t s=C s t)
    (s t : ℝ≥0) (hs : s≤T) (ht : t≤T) :
    correlationSlope p β C R s t=CKSpecification.correlationSlope p β (realCKData p β C R) t s := by
  simp only [correlationSlope,CKSpecification.correlationSlope,realCKData,realKernel,Real.toNNReal_coe]
  rw [hSymm s hs t ht]
  congr 1
  · congr 1
    unfold correlationMemory
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [uIcc_of_le t.coe_nonneg] at hu
    have huT : u.toNNReal≤T := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ hu.1]
      exact hu.2.trans (show (t : ℝ)≤T from ht)
    simp only [pow_one,CKSpecification.xiDoublePrime]
    rw [hSymm u.toNNReal huT t ht,Nat.cast_sub hp,Nat.cast_one]
    ring
  · unfold correlationMemory
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [uIcc_of_le s.coe_nonneg] at hu
    have huT : u.toNNReal≤T := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ hu.1]
      exact hu.2.trans (show (s : ℝ)≤T from hs)
    simp only [pow_zero,mul_one,CKSpecification.xiPrime]
    rw [hSymm u.toNNReal huT t ht]
    ring

end SphericalAging.CompactCKPrimitiveSlopeIdentification
