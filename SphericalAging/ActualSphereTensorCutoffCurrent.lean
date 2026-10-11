module

public import SphericalAging.ActualSphereTensorCurrentBounds

public section

/-! The exact finite tensor product-current receipt on the genuine
Gaussian landscape event. The rate is uniform in the tensor dimension
and in the interpolation variable, including both zero-lag endpoints. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualSphereTensorCutoffCurrent
open MeasureTheory Set
open FiniteModel HardSphereDynamics SphereFisherHelly SphereRotationGeometry
open ActualSphereTensorProductCurrent ActualSphereTensorCurrentBounds
open GaussianLandscape SphereGoodEventFisherClock
open scoped NNReal
variable {N p k : ℕ}

theorem actualTensorCurrent_square_bound_cutoff (hN : 0<N) (hp : 2≤p) (hk : 1≤k)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (E : FisherDensity N p β) (J : Disorder N p) (T a d A : ℝ)
    (hT : 0≤T) (hd : 0≤d) (hA : 0≤A) (hJ : J∈goodEvent N p A)
    {z : ℝ} (hz : z∈Icc 0 a) :
    (actualTensorCurrent (k:=k) β R hR E J T a d z)^2≤
      (2*(k:ℝ)*Real.exp ((β:ℝ)*(p:ℝ)^2*A*(a+d)))^2*
        (fisherInformation β J (E.ρ J (T+z))/(N:ℝ)) := by
  have hbase := actualTensorCurrent_square_bound hN hp hk β R hR hNR E J T a d z
    (add_nonneg hT hz.1) (add_nonneg hd hz.1)
  have hQ : landscapeNorm N p J≤A := hJ
  have hqtime : landscapeNorm N p J*(d+z)≤A*(a+d) :=
    mul_le_mul hQ (by linarith [hz.2]) (add_nonneg hd hz.1) hA
  have hexp : Real.exp ((β:ℝ)*(p:ℝ)^2*landscapeNorm N p J*(d+z))≤
      Real.exp ((β:ℝ)*(p:ℝ)^2*A*(a+d)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hqtime (mul_nonneg β.coe_nonneg (sq_nonneg (p:ℝ)))]
  have hc := mul_le_mul_of_nonneg_left hexp (show 0≤2*(k:ℝ) by positivity)
  have hcsq := (sq_le_sq₀ (by positivity) (by positivity)).mpr hc
  have hFI : 0≤fisherInformation β J (E.ρ J (T+z))/(N:ℝ) :=
    div_nonneg (SphereFisherClockDecay.spherical_fisher_nonneg β J (E.positive J) (T+z)) (Nat.cast_nonneg N)
  exact hbase.trans (mul_le_mul_of_nonneg_right hcsq hFI)

theorem actualTensorCurrent_abs_bound_cutoff (hN : 0<N) (hp : 2≤p) (hk : 1≤k)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (E : FisherDensity N p β) (J : Disorder N p) (T a d A : ℝ)
    (hT : 0≤T) (hd : 0≤d) (hA : 0≤A) (hJ : J∈goodEvent N p A)
    {z : ℝ} (hz : z∈Icc 0 a) :
    |actualTensorCurrent (k:=k) β R hR E J T a d z|≤
      (2*(k:ℝ)*Real.exp ((β:ℝ)*(p:ℝ)^2*A*(a+d)))*
        Real.sqrt (fisherInformation β J (E.ρ J (T+z))/(N:ℝ)) := by
  have hh := actualTensorCurrent_square_bound_cutoff hN hp hk β R hR hNR E J T a d A hT hd hA hJ hz
  have hFI : 0≤fisherInformation β J (E.ρ J (T+z))/(N:ℝ) :=
    div_nonneg (SphereFisherClockDecay.spherical_fisher_nonneg β J (E.positive J) (T+z)) (Nat.cast_nonneg N)
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs,mul_pow,Real.sq_sqrt hFI]
  exact hh

/-- All finite interpolation clauses used in source (10.13), derived
from the actual SDE semigroup and the preceding strong forward density. -/
theorem source10_13_finite (hN : 0<N) (hp : 2≤p) (hk : 1≤k)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (E : FisherDensity N p β) (J : Disorder N p) (T a d A : ℝ)
    (hT : 0≤T) (ha : 0≤a) (hd : 0≤d) (hA : 0≤A) (hJ : J∈goodEvent N p A) :
    Continuous (actualTensorPairing (k:=k) β R hR E J T a d) ∧
    Continuous (actualTensorCurrent (k:=k) β R hR E J T a d) ∧
    (∀z∈Ioo 0 a,HasDerivAt (actualTensorPairing (k:=k) β R hR E J T a d)
      (actualTensorCurrent (k:=k) β R hR E J T a d z) z) ∧
    (∀z∈Icc 0 a,|actualTensorPairing (k:=k) β R hR E J T a d z|≤1) ∧
    (∀z∈Icc 0 a,|actualTensorCurrent (k:=k) β R hR E J T a d z|≤
      (2*(k:ℝ)*Real.exp ((β:ℝ)*(p:ℝ)^2*A*(a+d)))*
        Real.sqrt (fisherInformation β J (E.ρ J (T+z))/(N:ℝ))) ∧
    actualTensorPairing (k:=k) β R hR E J T a d a-
      actualTensorPairing (k:=k) β R hR E J T a d 0=
        ∫z in (0:ℝ)..a,actualTensorCurrent (k:=k) β R hR E J T a d z := by
  refine ⟨actualTensorPairing_continuous hN β R hR E J T a d,
    actualTensorCurrent_continuous hN β R hR E J T a d,?_,?_,?_,?_⟩
  · intro z hz
    exact actualTensorPairing_hasDerivAt hN β R hR hNR E J T a d z
      (by linarith [hz.1]) hz.2 (by linarith [hz.1])
  · intro z hz
    exact actualTensorPairing_abs_le_one hN β R hR hNR E J T a d z (add_nonneg hT hz.1)
  · intro z hz
    exact actualTensorCurrent_abs_bound_cutoff hN hp hk β R hR hNR E J T a d A hT hd hA hJ hz
  · exact actualTensorPairing_increment_current hN β R hR hNR E J T a d ha
      (by simpa using hT) le_rfl (by simpa using hd)

end SphericalAging.ActualSphereTensorCutoffCurrent
