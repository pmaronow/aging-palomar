module

public import SphericalAging.SphereEulerLocalMoment
public import SphericalAging.AdditiveSphereApproximationCoefficients

public section

/-! Dimension-uniform Euler coefficient and local-energy constants on the
actual landscape norm event. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace SphericalAging.SphereEulerDimensionRate
open HardSphereDynamics SphereEulerCoefficients SphereEulerPredictable SphereEulerLocalMoment
open SphereEulerInterpolationAlgebra AdditiveSphereApproximationCoefficients
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def localRate (p : ℕ) (β A T : ℝ≥0) : ℝ≥0 := 2*T*(normRate p β A)^2+4
@[expose] def globalRate (p : ℕ) (β A T : ℝ≥0) : ℝ≥0 :=
  ⟨(4*(T:ℝ)^2*(stateRate p β A:ℝ)^2+32*(T:ℝ))*(localRate p β A T:ℝ)*
    Real.exp ((4*(T:ℝ)*(stateRate p β A:ℝ)^2+32)*(T:ℝ)),by positivity⟩

theorem drift_lipschitz_on_good (hN : 0<N) (hp : 2≤p) (β A : ℝ≥0)
    (J : FiniteModel.Disorder N p) (hJ : GaussianLandscape.landscapeNorm N p J≤A) (x y : State N) :
    ‖SphereEulerCoefficients.drift β J x-SphereEulerCoefficients.drift β J y‖≤
      (stateRate p β A:ℝ)*‖x-y‖ := by
  refine (drift_lipschitz_bound hN hp β.coe_nonneg J x y).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  change 1+(β:ℝ)*(p:ℝ)*GaussianLandscape.landscapeNorm N p J*2^(p-2)*(3*(p:ℝ)+5)≤
    1+(β:ℝ)*(p:ℝ)*(A:ℝ)*2^(p-2)*(3*(p:ℝ)+5)
  gcongr

theorem driftCap_sq_on_good (β A : ℝ≥0) (J : FiniteModel.Disorder N p)
    (hJ : GaussianLandscape.landscapeNorm N p J≤A) :
    (driftCap β J:ℝ)^2≤(N:ℝ)*(normRate p β A:ℝ)^2 := by
  have hn : (0:ℝ)≤N := Nat.cast_nonneg _
  have hb : (driftCap β J:ℝ)≤(normRate p β A:ℝ)*Real.sqrt N := by
    change (2+3*(β:ℝ)*(p:ℝ)*2^(p-1)*GaussianLandscape.landscapeNorm N p J)*Real.sqrt N≤
      (2+3*(β:ℝ)*(p:ℝ)*2^(p-1)*(A:ℝ))*Real.sqrt N
    gcongr
  refine (pow_le_pow_left₀ (driftCap β J).coe_nonneg hb 2).trans_eq ?_
  rw [mul_pow,Real.sq_sqrt hn]
  ring

theorem localCeiling_on_good (β A h : ℝ≥0) (J : FiniteModel.Disorder N p)
    (hJ : GaussianLandscape.landscapeNorm N p J≤A) (M : ℕ) :
    (localCeiling β h J M:ℝ)≤(N:ℝ)*(localRate p β A (grid h M):ℝ)*(h:ℝ) := by
  change (2*(grid h M:ℝ)*(driftCap β J:ℝ)^2+4*(N:ℝ))*(h:ℝ)≤_
  have hh := driftCap_sq_on_good β A J hJ
  calc
    _ ≤(2*(grid h M:ℝ)*((N:ℝ)*(normRate p β A:ℝ)^2)+4*(N:ℝ))*(h:ℝ) := by gcongr
    _ = _ := by simp only [localRate,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_ofNat];ring
end SphericalAging.SphereEulerDimensionRate
