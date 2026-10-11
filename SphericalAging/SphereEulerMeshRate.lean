module

public import SphericalAging.SphereEulerDimensionRate
public import Mathlib.Analysis.SpecificLimits.Basic

public section

/-! Uniform mesh constants for the genuine whole-vector Euler comparison. -/
noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal
namespace SphericalAging.SphereEulerMeshRate
open HardSphereDynamics SphereEulerPredictable SphereEulerLocalMoment
open SphereEulerDimensionRate AdditiveSphereApproximationCoefficients
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def mesh (T : ℝ≥0) (M : ℕ) : ℝ≥0 := T/M

theorem grid_mesh (T : ℝ≥0) {M : ℕ} (hM : M≠0) : grid (mesh T M) M=T := by
  apply NNReal.eq
  change (T:ℝ)/(M:ℝ)*(M:ℝ)=(T:ℝ)
  exact div_mul_cancel₀ _ (by exact_mod_cast hM)

theorem mesh_tendsto_zero (T : ℝ≥0) :
    Tendsto (fun M : ℕ => (mesh T M:ℝ)) atTop (𝓝 0) :=
  tendsto_const_div_atTop_nhds_zero_nat (T:ℝ)

@[expose] def comparisonBound (N : ℕ) (K C T t : ℝ≥0) : ℝ :=
  (T:ℝ)*(C:ℝ)*(4*(T:ℝ)*(K:ℝ)^2+32/(N:ℝ))*
    Real.exp ((4*(T:ℝ)*(K:ℝ)^2+32/(N:ℝ))*(t:ℝ))

theorem comparisonBound_uniform (hN : 0<N) (β A h : ℝ≥0)
    (J : FiniteModel.Disorder N p) (hJ : GaussianLandscape.landscapeNorm N p J≤A)
    (M : ℕ) (K t : ℝ≥0) (hK : K≤stateRate p β A) (ht : t≤grid h M) :
    comparisonBound N K (localCeiling β h J M) (grid h M) t≤
      (N:ℝ)*(globalRate p β A (grid h M):ℝ)*(h:ℝ) := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := by exact_mod_cast hN
  have hdiv : (32:ℝ)/(N:ℝ)≤32 := by
    apply (div_le_iff₀ hn0).mpr
    nlinarith
  have hc := localCeiling_on_good β A h J hJ M
  have hk : (K:ℝ)≤(stateRate p β A:ℝ) := hK
  have htime : (t:ℝ)≤(grid h M:ℝ) := ht
  have hr : 4*(grid h M:ℝ)*(K:ℝ)^2+32/(N:ℝ)≤
      4*(grid h M:ℝ)*(stateRate p β A:ℝ)^2+32 := by gcongr
  have he : Real.exp ((4*(grid h M:ℝ)*(K:ℝ)^2+32/(N:ℝ))*(t:ℝ))≤
      Real.exp ((4*(grid h M:ℝ)*(stateRate p β A:ℝ)^2+32)*(grid h M:ℝ)) := by
    apply Real.exp_le_exp.mpr
    gcongr
  unfold comparisonBound
  calc
    _ ≤ (grid h M:ℝ)*((N:ℝ)*(localRate p β A (grid h M):ℝ)*(h:ℝ))*
        (4*(grid h M:ℝ)*(stateRate p β A:ℝ)^2+32)*
        Real.exp ((4*(grid h M:ℝ)*(stateRate p β A:ℝ)^2+32)*(grid h M:ℝ)) := by
      gcongr
    _ = _ := by change _=(N:ℝ)*((4*(grid h M:ℝ)^2*(stateRate p β A:ℝ)^2+
        32*(grid h M:ℝ))*(localRate p β A (grid h M):ℝ)*
        Real.exp ((4*(grid h M:ℝ)*(stateRate p β A:ℝ)^2+32)*(grid h M:ℝ)))*(h:ℝ)
                ring

theorem normalized_comparisonBound_mesh (hN : 0<N) (β A T : ℝ≥0)
    (J : FiniteModel.Disorder N p) (hJ : GaussianLandscape.landscapeNorm N p J≤A)
    {M : ℕ} (hM : M≠0) (K : ℝ≥0) (hK : K≤stateRate p β A) :
    comparisonBound N K (localCeiling β (mesh T M) J M) T T/(N:ℝ)≤
      (globalRate p β A T:ℝ)*(T:ℝ)/(M:ℝ) := by
  have hh := comparisonBound_uniform hN β A (mesh T M) J hJ M K T hK
    (by rw [grid_mesh T hM])
  rw [grid_mesh T hM] at hh
  apply (div_le_iff₀ (by exact_mod_cast hN : (0:ℝ)<N)).mpr
  refine hh.trans_eq ?_
  change (N:ℝ)*(globalRate p β A T:ℝ)*((T:ℝ)/(M:ℝ))=
    (globalRate p β A T:ℝ)*(T:ℝ)/(M:ℝ)*(N:ℝ)
  ring

end SphericalAging.SphereEulerMeshRate
