module

public import SphericalAging.PhysicalResponseTerminalIncrement
public import SphericalAging.GaussianLandscapeMoments

public section

/-! Dimension-uniform Gaussian averaging of the physical response
increment ceiling. Only the proved actual landscape exponential moments
are used. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ResponseIncrementGaussianCeiling
open FiniteModel GaussianLandscape GaussianLandscapeMoments PhysicalVariationalMoments
open PhysicalResponseTerminalIncrement
set_option maxHeartbeats 1800000
variable {N p : ℕ}

@[expose] def landscapeSlope (p : ℕ) (β : ℝ≥0) : ℝ := (β:ℝ)*(p:ℝ)*((p:ℝ)+1)

@[expose] def incrementPrefactor (p : ℕ) (β δ : ℝ≥0) : ℝ :=
  2*(1+landscapeSlope p β)^2*(δ:ℝ)^2+16*(δ:ℝ)

@[expose] def annealedIncrementCeiling (p : ℕ) (β H δ : ℝ≥0) : ℝ :=
  incrementPrefactor p β δ*Real.exp (11*(H:ℝ))*
    momentCeiling p (2*landscapeSlope p β*(H:ℝ)+2)

theorem scalar_increment_exp_domination (α q H δ : ℝ)
    (hα : 0≤α) (hq : 0≤q) (hH : 0≤H) (hδ : 0≤δ) :
    (2*(1+α*q)^2*δ^2+16*δ)*Real.exp ((2*(1+α*q)+9)*H)≤
      (2*(1+α)^2*δ^2+16*δ)*Real.exp (11*H)*Real.exp ((2*α*H+2)*q) := by
  have hexp : 1≤Real.exp q := Real.one_le_exp hq
  have hqexp : q≤Real.exp q := by linarith [Real.add_one_le_exp q]
  have hK : 1+α*q≤(1+α)*Real.exp q := by nlinarith
  have hKpow := pow_le_pow_left₀ (by positivity : 0≤1+α*q) hK 2
  rw [mul_pow,←Real.exp_nat_mul] at hKpow
  norm_num only [Nat.cast_ofNat] at hKpow
  have h2exp : 1≤Real.exp (2*q) := Real.one_le_exp (by positivity)
  have hp : 2*(1+α*q)^2*δ^2+16*δ≤(2*(1+α)^2*δ^2+16*δ)*Real.exp (2*q) := by
    nlinarith [mul_le_mul_of_nonneg_right hKpow (by positivity : 0≤2*δ^2),
      mul_le_mul_of_nonneg_left h2exp (by positivity : 0≤16*δ)]
  refine (mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)).trans_eq ?_
  calc
    _=(2*(1+α)^2*δ^2+16*δ)*Real.exp (2*q+(2*(1+α*q)+9)*H) := by
      rw [mul_assoc,←Real.exp_add]
    _=(2*(1+α)^2*δ^2+16*δ)*Real.exp (11*H+(2*α*H+2)*q) := by
      congr 2
      ring
    _=_ := by rw [Real.exp_add];ring

theorem incrementCeiling_exp_domination (β : ℝ≥0) (J : Disorder N p) (H δ : ℝ≥0) :
    incrementCeiling p β J H δ ≤ incrementPrefactor p β δ*Real.exp (11*(H:ℝ))*
      Real.exp ((2*landscapeSlope p β*(H:ℝ)+2)*landscapeNorm N p J) := by
  exact scalar_increment_exp_domination (landscapeSlope p β) (landscapeNorm N p J) H δ
    (by unfold landscapeSlope;positivity) (landscapeNorm_nonnegative N p J) H.coe_nonneg δ.coe_nonneg

theorem incrementCeiling_integrable_bound (hN : 1≤N) (hp : 0<p) (β H δ : ℝ≥0) :
    Integrable (fun J : Disorder N p => incrementCeiling p β J H δ) (disorderLaw N p) ∧
      (∫J : Disorder N p,incrementCeiling p β J H δ ∂disorderLaw N p)≤annealedIncrementCeiling p β H δ := by
  let c := incrementPrefactor p β δ*Real.exp (11*(H:ℝ))
  let b := 2*landscapeSlope p β*(H:ℝ)+2
  have hc : 0≤c := by dsimp [c,incrementPrefactor];positivity
  have hexp := uniform_exponential_moment hN hp b
  have hi : Integrable (fun J : Disorder N p => c*Real.exp (b*landscapeNorm N p J)) (disorderLaw N p) :=
    hexp.1.const_mul c
  have hsm : AEStronglyMeasurable (fun J : Disorder N p => incrementCeiling p β J H δ) (disorderLaw N p) := by
    simp only [incrementCeiling,physicalDriftBound,NNReal.coe_add,NNReal.coe_mul,
      NNReal.coe_natCast,NNReal.coe_one,NNReal.coe_mk]
    apply Continuous.aestronglyMeasurable
    have hQ := landscapeNorm_continuous N p
    fun_prop
  have hm : Integrable (fun J : Disorder N p => incrementCeiling p β J H δ) (disorderLaw N p) :=
    hi.mono_nonneg hsm (.of_forall (fun J => incrementCeiling_nonneg p β J H δ))
      (.of_forall (fun J => incrementCeiling_exp_domination β J H δ))
  refine ⟨hm,?_⟩
  calc
    _≤∫J : Disorder N p,c*Real.exp (b*landscapeNorm N p J) ∂disorderLaw N p :=
      integral_mono hm hi (fun J => incrementCeiling_exp_domination β J H δ)
    _=c*(∫J : Disorder N p,Real.exp (b*landscapeNorm N p J) ∂disorderLaw N p) := integral_const_mul _ _
    _≤annealedIncrementCeiling p β H δ := mul_le_mul_of_nonneg_left hexp.2 hc

end SphericalAging.ResponseIncrementGaussianCeiling
