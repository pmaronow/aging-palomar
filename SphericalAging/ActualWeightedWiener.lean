module

public import SphericalAging.WeightedWienerExtension
public import SphericalAging.ActualModelRestart

public section

/-! Actual annealed physical Brownian pairings, with the weighted extension
from the unweighted Brownian primitive bridge. The latter is explicitly an
upstream input, not an assumed weighted conclusion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace RealInnerProductSpace
namespace SphericalAging.ActualWeightedWiener
open HardSphereDynamics AnnealedHamiltonianEnergyStein FiniteModel
open WienerVectorGaussian WienerTrunkWeight WienerPairingFunctional WeightedWienerExtension

theorem model_memLp (N p : ℕ) (β : ℝ) (t : ℝ≥0) :
    MemLp (modelProcess N p β t) 2 (AnnealedModelLaw.law N p) := by
  by_cases hN : 0<N
  · exact (ActualModelRestart.modelProcess_restart (p:=p) hN β t).2.1
  · have hzero : N=0 := by omega
    subst N
    convert (MemLp.zero : MemLp (0 : AnnealedCutoffProcess.Parameter 0 p×VectorBrownian.Space 0→Vector 0) 2
      (AnnealedModelLaw.law 0 p)) using 1
    funext ω
    exact Subsingleton.elim _ _

@[expose] def modelLp (N p : ℕ) (β : ℝ) (t : ℝ≥0) :
    Lp (Vector N) 2 (AnnealedModelLaw.law N p) :=
  (model_memLp N p β t).toLp (modelProcess N p β t)

theorem modelLp_norm_sq_le (N p : ℕ) (β : ℝ) (t : ℝ≥0) :
    ‖modelLp N p β t‖^2≤(N:ℝ) := by
  by_cases hN : 0<N
  · apply norm_sq_le_of_sphere_bound (AnnealedModelLaw.parameterLaw N p)
    filter_upwards [(model_memLp N p β t).coeFn_toLp,
      (ActualModelRestart.modelProcess_physical (p:=p) hN β).2] with ω hω hs
    change ‖((model_memLp N p β t).toLp (modelProcess N p β t)) ω‖^2≤_
    rw [hω,←real_inner_self_eq_norm_sq]
    exact (hs t).le
  · have hzero : N=0 := by omega
    subst N
    have hz : modelLp 0 p β t=0 := by
      apply Lp.ext
      exact Eventually.of_forall (fun ω => Subsingleton.elim _ _)
    simp [hz]

@[expose] def actualFunctional (N p : ℕ) (β : ℝ) (t : ℝ≥0) : TimeL2→L[ℝ]ℝ :=
  pairingFunctional (AnnealedModelLaw.parameterLaw N p) (modelLp N p β t)

@[expose] def actualPairing (N p : ℕ) (β : ℝ) (t : ℝ≥0) (k : TimeL2) : ℝ :=
  (N:ℝ)⁻¹ * ∫ ω,⟪modelProcess N p β t ω,vectorIntegral k ω.2⟫_ℝ ∂AnnealedModelLaw.law N p

@[expose] def actualPrefixPairing (N p : ℕ) (β : ℝ) (t u : ℝ≥0) : ℝ :=
  (N:ℝ)⁻¹ * ∫ ω,⟪modelProcess N p β t ω,WithLp.toLp 2 (fun i => ω.2 i u)⟫_ℝ
    ∂AnnealedModelLaw.law N p

theorem actualFunctional_apply (N p : ℕ) (β : ℝ) (t : ℝ≥0) (k : TimeL2) :
    actualFunctional N p β t k=actualPairing N p β t k := by
  rw [actualFunctional,pairingFunctional_apply]
  unfold actualPairing
  congr 1
  apply integral_congr_ae
  filter_upwards [(model_memLp N p β t).coeFn_toLp] with ω hω
  exact congrArg (fun x => ⟪x,vectorIntegral k ω.2⟫_ℝ) hω

theorem actualFunctional_prefix (N p : ℕ) (β : ℝ) (t u : ℝ≥0) :
    actualFunctional N p β t (intervalIndicator u)=actualPrefixPairing N p β t u := by
  rw [actualFunctional,pairingFunctional_prefix]
  unfold actualPrefixPairing
  congr 1
  apply integral_congr_ae
  filter_upwards [(model_memLp N p β t).coeFn_toLp] with ω hω
  exact congrArg (fun x => ⟪x,WithLp.toLp 2 (fun i => ω.2 i u)⟫_ℝ) hω

theorem actualFunctional_norm_le (N p : ℕ) (β : ℝ) (t : ℝ≥0) :
    ‖actualFunctional N p β t‖≤1 :=
  pairingFunctional_norm_le (AnnealedModelLaw.parameterLaw N p) (modelLp N p β t)
    (modelLp_norm_sq_le N p β t)

theorem actual_weighted_from_prefix (p : ℕ) (β : ℝ) (t : ℝ≥0)
    {r k : ℝ→ℝ} {T : ℝ≥0}
    (hr : ContinuousOn r (Icc 0 (T:ℝ))) (hk : ContinuousOn k (Icc 0 (T:ℝ)))
    (hprefix : ∀ u : ℝ≥0,u≤T→Tendsto (fun N => actualPrefixPairing N p β t u) atTop
      (𝓝 (Real.sqrt 2 * ∫v in (0:ℝ)..(u:ℝ),r v))) :
    Tendsto (fun N => actualPairing N p β t (weight k T hk)) atTop
      (𝓝 (Real.sqrt 2 * ∫u in (0:ℝ)..(T:ℝ),k u*r u)) := by
  have hh := weighted_from_unweighted (fun N => actualFunctional N p β t)
    (fun N => actualFunctional_norm_le N p β t) hr hk (by
      intro u hu
      simpa only [actualFunctional_prefix] using hprefix u hu)
  simpa only [actualFunctional_apply] using hh

end SphericalAging.ActualWeightedWiener
