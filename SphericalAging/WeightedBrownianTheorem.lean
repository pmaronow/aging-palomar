module

public import SphericalAging.WienerForkTransfer
public import SphericalAging.CKSpecification

public section

/-! Complete local source 11.10, from its printed preceding inputs:
the source 3.4 Brownian primitive expectation bridge and the source 10.4
endpoint/trunk-past joint law. The Gaussian clauses, Wiener normalization,
finite branch averaging and continuous-weight limit are all derived. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace RealInnerProductSpace
namespace SphericalAging.WeightedBrownianTheorem
open FiniteModel AnnealedHamiltonianEnergyStein CKSpecification
open WienerVectorGaussian WienerTrunkWeight WienerForkTransfer ActualWeightedWiener

/-- The literal expectation of the Brownian observable Γ_N in source 3.4. -/
@[expose] def brownianPrimitive (N p : ℕ) (β : ℝ) (t u : ℝ≥0) : ℝ :=
  ∫ ω,⟪modelProcess N p β t ω,WithLp.toLp 2 (fun i => ω.2 i u)⟫_ℝ /
    (Real.sqrt 2*(N:ℝ)) ∂AnnealedModelLaw.law N p

theorem prefix_eq_sqrt_two_primitive (N p : ℕ) (β : ℝ) (t u : ℝ≥0) :
    actualPrefixPairing N p β t u=Real.sqrt 2*brownianPrimitive N p β t u := by
  unfold brownianPrimitive actualPrefixPairing
  rw [integral_div]
  by_cases hN : (N:ℝ)=0
  · simp [hN]
  · have hs : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
    field_simp

theorem response_row_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T L : ℝ≥0) :
    ContinuousOn (d.R (T+L)) (Icc 0 (T:ℝ)) := by
  apply h.response_continuous.comp ((continuous_const.prodMk continuous_id).continuousOn)
  intro u hu
  exact ⟨hu.1,hu.2.trans (le_add_of_nonneg_right L.coe_nonneg)⟩

/-- All printed clauses of the local weighted Brownian lemma. `hprimitive`
is precisely the preceding unweighted Γ_N expectation limit, and `hY` is
the preceding physical fork endpoint/past law. No weighted limit or
Gaussian target law is an input. Any dimension subsequence is allowed. -/
theorem source11_10 {ι : Type} {l : Filter ι} (dims : ι→ℕ)
    {p K : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (hK : 0<K) (T L : ℝ≥0) (hT : 0<T)
    (Y : ∀ i,Fin K→ForkSpace (dims i) p K→Vector (dims i))
    (hY : ∀ i,ForkJointLaw β (T+L) T (Y i))
    {k : ℝ→ℝ} (hk : ContinuousOn k (Icc 0 (T:ℝ)))
    (hunit : (∫u in (0:ℝ)..(T:ℝ),k u^2)=1)
    (hprimitive : ∀ u : ℝ≥0,u≤T→Tendsto
      (fun i => brownianPrimitive (dims i) p β (T+L) u) l
      (𝓝 (∫v in (0:ℝ)..(u:ℝ),d.R (T+L) v))) :
    (∀ i,HasLaw (fun ω : ForkSpace (dims i) p K => vectorIntegral (weight k T hk) ω.2)
      (stdGaussian (Vector (dims i))) (forkLaw (dims i) p K)) ∧
    (∀ i,IndepFun (fun ω : ForkSpace (dims i) p K => vectorIntegral (weight k T hk) ω.2)
      (fun ω => ω.1.1.1) (forkLaw (dims i) p K)) ∧
    Tendsto (fun i => meanPairing (Y i) (weight k T hk)) l
      (𝓝 (Real.sqrt 2*∫u in (0:ℝ)..(T:ℝ),k u*d.R (T+L) u)) := by
  refine ⟨fun i => (gaussian_trunk_independent_disorder hk hunit).1,
    fun i => (gaussian_trunk_independent_disorder hk hunit).2,?_⟩
  apply weighted_fork_from_prefix dims p K hK β (T+L) T Y hY
    (response_row_continuous h T L) hk
  intro u hu
  simpa only [prefix_eq_sqrt_two_primitive] using
    (hprimitive u hu).const_mul (Real.sqrt 2)

end SphericalAging.WeightedBrownianTheorem
