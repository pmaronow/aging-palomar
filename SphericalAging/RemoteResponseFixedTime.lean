module

public import SphericalAging.FiniteForkProjectionLimits
public import SphericalAging.GaussianSeedCostTheorem
public import SphericalAging.RemoteResponseTest

public section

/-! Source 11.11 Steps 1--3 on the literal finite physical fork space.
The preceding inputs are source 3.4's unweighted primitive limit and
source 10.4's endpoint/past law, concentration, energy, and Lipschitz maps.
The weighted Gaussian law, energy lower limit, and remote-response estimate
are all derived. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology InnerProductSpace
namespace SphericalAging.RemoteResponseFixedTime
open FiniteModel CKSpecification ForkSeedCoordinates WienerForkTransfer FiniteForkMoments
open ForkNormalizedEnergy ForkEnergyComparison RandomGaussianPairing RandomVectorBounds
open FiniteForkProjectionLimits AsymptoticErrorTransfer RemoteResponseTest
open GaussianSeedCostTheorem ExternalFieldUniformCost GaussianLandscape SphereInitialLaw
open ExternalFieldElementaryPenalty
open WienerTrunkWeight WienerVectorGaussian WeightedBrownianTheorem

theorem fixed_time {p K : ℕ} (hp : 3≤p) (hK : 0<K)
    {Lip : ℝ≥0} (H : PublishedFieldThreshold p Lip)
    (dim : ℕ→ℕ) (hDim : ∀n,1≤dim n) (hTop : Tendsto dim atTop atTop)
    {β : ℝ} {d : CKData} (h : CKEquations p β d) (T L : ℝ≥0) (hT : 0<T)
    {Q e γ ζ ε : ℝ} (hQ : 0<Q) (hQ1 : Q≤1)
    (hγ : 0≤γ) (hζ : 0≤ζ) (hε : 0≤ε)
    (hδ : 0≤thresholdEnergy p-Q^(-((p:ℝ)/2))*e)
    (Y : ∀n,Fin K→ForkSpace (dim n) p K→Vector (dim n))
    (hY : ∀n,ForkJointLaw β (T+L) T (Y n))
    (A : ∀n,Seed (dim n) K×Disorder (dim n) p→Vector (dim n))
    (hA : ∀n,Measurable (A n))
    (hgood : ∀n,∀ᵐξ ∂ForkSeedCoordinates.law (dim n) K,
      LipschitzWith Lip (fun J : EuclideanSpace ℝ (TensorIndex (dim n) p) => A n (ξ,J.ofLp)) ∧
        ∀J,‖A n (ξ,J)‖≤Real.sqrt (dim n))
    (hEnergy : limsup (fun n => |(∫z,Hamiltonian (dim n) p z.1.1.1
      (mean (Y n) z) ∂forkLaw (dim n) p K)/(dim n:ℝ)-e|) atTop≤γ)
    (hDefect : limsup (fun n => ∫z,(‖mean (Y n) z‖^2/(dim n:ℝ)-Q)^2
      ∂forkLaw (dim n) p K) atTop≤ζ)
    (hApprox : limsup (fun n => (∫z,‖A n z-projected Q (seededMean (Y n)) z‖^2
      ∂measure (dim n) p K)/(dim n:ℝ)) atTop≤ε^2)
    (hprimitive : ∀u : ℝ≥0,u≤T→Tendsto
      (fun n => brownianPrimitive (dim n) p β (T+L) u) atTop
      (𝓝 (∫v in (0:ℝ)..(u:ℝ),d.R (T+L) v))) :
    Real.sqrt (2*WhitePrefixResponse.remoteTail d (T+L) L/Q)≤
      (ExternalFieldSharpScalar.betaD p)^(-((p:ℝ)⁻¹))*
        (thresholdEnergy p-Q^(-((p:ℝ)/2))*e+Q^(-((p:ℝ)/2))*γ+
          comparison p Q*(ε+Real.sqrt ζ/Q))^((p:ℝ)⁻¹)+ε+Real.sqrt ζ/Q := by
  have hn n : 0<dim n := by have hh := hDim n;omega
  let μ n := measure (dim n) p K
  let M n := seededMean (Y n)
  let P n := projected Q (M n)
  let X n := normalized Q (M n)
  let a n := distanceRoot (μ n) (dim n) (A n) (P n)
  let b n := distanceRoot (μ n) (dim n) (P n) (X n)
  let ρ := Q^(-((p:ℝ)/2))
  let D := comparison p Q
  let κ := Real.sqrt ζ/Q
  let δ := thresholdEnergy p-ρ*e+ρ*γ+D*(ε+κ)
  have hρ : 0≤ρ := Real.rpow_nonneg hQ.le _
  have hD : 0≤D := comparison_nonneg p Q
  have hκ : 0≤κ := div_nonneg (Real.sqrt_nonneg _) hQ.le
  have hδ' : 0≤δ := by dsimp only [δ,ρ];positivity
  have hMb n : ∀ᵐz ∂μ n,‖M n z‖≤Real.sqrt (dim n) := seededMean_bound hK (hY n)
  have hMm n : MemLp (M n) 2 (μ n) := seededMean_memLp (hY n)
  have hPm n : MemLp (P n) 2 (μ n) := projected_memLp (Q:=Q) (hn n) (hMm n)
  have hXm n : MemLp (X n) 2 (μ n) := normalized_memLp (Q:=Q) (hMm n)
  have hAb n : ∀ᵐz ∂μ n,‖A n z‖≤Real.sqrt (dim n) := by
    filter_upwards [(measurePreserving_fst (μ:=ForkSeedCoordinates.law (dim n) K)
      (ν:=disorderLaw (dim n) p)).quasiMeasurePreserving.ae (hgood n)] with z hz
    exact hz.2 z.2
  have hAm n : MemLp (A n) 2 (μ n) :=
    MemLp.of_bound (hA n).aestronglyMeasurable (Real.sqrt (dim n)) (hAb n)
  have hPb n : ∀ᵐz ∂μ n,‖P n z‖≤Real.sqrt (dim n) := projected_bound Q (M n)
  have hXb n := normalized_bound hQ (hMb n)
  have haB : ∀n,a n≤2 := by
    intro n
    simpa only [a,one_mul,one_add_one_eq_two] using distanceRoot_le (hn n) (hAm n) (hPm n)
      (C:=1) (D:=1) (by norm_num) (by norm_num)
      (by simpa only [one_mul] using hAb n) (by simpa only [one_mul] using hPb n)
  have hbB : ∀n,b n≤1+(Real.sqrt Q)⁻¹ := by
    intro n
    exact distanceRoot_le (hn n) (hPm n) (hXm n) (C:=1) (D:=(Real.sqrt Q)⁻¹)
      (by norm_num) (by positivity) (by simpa only [one_mul] using hPb n) (hXb n)
  have haBound : IsBoundedUnder (·≤·) atTop a :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall haB)
  have hbBound : IsBoundedUnder (·≤·) atTop b :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hbB)
  have ha : limsup a atTop≤ε := distance_limsup_of_second_moment hn μ hAm hPm hε haB hApprox
  have hb : limsup b atTop≤κ := projection_limsup_le hn hK hQ hY (by
    simpa only [defect_transfer] using hDefect)
  let en n := expectedEnergy (μ:=μ n) Prod.snd (M n)
  let an n := expectedEnergy (μ:=μ n) Prod.snd (A n)
  have hEb n : |en n|≤GaussianLandscapeMoments.momentCeiling p 1 :=
    energy_abs_le (hn n) (by omega : 0<p) (disorder_hasLaw (dim n) p K)
      (hMm n).aestronglyMeasurable (hMb n)
  have hAbE n : |an n|≤GaussianLandscapeMoments.momentCeiling p 1 :=
    energy_abs_le (hn n) (by omega : 0<p) (disorder_hasLaw (dim n) p K)
      (hAm n).aestronglyMeasurable (hAb n)
  have hAlgBound : IsBoundedUnder (·≤·) atTop an :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => le_of_abs_le (hAbE n))
  have hMeanBound : IsBoundedUnder (·≤·) atTop (fun n => |en n-e|) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n =>
      (abs_sub _ _).trans (add_le_add (hEb n) le_rfl))
  have hMean : limsup (fun n => |en n-e|) atTop≤γ := by
    simpa only [en,M,μ,energy_transfer] using hEnergy
  have hpoint n : ρ*en n-D*(a n+b n)≤an n :=
    algorithm_energy_lower (hn n) (by omega : 0<p) hQ hQ1
      (disorder_hasLaw (dim n) p K) (hMm n) (hAm n) (hMb n) (hAb n)
  have heLower := energy_liminf_lower hρ hD hpoint hAlgBound hMeanBound
    haBound hbBound hMean ha hb
  have heLow : thresholdEnergy p-δ≤liminf
      (fun n => ∫z,SeedAlgorithmEnergyBounds.energy (A n) z ∂μ n) atTop := by
    have he : (fun n => ∫z,SeedAlgorithmEnergyBounds.energy (A n) z ∂μ n)=an := by
      funext n
      simp only [SeedAlgorithmEnergyBounds.energy,an,expectedEnergy,integral_div]
    rw [he]
    convert heLower using 1 <;> dsimp only [δ] <;> ring
  let k := testWeight d T L
  have hk : ContinuousOn k (Icc 0 (T:ℝ)) := testWeight_continuous h T L
  let w := weight k T hk
  have hw : ‖w‖^2=1 := (weight_norm_sq hk).trans (testWeight_unit h hT L)
  let G n := ForkSeedCoordinates.gaussian (N:=dim n) (K:=K) w
  have hG n : HasLaw (G n) (gaussianLaw (dim n)) (ForkSeedCoordinates.law (dim n) K) :=
    gaussian_hasLaw hw
  have hGlaw n : HasLaw (fun z => G n z.1) (gaussianLaw (dim n)) (μ n) :=
    (hG n).comp measurePreserving_fst.hasLaw
  have hcost := source11_9 hp H dim hDim hTop (fun n => ForkSeedCoordinates.law (dim n) K)
    G hG (fun n => gaussian_measurable w) A hA hgood hδ' heLow
  let g n := ∫z,|⟪A n z,G n z.1⟫_ℝ/(dim n:ℝ)| ∂μ n
  have hgBound : IsBoundedUnder (·≤·) atTop g :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n =>
      absolute_pairing_le_one (hn n) (hAm n) (hGlaw n) (hAb n))
  have hg : limsup g atTop≤(ExternalFieldSharpScalar.betaD p)^(-((p:ℝ)⁻¹))*δ^((p:ℝ)⁻¹) :=
    hcost.2
  have hpLimit := (source11_10 dim h hK T L hT Y hY hk (testWeight_unit h hT L) hprimitive).2.2
  rw [testWeight_response h hT L] at hpLimit
  have hf : Tendsto (fun n => pairing (μ:=μ n) (X n) (fun z => G n z.1)) atTop
      (𝓝 ((Real.sqrt Q)⁻¹*Real.sqrt (2*WhitePrefixResponse.remoteTail d (T+L) L))) := by
    simpa only [X,normalized,pairing_smul,μ,M,G,pairing_transfer] using
      hpLimit.const_mul (Real.sqrt Q)⁻¹
  have hfpoint n : pairing (μ:=μ n) (X n) (fun z => G n z.1)≤g n+a n+b n := by
    have hc := pairing_comparison (hn n) (hAm n) (hXm n) (hGlaw n)
    have ht := distanceRoot_triangle (hAm n) (hPm n) (hXm n)
    have hs := pairing_le_absolute (hn n) (hAm n) (hGlaw n)
    linarith [neg_abs_le (pairing (μ:=μ n) (A n) (fun z => G n z.1)-
      pairing (μ:=μ n) (X n) (fun z => G n z.1))]
  have hfinal := pairing_limit_upper hf hfpoint hgBound haBound hbBound hg ha hb
  have hS : 0≤2*WhitePrefixResponse.remoteTail d (T+L) L :=
    mul_nonneg (by norm_num) (remoteTail_positive h hT L).le
  rw [Real.sqrt_div hS,div_eq_mul_inv,mul_comm]
  exact hfinal

end SphericalAging.RemoteResponseFixedTime
