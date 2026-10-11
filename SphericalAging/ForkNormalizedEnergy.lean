module

public import SphericalAging.ForkBallProjection
public import SphericalAging.RandomGaussianPairing

public section

/-! Source 11.11's normalized mean, actual ball projection, homogeneity,
and algorithm energy comparison. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal InnerProductSpace Topology
namespace SphericalAging.ForkNormalizedEnergy
open FiniteModel GaussianLandscape LandscapeDerivatives ForkEnergyComparison ForkBallProjection
open RandomGaussianPairing
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

@[expose] def normalized {N : ℕ} (Q : ℝ) (M : Ω→Vector N) : Ω→Vector N := (Real.sqrt Q)⁻¹ • M
@[expose] def projected {N : ℕ} (Q : ℝ) (M : Ω→Vector N) : Ω→Vector N :=
  fun ω => clip (Real.sqrt N) (normalized Q M ω)
@[expose] def expectedEnergy {N p : ℕ} (J : Ω→Disorder N p) (X : Ω→Vector N) : ℝ :=
  (∫ω,Hamiltonian N p (J ω) (X ω) ∂μ)/(N:ℝ)
@[expose] def comparison (p : ℕ) (Q : ℝ) : ℝ := comparisonConstant p (Real.sqrt Q)⁻¹

theorem Hamiltonian_spatial_smul {N p : ℕ} (J : Disorder N p) (x : Vector N) (a : ℝ) :
    Hamiltonian N p J (a • x)=a^p*Hamiltonian N p J x := by
  rw [Hamiltonian_eq_diagonal,Hamiltonian_eq_diagonal]
  have hm := (tensorForm N p J).map_smul_univ (fun _ => a) (fun _ => x)
  rw [hm]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

theorem normalization_power {p : ℕ} {Q : ℝ} (hQ : 0<Q) :
    (Real.sqrt Q)⁻¹^p=Q^(-((p:ℝ)/2)) := by
  rw [inv_pow,Real.rpow_neg hQ.le,Real.rpow_div_two_eq_sqrt _ hQ.le,Real.rpow_natCast]

theorem expected_normalized {N p : ℕ} {Q : ℝ} (hQ : 0<Q)
    (J : Ω→Disorder N p) (M : Ω→Vector N) :
    expectedEnergy (μ:=μ) J (normalized Q M)=Q^(-((p:ℝ)/2))*expectedEnergy (μ:=μ) J M := by
  unfold expectedEnergy normalized
  simp only [Pi.smul_apply,Hamiltonian_spatial_smul,integral_const_mul]
  rw [normalization_power hQ]
  ring

theorem normalization_radius {Q : ℝ} (hQ : 0<Q) (hQ1 : Q≤1) :
    1≤(Real.sqrt Q)⁻¹ := by
  apply (one_le_inv₀ (Real.sqrt_pos.mpr hQ)).mpr
  exact (Real.sqrt_le_sqrt hQ1).trans_eq (by norm_num)

theorem normalized_memLp {N : ℕ} {Q : ℝ} {M : Ω→Vector N} (hM : MemLp M 2 μ) :
    MemLp (normalized Q M) 2 μ := hM.const_smul _

theorem projected_memLp {N : ℕ} (hN : 0<N) {Q : ℝ} {M : Ω→Vector N}
    (hM : MemLp M 2 μ) : MemLp (projected Q M) 2 μ := by
  apply MemLp.of_bound
    ((clip_continuous (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))).comp_aestronglyMeasurable
      (normalized_memLp hM).aestronglyMeasurable) (Real.sqrt N)
  exact Eventually.of_forall fun ω => clip_norm_le (Real.sqrt_nonneg _) _

theorem normalized_bound {N : ℕ} {Q : ℝ} (hQ : 0<Q) {M : Ω→Vector N}
    (hM : ∀ᵐω ∂μ,‖M ω‖≤Real.sqrt N) :
    ∀ᵐω ∂μ,‖normalized Q M ω‖≤(Real.sqrt Q)⁻¹*Real.sqrt N := by
  filter_upwards [hM] with ω hω
  simpa only [normalized,Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg Q)] using
    mul_le_mul_of_nonneg_left hω (inv_nonneg.mpr (Real.sqrt_nonneg _))

theorem projected_bound {N : ℕ} (Q : ℝ) (M : Ω→Vector N) :
    ∀ᵐω ∂μ,‖projected Q M ω‖≤Real.sqrt N :=
  Eventually.of_forall fun _ => clip_norm_le (Real.sqrt_nonneg _) _

theorem comparison_nonneg (p : ℕ) (Q : ℝ) : 0≤comparison p Q := by
  unfold comparison comparisonConstant
  positivity

theorem algorithm_energy_lower {N p : ℕ} (hN : 0<N) (hp : 0<p)
    {Q : ℝ} (hQ : 0<Q) (hQ1 : Q≤1)
    {J : Ω→Disorder N p} (hJ : HasLaw J (disorderLaw N p) μ)
    {M A : Ω→Vector N} (hM : MemLp M 2 μ) (hA : MemLp A 2 μ)
    (hMB : ∀ᵐω ∂μ,‖M ω‖≤Real.sqrt N) (hAB : ∀ᵐω ∂μ,‖A ω‖≤Real.sqrt N) :
    Q^(-((p:ℝ)/2))*expectedEnergy (μ:=μ) J M-
      comparison p Q*(distanceRoot μ N A (projected Q M)+
        distanceRoot μ N (projected Q M) (normalized Q M))≤
      expectedEnergy (μ:=μ) J A := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hr := normalization_radius hQ hQ1
  have hC : 0≤(Real.sqrt Q)⁻¹ := by positivity
  have hAB' : ∀ᵐω ∂μ,‖A ω‖≤(Real.sqrt Q)⁻¹*Real.sqrt N :=
    hAB.mono fun ω hω => hω.trans (by nlinarith [Real.sqrt_nonneg (N:ℝ)])
  have hb := random_energy_comparison hN hp hC hJ hA.aestronglyMeasurable
    (normalized_memLp hM).aestronglyMeasurable hAB' (normalized_bound hQ hMB)
  have he : |expectedEnergy (μ:=μ) J A-expectedEnergy (μ:=μ) J (normalized Q M)|≤
      comparison p Q*distanceRoot μ N A (normalized Q M) := by
    simpa only [expectedEnergy,comparison,←sub_div,abs_div,
      abs_of_pos hNr] using hb
  have ht := distanceRoot_triangle hA (projected_memLp (Q:=Q) hN hM)
    (normalized_memLp (Q:=Q) hM)
  have hc := mul_le_mul_of_nonneg_left ht (comparison_nonneg p Q)
  rw [expected_normalized hQ] at he
  linarith [neg_abs_le (expectedEnergy (μ:=μ) J A-
    Q^(-((p:ℝ)/2))*expectedEnergy (μ:=μ) J M)]

end SphericalAging.ForkNormalizedEnergy
