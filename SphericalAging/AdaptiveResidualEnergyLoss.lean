module

public import SphericalAging.ForkEnergyComparison
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

public section

/-! Removing the disclosed-space component of an actual algorithm costs
only its normalized projection energy. Both the pointwise Hamiltonian
estimate and the original Gaussian-disorder expectation are derived. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal
namespace SphericalAging.AdaptiveResidualEnergyLoss
open FiniteModel GaussianLandscape GaussianLandscapeMoments ForkEnergyComparison

theorem Hamiltonian_residual_energy_loss {N p : ℕ} (hN : 0<N)
    (J : Disorder N p) (W : Submodule ℝ (Vector N)) (A : Vector N)
    (hA : ‖A‖≤Real.sqrt N) :
    |Hamiltonian N p J A-Hamiltonian N p J (Wᗮ.starProjection A)|/(N:ℝ)≤
      (p:ℝ)*landscapeNorm N p J*‖W.starProjection A‖/Real.sqrt N := by
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hr : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNr
  have hY := (Wᗮ.norm_starProjection_apply_le A).trans hA
  have hh := Hamiltonian_ball_lipschitz hN (by norm_num : (0:ℝ)≤1) J
    (by simpa only [one_mul] using hA) (by simpa only [one_mul] using hY)
  have hdiff : A-Wᗮ.starProjection A=W.starProjection A := by
    rw [Submodule.starProjection_orthogonal_val,sub_sub_cancel]
  simp only [one_pow,mul_one,hdiff] at hh
  have hd : Real.sqrt (N:ℝ)/(N:ℝ)=1/Real.sqrt (N:ℝ) := by
    apply (div_eq_div_iff hNr.ne' hr.ne').mpr
    simpa only [one_mul] using Real.mul_self_sqrt hNr.le
  calc
    _≤((p:ℝ)*landscapeNorm N p J*Real.sqrt N*‖W.starProjection A‖)/(N:ℝ) :=
      div_le_div_of_nonneg_right hh hNr.le
    _=((p:ℝ)*landscapeNorm N p J*‖W.starProjection A‖)*(Real.sqrt N/(N:ℝ)) := by ring
    _=_ := by rw [hd];ring

section Random
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem random_residual_energy_loss {N p : ℕ} (hN : 0<N) (hp : 0<p)
    {J : Ω→Disorder N p} (hJ : HasLaw J (disorderLaw N p) μ)
    (W : Ω→Submodule ℝ (Vector N)) (A : Ω→Vector N)
    (hA : AEStronglyMeasurable A μ)
    (hP : AEStronglyMeasurable (fun ω => (W ω).starProjection (A ω)) μ)
    (hAB : ∀ᵐω ∂μ,‖A ω‖≤Real.sqrt N) :
    (∫ω,|Hamiltonian N p (J ω) (A ω)-
      Hamiltonian N p (J ω) ((W ω)ᗮ.starProjection (A ω))|/(N:ℝ) ∂μ)≤
      (p:ℝ)*Real.sqrt (∫ω,(landscapeNorm N p (J ω))^2 ∂μ)*
        Real.sqrt (∫ω,‖(W ω).starProjection (A ω)‖^2/(N:ℝ) ∂μ) := by
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hr : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNr
  let P : Ω→Vector N := fun ω => (W ω).starProjection (A ω)
  let Y : Ω→Vector N := fun ω => (W ω)ᗮ.starProjection (A ω)
  have hY : AEStronglyMeasurable Y μ := by
    have he : Y=A-P := by
      funext ω
      exact Submodule.starProjection_orthogonal_val _
    rw [he]
    exact hA.sub hP
  have hYB : ∀ᵐω ∂μ,‖Y ω‖≤Real.sqrt N := by
    filter_upwards [hAB] with ω hω
    exact ((W ω)ᗮ.norm_starProjection_apply_le (A ω)).trans hω
  have hPB : ∀ᵐω ∂μ,‖P ω‖≤Real.sqrt N := by
    filter_upwards [hAB] with ω hω
    exact ((W ω).norm_starProjection_apply_le (A ω)).trans hω
  have hPM : MemLp P 2 μ := MemLp.of_bound hP (Real.sqrt N) hPB
  have hq : MemLp (fun ω => landscapeNorm N p (J ω)) 2 μ :=
    hJ.memLp_comp (landscape_memLp_two hN hp)
  have hg := hPM.norm
  have hHX := random_Hamiltonian_integrable hN hp (by norm_num : (0:ℝ)≤1) hJ hA
    (by simpa only [one_mul] using hAB)
  have hHY := random_Hamiltonian_integrable hN hp (by norm_num : (0:ℝ)≤1) hJ hY
    (by simpa only [one_mul] using hYB)
  have hAbs : Integrable (fun ω => |Hamiltonian N p (J ω) (A ω)-
      Hamiltonian N p (J ω) (Y ω)|/(N:ℝ)) μ := by
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using (hHX.sub hHY).norm.div_const (N:ℝ)
  have hProd := hq.integrable_mul hg
  have hb : (∫ω,|Hamiltonian N p (J ω) (A ω)-Hamiltonian N p (J ω) (Y ω)|/(N:ℝ) ∂μ)≤
      (p:ℝ)/Real.sqrt N*(∫ω,landscapeNorm N p (J ω)*‖P ω‖ ∂μ) := by
    rw [←integral_const_mul]
    apply integral_mono_ae hAbs (hProd.const_mul ((p:ℝ)/Real.sqrt N))
    filter_upwards [hAB] with ω hω
    exact (Hamiltonian_residual_energy_loss hN (J ω) (W ω) (A ω) hω).trans_eq (by
      dsimp only [P,Y,Pi.mul_apply]
      ring)
  have hCS := scalar_product_L2_bound hq hg
  have hnonneg : 0≤∫ω,landscapeNorm N p (J ω)*‖P ω‖ ∂μ :=
    integral_nonneg (fun ω => mul_nonneg (landscapeNorm_nonnegative _ _ _) (norm_nonneg _))
  rw [abs_of_nonneg hnonneg] at hCS
  have hqn : ‖hq.toLp (fun ω => landscapeNorm N p (J ω))‖=
      Real.sqrt (∫ω,(landscapeNorm N p (J ω))^2 ∂μ) := by
    rw [←ProjectedTreeDrift.toLp_norm_sq hq,Real.sqrt_sq (norm_nonneg _)]
  have hgn : ‖hg.toLp (fun ω => ‖P ω‖)‖/Real.sqrt N=
      Real.sqrt (∫ω,‖P ω‖^2/(N:ℝ) ∂μ) := by
    rw [integral_div,Real.sqrt_div,←ProjectedTreeDrift.toLp_norm_sq hg,
      Real.sqrt_sq (norm_nonneg _)]
    exact integral_nonneg (fun ω => sq_nonneg ‖P ω‖)
  calc
    _≤(p:ℝ)/Real.sqrt N*(∫ω,landscapeNorm N p (J ω)*‖P ω‖ ∂μ) := hb
    _≤(p:ℝ)/Real.sqrt N*(‖hq.toLp (fun ω => landscapeNorm N p (J ω))‖*
        ‖hg.toLp (fun ω => ‖P ω‖)‖) :=
      mul_le_mul_of_nonneg_left hCS (by positivity)
    _=(p:ℝ)*‖hq.toLp (fun ω => landscapeNorm N p (J ω))‖*
        (‖hg.toLp (fun ω => ‖P ω‖)‖/Real.sqrt N) := by ring
    _=_ := by rw [hqn,hgn]

theorem expected_energy_difference_le_loss {N p : ℕ} (hN : 0<N) (hp : 0<p)
    {J : Ω→Disorder N p} (hJ : HasLaw J (disorderLaw N p) μ)
    (W : Ω→Submodule ℝ (Vector N)) (A : Ω→Vector N)
    (hA : AEStronglyMeasurable A μ)
    (hP : AEStronglyMeasurable (fun ω => (W ω).starProjection (A ω)) μ)
    (hAB : ∀ᵐω ∂μ,‖A ω‖≤Real.sqrt N) :
    (∫ω,Hamiltonian N p (J ω) (A ω) ∂μ)/(N:ℝ)-
      (∫ω,Hamiltonian N p (J ω) ((W ω)ᗮ.starProjection (A ω)) ∂μ)/(N:ℝ)≤
    ∫ω,|Hamiltonian N p (J ω) (A ω)-
      Hamiltonian N p (J ω) ((W ω)ᗮ.starProjection (A ω))|/(N:ℝ) ∂μ := by
  let Y : Ω→Vector N := fun ω => (W ω)ᗮ.starProjection (A ω)
  have hY : AEStronglyMeasurable Y μ := by
    have he : Y=A-(fun ω => (W ω).starProjection (A ω)) := by
      funext ω
      exact Submodule.starProjection_orthogonal_val _
    rw [he]
    exact hA.sub hP
  have hYB : ∀ᵐω ∂μ,‖Y ω‖≤Real.sqrt N := by
    filter_upwards [hAB] with ω hω
    exact ((W ω)ᗮ.norm_starProjection_apply_le (A ω)).trans hω
  have hHX := random_Hamiltonian_integrable hN hp (by norm_num : (0:ℝ)≤1) hJ hA
    (by simpa only [one_mul] using hAB)
  have hHY := random_Hamiltonian_integrable hN hp (by norm_num : (0:ℝ)≤1) hJ hY
    (by simpa only [one_mul] using hYB)
  rw [←sub_div,←integral_sub hHX hHY,←integral_div]
  apply integral_mono ((hHX.sub hHY).div_const (N:ℝ))
    ((hHX.sub hHY).norm.div_const (N:ℝ))
  intro ω
  exact div_le_div_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg N)

end Random

/-- The independent seed/original disorder model; the original Gaussian law
and its finite second moment are proved, rather than supplied as a loss bound. -/
theorem actual_seed_residual_energy_loss {N p : ℕ} (hN : 0<N) (hp : 0<p)
    {S : Type} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (W : S×Disorder N p→Submodule ℝ (Vector N)) (A : S×Disorder N p→Vector N)
    (hA : AEStronglyMeasurable A (ν.prod (disorderLaw N p)))
    (hP : AEStronglyMeasurable (fun z => (W z).starProjection (A z)) (ν.prod (disorderLaw N p)))
    (hAB : ∀ᵐz ∂ν.prod (disorderLaw N p),‖A z‖≤Real.sqrt N) :
    (∫z,|Hamiltonian N p z.2 (A z)-Hamiltonian N p z.2 ((W z)ᗮ.starProjection (A z))|/(N:ℝ)
      ∂ν.prod (disorderLaw N p))≤
      (p:ℝ)*Real.sqrt (∫J,(landscapeNorm N p J)^2 ∂disorderLaw N p)*
        Real.sqrt (∫z,‖(W z).starProjection (A z)‖^2/(N:ℝ) ∂ν.prod (disorderLaw N p)) := by
  have hJ : HasLaw (Prod.snd : S×Disorder N p→Disorder N p) (disorderLaw N p)
      (ν.prod (disorderLaw N p)) := measurePreserving_snd.hasLaw
  have hh := random_residual_energy_loss hN hp hJ W A hA hP hAB
  have hi := hJ.integral_comp (((landscapeNorm_continuous N p).pow 2).aestronglyMeasurable)
  dsimp only [Function.comp_apply,Pi.pow_apply] at hi
  simpa only [hi] using hh

/-- A p-only uniform constant for source10.7 Step2, still against the literal
original disorder and the actual normalized disclosed-space projection energy. -/
theorem actual_seed_residual_energy_loss_uniform {N p : ℕ} (hN : 0<N) (hp : 0<p)
    {S : Type} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (W : S×Disorder N p→Submodule ℝ (Vector N)) (A : S×Disorder N p→Vector N)
    (hA : AEStronglyMeasurable A (ν.prod (disorderLaw N p)))
    (hP : AEStronglyMeasurable (fun z => (W z).starProjection (A z)) (ν.prod (disorderLaw N p)))
    (hAB : ∀ᵐz ∂ν.prod (disorderLaw N p),‖A z‖≤Real.sqrt N) :
    (∫z,|Hamiltonian N p z.2 (A z)-Hamiltonian N p z.2 ((W z)ᗮ.starProjection (A z))|/(N:ℝ)
      ∂ν.prod (disorderLaw N p))≤
      (p:ℝ)*Real.sqrt (momentCeiling p 2)*
        Real.sqrt (∫z,‖(W z).starProjection (A z)‖^2/(N:ℝ) ∂ν.prod (disorderLaw N p)) := by
  have hh := actual_seed_residual_energy_loss hN hp ν W A hA hP hAB
  have hmoment : (∫J,(landscapeNorm N p J)^2 ∂disorderLaw N p)≤momentCeiling p 2 := by
    simpa only [Real.rpow_two] using
      (uniform_real_power_moment (show 1≤N by omega) hp (k:=2) (by norm_num)).2
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmoment) (Nat.cast_nonneg p)) (Real.sqrt_nonneg _))

/-- The actual residual has the required lower energy, with loss obtained
from the original Gaussian Hamiltonian rather than assumed. -/
theorem actual_seed_residual_energy_lower {N p : ℕ} (hN : 0<N) (hp : 0<p)
    {S : Type} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (W : S×Disorder N p→Submodule ℝ (Vector N)) (A : S×Disorder N p→Vector N)
    (hA : AEStronglyMeasurable A (ν.prod (disorderLaw N p)))
    (hP : AEStronglyMeasurable (fun z => (W z).starProjection (A z)) (ν.prod (disorderLaw N p)))
    (hAB : ∀ᵐz ∂ν.prod (disorderLaw N p),‖A z‖≤Real.sqrt N) :
    (∫z,Hamiltonian N p z.2 (A z) ∂ν.prod (disorderLaw N p))/(N:ℝ)-
      (p:ℝ)*Real.sqrt (momentCeiling p 2)*
        Real.sqrt (∫z,‖(W z).starProjection (A z)‖^2/(N:ℝ) ∂ν.prod (disorderLaw N p))≤
    (∫z,Hamiltonian N p z.2 ((W z)ᗮ.starProjection (A z)) ∂ν.prod (disorderLaw N p))/(N:ℝ) := by
  have hJ : HasLaw (Prod.snd : S×Disorder N p→Disorder N p) (disorderLaw N p)
      (ν.prod (disorderLaw N p)) := measurePreserving_snd.hasLaw
  have hh := (expected_energy_difference_le_loss hN hp hJ W A hA hP hAB).trans
    (actual_seed_residual_energy_loss_uniform hN hp ν W A hA hP hAB)
  linarith

end SphericalAging.AdaptiveResidualEnergyLoss
