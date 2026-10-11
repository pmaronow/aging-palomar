module

public import SphericalAging.ForkBallProjectionLipschitz
public import SphericalAging.FiniteForkMoments

public section

/-! The literal sphere normalization, with zero mapped to zero, has the
same concentration control as the ball projection of the normalized
fork center. -/
noncomputable section
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ForkSphereNormalization
open MeasureTheory ProbabilityTheory Set Filter FiniteModel SphereInitialLaw
open ForkBallProjection ForkBallProjectionLipschitz ForkNormalizedEnergy
open FiniteForkMoments WienerForkTransfer ForkEnergyComparison RandomGaussianPairing
open scoped NNReal ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scalar_normalization_error {R S : ℝ} (hR : 0<R) (hS : 0<S)
    (x : E) (hx : x≠0) :
    ‖S⁻¹ • x-(R/‖x‖) • x‖/R≤|(‖x‖/(S*R))^2-1| := by
  have hn : ‖x‖≠0 := norm_ne_zero_iff.mpr hx
  have he : ‖S⁻¹ • x-(R/‖x‖) • x‖/R=|‖x‖/(S*R)-1| := by
    rw [←sub_smul,norm_smul,Real.norm_eq_abs]
    calc
      |S⁻¹-R/‖x‖| * ‖x‖/R=|(S⁻¹-R/‖x‖)*‖x‖/R| := by
        rw [abs_div,abs_mul,abs_of_pos hR,abs_of_nonneg (norm_nonneg x)]
      _ = _ := by congr 1;field_simp <;> ring
  rw [he]
  exact abs_sub_one_le_sq (div_nonneg (norm_nonneg x) (mul_pos hS hR).le)

theorem normalized_radial_secondMoment_pointwise {N : ℕ} (hN : 0<N)
    {Q : ℝ} (hQ : 0<Q) (m : Vector N) :
    ‖(Real.sqrt Q)⁻¹ • m-SphereInitialLaw.normalize N m‖^2/(N:ℝ)≤
      (‖m‖^2/(N:ℝ)-Q)^2/Q^2 := by
  by_cases hm : m=0
  · subst m
    simp [SphereInitialLaw.normalize,hQ.ne']
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hR := Real.sqrt_pos.mpr hNr
  have hS := Real.sqrt_pos.mpr hQ
  have he := scalar_normalization_error hR hS m hm
  have hs := (sq_le_sq₀ (div_nonneg (norm_nonneg _) hR.le) (abs_nonneg _)).mpr he
  rw [div_pow,Real.sq_sqrt hNr.le,sq_abs] at hs
  convert hs using 1
  · rfl
  · rw [div_pow,mul_pow,Real.sq_sqrt hQ.le,Real.sq_sqrt hNr.le]
    field_simp <;> ring

theorem projected_radial_secondMoment_pointwise {N : ℕ} (hN : 0<N)
    {Q : ℝ} (hQ : 0<Q) (m : Vector N) :
    ‖clip (Real.sqrt N) ((Real.sqrt Q)⁻¹ • m)-SphereInitialLaw.normalize N m‖^2/(N:ℝ)≤
      (‖m‖^2/(N:ℝ)-Q)^2/Q^2 := by
  have hr : ‖SphereInitialLaw.normalize N m‖≤Real.sqrt N := by
    by_cases hm : m=0
    · simp [hm,SphereInitialLaw.normalize,Real.sqrt_nonneg]
    · exact (normalize_norm m hm).le
  have he : clip (Real.sqrt N) (SphereInitialLaw.normalize N m)=SphereInitialLaw.normalize N m := by
    simp only [clip,if_pos hr]
  have hh := (clip_lipschitz (E:=Vector N) ⟨Real.sqrt N,Real.sqrt_nonneg _⟩).dist_le_mul
    ((Real.sqrt Q)⁻¹ • m) (SphereInitialLaw.normalize N m)
  change dist (clip (Real.sqrt N) ((Real.sqrt Q)⁻¹ • m))
    (clip (Real.sqrt N) (SphereInitialLaw.normalize N m))≤
      (1:ℝ)*dist ((Real.sqrt Q)⁻¹ • m) (SphereInitialLaw.normalize N m) at hh
  rw [he,one_mul,dist_eq_norm,dist_eq_norm] at hh
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hh
  exact (div_le_div_of_nonneg_right hs (Nat.cast_nonneg N)).trans
    (normalized_radial_secondMoment_pointwise hN hQ m)

@[expose] def radial {Ω : Type*} {N : ℕ} (M : Ω→Vector N) : Ω→Vector N :=
  fun ω => SphereInitialLaw.normalize N (M ω)

theorem radial_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {N : ℕ} {M : Ω→Vector N}
    (hM : MemLp M 2 μ) : MemLp (radial M) 2 μ := by
  apply MemLp.of_bound ((normalize_measurable N).comp_aemeasurable
    hM.aemeasurable).aestronglyMeasurable (Real.sqrt N)
  exact Eventually.of_forall fun ω => by
    by_cases hm : M ω=0
    · simp [radial,hm,SphereInitialLaw.normalize,Real.sqrt_nonneg]
    · exact (normalize_norm (M ω) hm).le

theorem radial_projection_second_moment_le {N p K : ℕ} (hN : 0<N) (hK : 0<K)
    {Q : ℝ} (hQ : 0<Q) {β : ℝ} {t T : ℝ≥0}
    {Y : Fin K→ForkSpace N p K→Vector N} (hY : ForkJointLaw β t T Y) :
    distanceRoot (measure N p K) N (projected Q (seededMean Y))
      (radial (seededMean Y))^2≤normDefect Q Y/Q^2 := by
  have hM := seededMean_memLp hY
  rw [distanceRoot_sq hN (projected_memLp (Q:=Q) hN hM) (radial_memLp hM)]
  have hi := ((projected_memLp (Q:=Q) hN hM).sub (radial_memLp hM)).norm.integrable_sq
  rw [←integral_div,normDefect,←integral_div]
  apply integral_mono_ae (hi.div_const _) ((defect_integrable hN hK hY Q).div_const _)
  exact Eventually.of_forall fun z => projected_radial_secondMoment_pointwise hN hQ _

end SphericalAging.ForkSphereNormalization
