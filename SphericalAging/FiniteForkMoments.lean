module

public import SphericalAging.ForkSeedCoordinates
public import SphericalAging.RandomVectorBounds

public section

/-! Actual finite-fork means on the canonical independent seed/disorder
space, including the expectation and concentration transfers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology InnerProductSpace
namespace SphericalAging.FiniteForkMoments
open FiniteModel WienerForkTransfer ForkSeedCoordinates ForkNormalizedEnergy
open ForkEnergyComparison RandomGaussianPairing RandomVectorBounds WienerVectorGaussian

@[expose] def measure (N p K : ℕ) := (ForkSeedCoordinates.law N K).prod (disorderLaw N p)
instance probability (N p K : ℕ) : IsProbabilityMeasure (measure N p K) := by
  unfold measure
  infer_instance
@[expose] def seededMean {N p K : ℕ} (Y : Fin K→ForkSpace N p K→Vector N) :
    Seed N K×Disorder N p→Vector N := fun z => mean Y (toFork z)
@[expose] def normDefect {N p K : ℕ} (Q : ℝ) (Y : Fin K→ForkSpace N p K→Vector N) : ℝ :=
  ∫z,(‖seededMean Y z‖^2/(N:ℝ)-Q)^2 ∂measure N p K

theorem seededMean_memLp {N p K : ℕ} {β : ℝ} {t T : ℝ≥0}
    {Y : Fin K→ForkSpace N p K→Vector N} (hY : ForkJointLaw β t T Y) :
    MemLp (seededMean Y) 2 (measure N p K) := by
  have hm : MemLp (mean Y) 2 (forkLaw N p K) :=
    (Lp.memLp (meanLp Y hY)).ae_eq (meanLp_coe Y hY)
  exact hm.comp_measurePreserving (toFork_measurePreserving N p K)

theorem seededMean_bound {N p K : ℕ} {β : ℝ} {t T : ℝ≥0} (hK : 0<K)
    {Y : Fin K→ForkSpace N p K→Vector N} (hY : ForkJointLaw β t T Y) :
    ∀ᵐz ∂measure N p K,‖seededMean Y z‖≤Real.sqrt N :=
  (toFork_measurePreserving N p K).quasiMeasurePreserving.ae (mean_norm_bound hK hY)

theorem pairing_transfer {N p K : ℕ} (Y : Fin K→ForkSpace N p K→Vector N) (k : TimeL2) :
    pairing (μ:=measure N p K) (seededMean Y)
      (fun z => gaussian k z.1)=meanPairing Y k := by
  unfold pairing meanPairing
  rw [div_eq_mul_inv,mul_comm]
  congr 1
  exact toFork_integral (fun z => ⟪mean Y z,vectorIntegral k z.2⟫_ℝ)

theorem energy_transfer {N p K : ℕ} (Y : Fin K→ForkSpace N p K→Vector N) :
    expectedEnergy (μ:=measure N p K) Prod.snd (seededMean Y)=
      (∫z,Hamiltonian N p z.1.1.1 (mean Y z) ∂forkLaw N p K)/(N:ℝ) := by
  unfold expectedEnergy
  congr 1
  exact toFork_integral (fun z => Hamiltonian N p z.1.1.1 (mean Y z))

theorem defect_transfer {N p K : ℕ} (Q : ℝ) (Y : Fin K→ForkSpace N p K→Vector N) :
    normDefect Q Y=(∫z,(‖mean Y z‖^2/(N:ℝ)-Q)^2 ∂forkLaw N p K) :=
  toFork_integral (fun z => (‖mean Y z‖^2/(N:ℝ)-Q)^2)

theorem defect_integrable {N p K : ℕ} (hN : 0<N) (hK : 0<K) {β : ℝ} {t T : ℝ≥0}
    {Y : Fin K→ForkSpace N p K→Vector N} (hY : ForkJointLaw β t T Y) (Q : ℝ) :
    Integrable (fun z => (‖seededMean Y z‖^2/(N:ℝ)-Q)^2) (measure N p K) := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hM := seededMean_memLp hY
  have hc : Continuous (fun x : Vector N => (‖x‖^2/(N:ℝ)-Q)^2) := by fun_prop
  have hmeas : AEStronglyMeasurable
      (fun z => (‖seededMean Y z‖^2/(N:ℝ)-Q)^2) (measure N p K) :=
    hc.comp_aestronglyMeasurable hM.aestronglyMeasurable
  apply (integrable_const ((1+|Q|)^2)).mono' hmeas
  filter_upwards [seededMean_bound hK hY] with z hz
  have hy : ‖seededMean Y z‖^2/(N:ℝ)∈Set.Icc (0:ℝ) 1 := by
    refine ⟨by positivity,?_⟩
    exact (div_le_one hNr).mpr
      ((sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hz |>.trans_eq
        (Real.sq_sqrt hNr.le))
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using
    (sq_le_sq₀ (abs_nonneg (‖seededMean Y z‖^2/(N:ℝ)-Q)) (by positivity : 0≤1+|Q|)).mpr
      ((abs_sub _ _).trans (by rw [abs_of_nonneg hy.1];exact add_le_add hy.2 le_rfl))

theorem projection_second_moment_le {N p K : ℕ} (hN : 0<N) (hK : 0<K)
    {Q : ℝ} (hQ : 0<Q) {β : ℝ} {t T : ℝ≥0}
    {Y : Fin K→ForkSpace N p K→Vector N} (hY : ForkJointLaw β t T Y) :
    distanceRoot (measure N p K) N (projected Q (seededMean Y))
      (normalized Q (seededMean Y))^2≤normDefect Q Y/Q^2 := by
  have hM := seededMean_memLp hY
  rw [distanceRoot_sq hN (projected_memLp (Q:=Q) hN hM) (normalized_memLp (Q:=Q) hM)]
  have hi := ((projected_memLp (Q:=Q) hN hM).sub (normalized_memLp (Q:=Q) hM)).norm.integrable_sq
  rw [←integral_div, normDefect, ←integral_div]
  apply integral_mono_ae (hi.div_const _) ((defect_integrable hN hK hY Q).div_const _)
  exact Eventually.of_forall fun z => ForkBallProjection.fork_concentration_pointwise hN hQ _

theorem defect_nonneg {N p K : ℕ} (Q : ℝ) (Y : Fin K→ForkSpace N p K→Vector N) :
    0≤normDefect Q Y := integral_nonneg fun _ => sq_nonneg _

theorem defect_bound {N p K : ℕ} (hN : 0<N) (hK : 0<K) {β : ℝ} {t T : ℝ≥0}
    {Y : Fin K→ForkSpace N p K→Vector N} (hY : ForkJointLaw β t T Y) (Q : ℝ) :
    normDefect Q Y≤(1+|Q|)^2 := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hb : ∀ᵐz ∂measure N p K,(‖seededMean Y z‖^2/(N:ℝ)-Q)^2≤(1+|Q|)^2 := by
    filter_upwards [seededMean_bound hK hY] with z hz
    have hy : ‖seededMean Y z‖^2/(N:ℝ)∈Set.Icc (0:ℝ) 1 := by
      refine ⟨by positivity,?_⟩
      exact (div_le_one hNr).mpr
        ((sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hz |>.trans_eq
          (Real.sq_sqrt hNr.le))
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (‖seededMean Y z‖^2/(N:ℝ)-Q)) (by positivity : 0≤1+|Q|)).mpr
        ((abs_sub _ _).trans (by rw [abs_of_nonneg hy.1];exact add_le_add hy.2 le_rfl))
  simpa only [normDefect,integral_const,probReal_univ,one_smul] using
    integral_mono_ae (defect_integrable hN hK hY Q) (integrable_const ((1+|Q|)^2)) hb

end SphericalAging.FiniteForkMoments
