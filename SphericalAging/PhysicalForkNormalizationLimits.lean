module

public import SphericalAging.PhysicalForkCenterConcentration
public import SphericalAging.ForkSphereNormalization

public section

/-! The two additional normalization clauses of source10.4 for the
actual fork: scaled mean-square distance from the ball projection to
the predicted normalization or to the sphere normalization, with
dimension limsup taken before stationary time. -/
noncomputable section
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.PhysicalForkNormalizationLimits
open MeasureTheory ProbabilityTheory Filter Set FiniteModel HardSphereDynamics
open WienerForkTransfer FiniteForkMoments ForkNormalizedEnergy ForkSphereNormalization
open ForkEnergyComparison RandomGaussianPairing PhysicalForkCenterConcentration
open PhysicalForkConstruction AnnealedHamiltonianEnergyStein
open CKSpecification StationaryClusterInputs ActualForkMeanBridge SphereFisherHelly
open ActualSphereForkEndpoints ForkParameterBounds
open scoped NNReal ENNReal Topology

@[expose] def normalizationError {N p K : ℕ} (Q : ℝ)
    (Y : Fin K→ForkSpace N p K→Vector N) : ℝ :=
  (∫z,‖projected Q (seededMean Y) z-normalized Q (seededMean Y) z‖^2
    ∂measure N p K)/(N:ℝ)

@[expose] def radialError {N p K : ℕ} (Q : ℝ)
    (Y : Fin K→ForkSpace N p K→Vector N) : ℝ :=
  (∫z,‖projected Q (seededMean Y) z-radial (seededMean Y) z‖^2
    ∂measure N p K)/(N:ℝ)

theorem normalizationError_nonneg {N p K : ℕ} (Q : ℝ)
    (Y : Fin K→ForkSpace N p K→Vector N) : 0≤normalizationError Q Y :=
  div_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (Nat.cast_nonneg N)

theorem radialError_nonneg {N p K : ℕ} (Q : ℝ)
    (Y : Fin K→ForkSpace N p K→Vector N) : 0≤radialError Q Y :=
  div_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (Nat.cast_nonneg N)

theorem normalizationError_le {N p K : ℕ} (hN : 0<N) (hK : 0<K)
    {Q : ℝ} (hQ : 0<Q) {β : ℝ} {t T : ℝ≥0}
    {Y : Fin K→ForkSpace N p K→Vector N} (hY : ForkJointLaw β t T Y) :
    normalizationError Q Y≤normDefect Q Y/Q^2 := by
  have hM := seededMean_memLp hY
  rw [normalizationError,←distanceRoot_sq hN (projected_memLp (Q:=Q) hN hM)
    (normalized_memLp (Q:=Q) hM)]
  exact projection_second_moment_le hN hK hQ hY

theorem radialError_le {N p K : ℕ} (hN : 0<N) (hK : 0<K)
    {Q : ℝ} (hQ : 0<Q) {β : ℝ} {t T : ℝ≥0}
    {Y : Fin K→ForkSpace N p K→Vector N} (hY : ForkJointLaw β t T Y) :
    radialError Q Y≤normDefect Q Y/Q^2 := by
  have hM := seededMean_memLp hY
  rw [radialError,←distanceRoot_sq hN (projected_memLp (Q:=Q) hN hM) (radial_memLp hM)]
  exact radial_projection_second_moment_le hN hK hQ hY

/-- The exact ordered normalization consequences of preceding norm
concentration, with both error bounds proved from the literal vectors. -/
theorem normalization_errors_ordered {dim : ℕ→ℕ} (hDim : ∀j,0<dim j)
    {p K : ℕ} (hK : 0<K) {β Q : ℝ} (hQ : 0<Q) {t T : ℕ→ℝ≥0}
    {Y : ∀n j,Fin K→ForkSpace (dim j) p K→Vector (dim j)}
    (hY : ∀n j,ForkJointLaw β (t n) (T n) (Y n j))
    (hDefect : Tendsto (fun v : ℕ×ℕ => normDefect Q (Y v.1 v.2))
      ((atTop : Filter ℕ).curry (atTop : Filter ℕ)) (𝓝 0)) :
    Tendsto (fun n => limsup (fun j => normalizationError Q (Y n j)) atTop) atTop (𝓝 0) ∧
      Tendsto (fun n => limsup (fun j => radialError Q (Y n j)) atTop) atTop (𝓝 0) := by
  have hNorm n j := normalizationError_le (hDim j) hK hQ (hY n j)
  have hRad n j := radialError_le (hDim j) hK hQ (hY n j)
  have hB n j : normDefect Q (Y n j)/Q^2≤(1+|Q|)^2/Q^2 :=
    div_le_div_of_nonneg_right (defect_bound (hDim j) hK (hY n j) Q) (sq_nonneg _)
  have hD : Tendsto (fun v : ℕ×ℕ => normDefect Q (Y v.1 v.2)/Q^2)
      ((atTop : Filter ℕ).curry (atTop : Filter ℕ)) (𝓝 0) := by
    simpa only [zero_div] using hDefect.div_const (Q^2)
  constructor
  · apply ordered_limsup_tendsto (M:=(1+|Q|)^2/Q^2)
      (fun n j => normalizationError_nonneg Q (Y n j))
      (fun n j => (hNorm n j).trans (hB n j))
    exact squeeze_zero (fun v => normalizationError_nonneg Q (Y v.1 v.2))
      (fun v => hNorm v.1 v.2) hD
  · apply ordered_limsup_tendsto (M:=(1+|Q|)^2/Q^2)
      (fun n j => radialError_nonneg Q (Y n j))
      (fun n j => (hRad n j).trans (hB n j))
    exact squeeze_zero (fun v => radialError_nonneg Q (Y v.1 v.2))
      (fun v => hRad v.1 v.2) hD

/-- Source10.4's two printed replacement clauses for the genuine
whole-path fork, from actual independent-future concentration and the
preceding CK mean/Fisher inputs, without a normalization error premise. -/
theorem actual_normalization_errors {p K : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j) (hTop : Tendsto dim atTop atTop)
    (E : ∀j,FisherDensity (dim j) p β)
    (hLaw : ∀j,WaitingDensityLaw β (dim j+1) (modelRadius_pos (dim j)) (E j))
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|(E j).full w-f w|) atTop (𝓝 0))
    (hK : 0<K) (L : ℝ≥0) :
    Tendsto (fun n => limsup (fun j => normalizationError (forkNorm c K L)
      (branch (N:=dim j) (p:=p) (K:=K) β ((T n).toNNReal+L) (T n).toNNReal)) atTop)
        atTop (𝓝 0) ∧
      Tendsto (fun n => limsup (fun j => radialError (forkNorm c K L)
        (branch (N:=dim j) (p:=p) (K:=K) β ((T n).toNNReal+L) (T n).toNNReal)) atTop)
          atTop (𝓝 0) := by
  apply normalization_errors_ordered (fun j => by have hd:=hDim j;omega) hK
    (forkNorm_pos_of_profile H.profile hK L)
    (fun n j => fork_joint_law β ((T n).toNNReal+L) (T n).toNNReal)
  simp_rw [defect_transfer]
  simpa only [forkNorm] using
    actual_center_defect_tendsto H hT dim hDim hTop E hLaw hbridge hi hn hL1 hK L

end SphericalAging.PhysicalForkNormalizationLimits
