module

public import SphericalAging.ActualSphereEnergyModelIdentification
public import SphericalAging.ActualCKMeanKernelConvergence
public import SphericalAging.GreenCovariance

public section

/-! Genuine canonical density energy converges to the manuscript's CK
energy, with no finite-dimensional convergence or calculus premises. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
namespace SphericalAging.ActualCKPrintedEnergyLimit
open CKSpecification GreenCovariance ActualCKMeanKernelConvergence
open CompactKernelMemoryLimit ActualCompactCKMemoryLimit ActualResponsePrimitiveInterchange
open ActualCKEnergyLimit ActualCKMultiplierResidual ActualSphereEnergyModelIdentification
open ActualSphereEnergyLimitTransfer AnnealedHamiltonianEnergyStein
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ}

@[expose] def correlationKernel (d : CKData) : Kernel := fun t s => clampedCorrelation d t s
@[expose] def responseKernel (d : CKData) : Kernel := fun t s => clampedResponse d t s

theorem correlationKernel_continuous {β : ℝ} {d : CKData} (hd : CKEquations p β d) :
    Continuous (Function.uncurry (correlationKernel d)) := by
  exact (clampedCorrelation_continuous hd).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

theorem responseKernel_continuous {β : ℝ} {d : CKData} (hd : CKEquations p β d) :
    Continuous (Function.uncurry (responseKernel d)) := by
  exact (clampedResponse_continuous hd).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

theorem kernel_energy_eq (β : ℝ≥0) (d : CKData) (hd : CKEquations p β d) (H : ℝ≥0) :
    (β:ℝ)*(p:ℝ)*correlationMemory (correlationKernel d) (responseKernel d) (p-1) 0 (H,H,H)=
      energy p β d H := by
  unfold energy memoryMass correlationMemory
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le H.coe_nonneg] at hu
  simp only [correlationKernel,responseKernel,pow_zero,mul_one]
  rw [Real.coe_toNNReal u hu.1,clampedCorrelation_eq hu.1 H.coe_nonneg,
    clampedResponse_eq hu.1 hu.2,hd.correlation_symmetric u H hu.1 H.coe_nonneg]

/-- Literal canonical full-model energy converges uniformly on compact
time intervals to exactly the printed CK energy. -/
theorem actual_meanEnergy_printed_uniform_limit (dim : ℕ→ℕ) (hD : ∀n,3≤dim n)
    (hTop : Tendsto dim atTop atTop) (hp : 3≤p) (β T : ℝ≥0) (hβ : 0<β)
    (d : CKData) (hd : CKEquations p β d) :
    TendstoUniformlyOn (fun n H => meanEnergy (dim n) p β H)
      (fun H : ℝ≥0 => energy p β d H) atTop (Iic T) := by
  have hm := actual_ck_means_uniform_limit dim hTop hp β hβ d hd T
  have hC : TendstoUniformlyOn (fun n => Function.uncurry (modelCorrelation (dim n) p β))
      (Function.uncurry (correlationKernel d)) atTop (square T) := by
    apply hm.1.congr_right
    intro z _
    exact (clampedCorrelation_eq z.1.coe_nonneg z.2.coe_nonneg).symm
  have hR : TendstoUniformlyOn (fun n => Function.uncurry (modelResponse (N:=dim n) (p:=p) β))
      (Function.uncurry (responseKernel d)) atTop (triangle T) := by
    apply hm.2.2.congr_right
    intro z hz
    exact (clampedResponse_eq z.2.coe_nonneg (show (z.2:ℝ)≤z.1 from hz.1)).symm
  have he := actual_energy_uniform_limit dim hD hTop (by omega : 2≤p) β T hC hR
    (correlationKernel_continuous hd) (responseKernel_continuous hd)
  exact he.congr_right (fun H _ => kernel_energy_eq β d hd H)

/-- The literal actual forward-density energy has the printed CK limit. -/
theorem actual_annealedEnergy_printed_uniform_limit (dim : ℕ→ℕ) (hD : ∀n,3≤dim n)
    (hTop : Tendsto dim atTop atTop) (hp : 3≤p) (β T : ℝ≥0) (hβ : 0<β)
    (d : CKData) (hd : CKEquations p β d) :
    TendstoUniformlyOn (fun n => fun H : ℝ≥0 => annealedEnergy (N:=dim n) (p:=p) β
      (dim n+1) (modelRadius_pos (dim n)) H)
      (fun H : ℝ≥0 => energy p β d H) atTop (Iic T) := by
  apply (actual_meanEnergy_printed_uniform_limit dim hD hTop hp β T hβ d hd).congr
  exact Eventually.of_forall (fun n H _ =>
    (annealedEnergy_eq_meanEnergy (by have := hD n;omega) (by omega) β H).symm)

/-- Pointwise real-time form for the actual Fisher increment transfer. -/
theorem actual_annealedEnergy_printed_tendsto (dim : ℕ→ℕ) (hD : ∀n,3≤dim n)
    (hTop : Tendsto dim atTop atTop) (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (d : CKData) (hd : CKEquations p β d) {t : ℝ} (ht : 0≤t) :
    Tendsto (fun n => annealedEnergy (N:=dim n) (p:=p) β
      (dim n+1) (modelRadius_pos (dim n)) t) atTop (𝓝 (energy p β d t)) := by
  simpa only [Real.coe_toNNReal t ht] using
    (actual_annealedEnergy_printed_uniform_limit dim hD hTop hp β t.toNNReal hβ d hd).tendsto_at
      (show t.toNNReal∈Iic t.toNNReal from (le_refl t.toNNReal))

end SphericalAging.ActualCKPrintedEnergyLimit
