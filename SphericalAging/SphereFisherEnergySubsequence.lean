module

public import SphericalAging.SphereOnSphereFisherMajorant
public import SphericalAging.SphereEnergyLimitTransfer

public section

/-! One genuine refinement of a preceding dimension sequence supplies both
the CK Fisher majorant and the energy increment control. Only actual finite
PDE data and preceding row-primitive/energy dimension limits enter. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereFisherEnergySubsequence
open Set Filter MeasureTheory FiniteModel SphereInitialLaw SphereFisherHelly
open SphereOnSphereCurrent SphereOnSphereFisherMajorant SphereFisherSubsequence
open SphereAnnealedCurrentFDT (rowPrimitive)
open SphereCKFisherMajorant (ckRowPrimitive stronglyMeasurable_of_exponential_clock)
open SphereEnergyLimitTransfer CKSpecification CKUniformLateEstimates StrongBackwardDefect
open SphereGoodEventFisherClock SphereBadEventFisherMass
open scoped Topology

theorem actual_Fisher_energy_refining_dimension_subsequence {p : ℕ} (hp : 2≤p)
    {β : ℝ} (hβ : 0≤β) {d : CKData} (h : CKEquations p β d)
    (dim : ℕ → ℕ) (hDim : ∀ n,2≤dim n) (hTop : Tendsto dim atTop atTop)
    (E : ∀ n,FisherDensity (dim n) p β) (M : ∀ n,SphereBackwardMean (dim n) p β)
    (hmeas : ∀ n t s,AEStronglyMeasurable
      (fun J => rowPrimitive ((E n).ρ J) ((M n).m J) t s) (disorderLaw (dim n) p))
    (hlimit : ∀ t s,0≤s → s≤t → Tendsto (fun n => annealedRowPrimitive (E n) (M n) t s)
      atTop (𝓝 (ckRowPrimitive d t s)))
    (hemeas : ∀ n t,AEStronglyMeasurable
      (fun J => SphereEnergyCurrent.energy (E n) J t) (disorderLaw (dim n) p))
    (helimit : ∀ t : ℝ,0≤t → Tendsto (fun n => annealedEnergy (E n) t) atTop
      (𝓝 (CKSpecification.energy p β d t))) :
    ∃ (φ : ℕ → ℕ) (aF : ℝ → ℝ),StrictMono φ ∧ (∀ s,0≤aF s) ∧
      FisherMajorant p β d aF ∧ (∫ s in Ioi 0,aF s)≤β^2/2 ∧
      (∀ s,ContinuousWithinAt aF (Ici s) s) ∧
      Antitone (fun s => Real.exp (-ceilingRate p β (cutoff p)*s)*aF s) ∧
      (∀ T : ℝ,Tendsto (fun n => ∫ s in Ioc 0 T,|(E (φ n)).full s-aF s|) atTop (𝓝 0)) ∧
      Tendsto (FisherLimitClockDecay.lateSup aF) atTop (𝓝 0) ∧
      IncrementControl aF (CKSpecification.energy p β d) ((p:ℝ)*cutoff p) := by
  obtain ⟨φ,aF,hφ,han,_,hac,hclock,hi,hmass,hFI⟩ :=
    actual_Fisher_subsequence_dimensions hp hβ dim hDim hTop E
  have hN n : 0<dim n := lt_of_lt_of_le (by norm_num : 0<2) (hDim n)
  have hmajor := fisherMajorant_of_actual_primitive_limits (by omega) hβ h
    (fun n => dim (φ n)) (fun n => hN (φ n)) (fun n => E (φ n)) (fun n => M (φ n))
    han hi (stronglyMeasurable_of_exponential_clock hclock) hac hFI (fun n => hmeas (φ n))
    (fun t s hs hst => (hlimit t s hs hst).comp hφ.tendsto_atTop)
  have hc : 0≤cutoff p := by
    unfold cutoff
    linarith [GaussianLandscape.landscapeThreshold_pos p]
  have hK : 0≤ceilingRate p β (cutoff p) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hβ) (sq_nonneg _)) hc
  have he := energyIncrementControl_of_actual_energy_limits (by omega : 1≤p) hβ
    (fun n => dim (φ n)) (fun n => hDim (φ n)) (hTop.comp hφ.tendsto_atTop)
    (fun n => E (φ n)) (fun n => hemeas (φ n)) hi hFI
    (fun t ht => (helimit t ht).comp hφ.tendsto_atTop)
  exact ⟨φ,aF,hφ,han,hmajor,hmass,hac,hclock,hFI,
    FisherLimitClockDecay.lateSup_tendsto_zero hK han hi (hclock.antitoneOn (Ici 0)),he⟩

end SphericalAging.SphereFisherEnergySubsequence
