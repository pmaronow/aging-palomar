module

public import SphericalAging.SphereOnSphereCurrent
public import SphericalAging.SphereCKFisherMajorant
public import SphericalAging.SphereFisherSubsequence

public section

/-! Actual Fisher extraction and CK majorant transfer with the backward mean
PDE only on sphere points. Preceding primitive dimension limits remain explicit. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereOnSphereFisherMajorant
open Set Filter MeasureTheory FiniteModel SphereInitialLaw SphereFisherHelly
open SphereOnSphereCurrent SphereFisherSubsequence
open SphereAnnealedCurrentFDT (rowPrimitive)
open SphereCKFisherMajorant (ckRowPrimitive ckRowPrimitive_hasDerivAt stronglyMeasurable_of_exponential_clock)
open CKSpecification StrongBackwardDefect SphereGoodEventFisherClock SphereBadEventFisherMass
open scoped Topology

/-- Honest finite PDE data and actual row-primitive limits transfer the
constructed Fisher limit to the true CK earlier derivative. -/
theorem fisherMajorant_of_actual_primitive_limits {p : ℕ} (hp : 1≤p) {β : ℝ} (hβ : 0≤β)
    {d : CKData} (h : CKEquations p β d) (dim : ℕ → ℕ) (hDim : ∀ n,0<dim n)
    (E : ∀ n,FisherDensity (dim n) p β) (M : ∀ n,SphereBackwardMean (dim n) p β)
    {aF : ℝ → ℝ} (han : ∀ s,0≤aF s) (hi : IntegrableOn aF (Ioi 0))
    (ham : StronglyMeasurable aF) (hac : ∀ s,ContinuousWithinAt aF (Ici s) s)
    (hFI : ∀ T : ℝ,Tendsto (fun n => ∫ s in Ioc 0 T,|(E n).full s-aF s|) atTop (𝓝 0))
    (hmeas : ∀ n t s,AEStronglyMeasurable
      (fun J => rowPrimitive ((E n).ρ J) ((M n).m J) t s) (disorderLaw (dim n) p))
    (hlimit : ∀ t s,0≤s → s≤t → Tendsto (fun n => annealedRowPrimitive (E n) (M n) t s)
      atTop (𝓝 (ckRowPrimitive d t s))) : FisherMajorant p β d aF := by
  refine ⟨fun s _ => han s,hi,?_⟩
  intro t s hs hst
  exact FisherIntervalTransfer.derivative_square_le_of_finite_intervals hs.le hst (hlimit t)
    (fun n => ((E n).full_budget (hDim n) hp hβ).1) hi hFI ham (hac s)
    (ckRowPrimitive_hasDerivAt h hs hst)
    (fun n v hsv hvt => annealedRowPrimitive_increment_fisher_bound (hDim n) hp hβ (E n) (M n)
      hs.le hsv.le hvt (hmeas n t))

theorem actual_FisherMajorant_refining_dimension_subsequence {p : ℕ} (hp : 2≤p)
    {β : ℝ} (hβ : 0≤β) {d : CKData} (h : CKEquations p β d)
    (dim : ℕ → ℕ) (hDim : ∀ n,2≤dim n) (hTop : Tendsto dim atTop atTop)
    (E : ∀ n,FisherDensity (dim n) p β) (M : ∀ n,SphereBackwardMean (dim n) p β)
    (hmeas : ∀ n t s,AEStronglyMeasurable
      (fun J => rowPrimitive ((E n).ρ J) ((M n).m J) t s) (disorderLaw (dim n) p))
    (hlimit : ∀ t s,0≤s → s≤t → Tendsto (fun n => annealedRowPrimitive (E n) (M n) t s)
      atTop (𝓝 (ckRowPrimitive d t s))) :
    ∃ (φ : ℕ → ℕ) (aF : ℝ → ℝ),StrictMono φ ∧ FisherMajorant p β d aF ∧
      (∫ s in Ioi 0,aF s)≤β^2/2 ∧
      (∀ s,ContinuousWithinAt aF (Ici s) s) ∧
      Antitone (fun s => Real.exp (-ceilingRate p β (cutoff p)*s)*aF s) ∧
      (∀ T : ℝ,Tendsto (fun n => ∫ s in Ioc 0 T,|(E (φ n)).full s-aF s|) atTop (𝓝 0)) ∧
      Tendsto (FisherLimitClockDecay.lateSup aF) atTop (𝓝 0) := by
  obtain ⟨φ,aF,hφ,han,_,hac,hclock,hi,hmass,hFI⟩ :=
    actual_Fisher_subsequence_dimensions hp hβ dim hDim hTop E
  have hN n : 0<dim n := lt_of_lt_of_le (by norm_num : 0<2) (hDim n)
  have hmajor := fisherMajorant_of_actual_primitive_limits (by omega) hβ h
    (fun n => dim (φ n)) (fun n => hN (φ n)) (fun n => E (φ n)) (fun n => M (φ n))
    han hi (stronglyMeasurable_of_exponential_clock hclock) hac hFI (fun n => hmeas (φ n))
    (fun t s hs hst => (hlimit t s hs hst).comp hφ.tendsto_atTop)
  have hK : 0≤ceilingRate p β (cutoff p) := by
    have hc : 0≤cutoff p := by
      unfold cutoff
      linarith [GaussianLandscape.landscapeThreshold_pos p]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hβ) (sq_nonneg _)) hc
  exact ⟨φ,aF,hφ,hmajor,hmass,hac,hclock,hFI,
    FisherLimitClockDecay.lateSup_tendsto_zero hK han hi (hclock.antitoneOn (Ici 0))⟩

end SphericalAging.SphereOnSphereFisherMajorant
