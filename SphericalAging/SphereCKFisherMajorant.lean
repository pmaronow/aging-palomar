module

public import SphericalAging.FisherIntervalTransfer
public import SphericalAging.SphereAnnealedCurrentFDT
public import SphericalAging.StrongBackwardDefect

public section

/-! Actual spherical forward/backward PDE currents produce the CK Fisher
majorant once the preceding source 5.1 row-primitive dimension limits are
realized. Those limits are stated for the literal constructed finite objects;
no CK Fisher domination premise is supplied. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereCKFisherMajorant
open Set Filter MeasureTheory FiniteModel SphereInitialLaw SphereFisherHelly
open SphereAnnealedCurrentFDT CKSpecification GreenCovariance EarlierCovariance
open StrongBackwardDefect SphereGoodEventFisherClock SphereBadEventFisherMass
open scoped Topology

@[expose] def ckRowPrimitive (d : CKData) (t s : ℝ) : ℝ :=
  d.C t s-d.C t 0-(∫ u in (0 : ℝ)..s,clampedResponse d t u)

theorem ckRowPrimitive_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {s t : ℝ} (hs : 0<s) (hst : s<t) :
    HasDerivAt (ckRowPrimitive d t) (backwardDefect p β d t s) s := by
  have hR : Continuous (fun u => clampedResponse d t u) :=
    (clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)
  have hd := (correlation_earlier_hasDerivAt h hs hst).sub_const (d.C t 0)
  have hp := intervalIntegral.integral_hasDerivAt_right (hR.intervalIntegrable 0 s)
    hR.stronglyMeasurable.stronglyMeasurableAtFilter hR.continuousAt
  rw [clampedResponse_eq hs.le hst.le] at hp
  exact hd.sub hp

theorem stronglyMeasurable_of_exponential_clock {a : ℝ → ℝ} {K : ℝ}
    (hc : Antitone (fun t => Real.exp (-K*t)*a t)) : StronglyMeasurable a := by
  have hExp : Continuous (fun t : ℝ => Real.exp (K*t)) := by fun_prop
  have he : (fun t => Real.exp (K*t)*(Real.exp (-K*t)*a t))=a := by
    funext t
    rw [← mul_assoc,← Real.exp_add]
    simp
  rw [← he]
  exact hExp.stronglyMeasurable.mul hc.measurable.stronglyMeasurable

/-- Honest finite PDE data and actual row-primitive limits transfer the
constructed Fisher limit to the true CK earlier derivative. -/
theorem fisherMajorant_of_actual_primitive_limits {p : ℕ} (hp : 1≤p) {β : ℝ} (hβ : 0≤β)
    {d : CKData} (h : CKEquations p β d) (dim : ℕ → ℕ) (hDim : ∀ n,0<dim n)
    (E : ∀ n,FisherDensity (dim n) p β) (M : ∀ n,BackwardMean (dim n) p β)
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

/-- Complete Fisher-majorant construction under explicit preceding source
5.1 primitive limits and honest positive smooth forward/backward PDE inputs.
The finite Fisher subsequence, CK domination, mass and uniform late tail are
all derived. Actual SDE density/mean regularity and the dimension limits remain
the explicitly stated upstream realization boundary. -/
theorem actual_FisherMajorant_from_PDE_and_primitive_limits {p : ℕ} (hp : 2≤p)
    {β : ℝ} (hβ : 0≤β) {d : CKData} (h : CKEquations p β d)
    (E : ∀ n,FisherDensity (n+2) p β) (M : ∀ n,BackwardMean (n+2) p β)
    (hmeas : ∀ n t s,AEStronglyMeasurable
      (fun J => rowPrimitive ((E n).ρ J) ((M n).m J) t s) (disorderLaw (n+2) p))
    (hlimit : ∀ t s,0≤s → s≤t → Tendsto (fun n => annealedRowPrimitive (E n) (M n) t s)
      atTop (𝓝 (ckRowPrimitive d t s))) :
    ∃ (φ : ℕ → ℕ) (aF : ℝ → ℝ),StrictMono φ ∧ FisherMajorant p β d aF ∧
      (∫ s in Ioi 0,aF s)≤β^2/2 ∧
      (∀ s,ContinuousWithinAt aF (Ici s) s) ∧
      Antitone (fun s => Real.exp (-ceilingRate p β (cutoff p)*s)*aF s) ∧
      (∀ T : ℝ,Tendsto (fun n => ∫ s in Ioc 0 T,|(E (φ n)).full s-aF s|) atTop (𝓝 0)) ∧
      Tendsto (FisherLimitClockDecay.lateSup aF) atTop (𝓝 0) := by
  obtain ⟨φ,aF,hφ,han,_,hac,hclock,hi,hmass,hFI⟩ := actual_Fisher_subsequence hp hβ E
  have hmajor := fisherMajorant_of_actual_primitive_limits (by omega) hβ h
    (fun n => φ n+2) (fun n => by omega) (fun n => E (φ n)) (fun n => M (φ n))
    han hi (stronglyMeasurable_of_exponential_clock hclock) hac hFI (fun n => hmeas (φ n))
    (fun t s hs hst => (hlimit t s hs hst).comp hφ.tendsto_atTop)
  have hK : 0≤ceilingRate p β (cutoff p) := by
    have hc : 0≤cutoff p := by
      unfold cutoff
      linarith [GaussianLandscape.landscapeThreshold_pos p]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hβ) (sq_nonneg _)) hc
  exact ⟨φ,aF,hφ,hmajor,hmass,hac,hclock,hFI,
    FisherLimitClockDecay.lateSup_tendsto_zero hK han hi (hclock.antitoneOn (Ici 0))⟩

end SphericalAging.SphereCKFisherMajorant
