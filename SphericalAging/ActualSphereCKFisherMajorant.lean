module

public import SphericalAging.ActualSphereRowPrimitiveLimit
public import SphericalAging.ActualSphereFisherCompactData

public section

/-! The CK Fisher majorant constructed from the literal spherical diffusion
and precisely the preceding source3.3 correlation/response primitive bridges.
The density, current, Fisher budget, clock and subsequence are all constructed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology
namespace SphericalAging.ActualSphereCKFisherMajorant
open FiniteModel CKSpecification StrongBackwardDefect SphereGoodEventFisherClock
open SphereFisherHelly SphereCKFisherMajorant ActualSphereRowPrimitiveLimit
open ActualSphereAnnealedFDT ActualSphereAnnealedFisherBudget ActualSphereGibbsDensity
open ActualSphereRestrictedFisherBudget ActualSphereFisherCompactData
open ActualForkMeanBridge ActualResponseWindowLimit SphereAnnealedFisherBudget
open AnnealedHamiltonianEnergyStein
open SphereBadEventFisherMass
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true

theorem fisherMajorant_of_actual_rowPrimitive_limits {p : ℕ} (hp : 1≤p) (β : ℝ≥0)
    {d : CKData} (h : CKEquations p β d)
    (dim : ℕ→ℕ) (hDim : ∀n,0<dim n) (R : ℕ→ℝ≥0)
    (hR : ∀n,0<(R n:ℝ)) (hNR : ∀n,(dim n:ℝ)<(R n:ℝ)^2)
    {aF : ℝ→ℝ} (han : ∀s,0≤aF s) (hi : IntegrableOn aF (Ioi 0))
    (ham : StronglyMeasurable aF) (hac : ∀s,ContinuousWithinAt aF (Ici s) s)
    (hFI : ∀T : ℝ,Tendsto (fun n => ∫s in Ioc 0 T,
      |full (N:=dim n) (p:=p) β (R n) (hR n) s-aF s|) atTop (𝓝 0))
    (hlimit : ∀t s,0≤s→s≤t→Tendsto (fun n => ActualSphereAnnealedFDT.annealedRowPrimitive
      (N:=dim n) (p:=p) β (R n) (hR n) t s) atTop (𝓝 (ckRowPrimitive d t s))) :
    FisherMajorant p β d aF := by
  refine ⟨fun s _ => han s,hi,?_⟩
  intro t s hs hst
  exact FisherIntervalTransfer.derivative_square_le_of_finite_intervals hs.le hst (hlimit t)
    (fun n => (actual_annealed_fisher_time_budget (hDim n) hp β (R n) (hR n) (hNR n)).1)
    hi hFI ham (hac s) (ckRowPrimitive_hasDerivAt h hs hst)
    (fun n v hsv hvt => actual_annealedRowPrimitive_increment_fisher_bound
      (hDim n) hp β (R n) (hR n) (hNR n) hs.le hsv.le hvt)

/-- The actual full-model Fisher limit, its mass and its uniform late tail
follow from the preceding source3.3 bridges. There are no density, PDE,
Fisher extraction, finite-row convergence or majorant premises. -/
theorem actual_FisherMajorant_of_source3_3 {p : ℕ} (hp : 2≤p) (β : ℝ≥0)
    {d : CKData} (h : CKEquations p β d) (dim : ℕ→ℕ)
    (hDim : ∀n,3≤dim n) (hdim : Tendsto dim atTop atTop)
    (hmean : MeanBridge (p:=p) β dim (fun n => dim n+1) (fun n => modelRadius_pos (dim n)) d)
    (hresponse : ResponsePrimitiveBridge hp β dim d) :
    ∃ (φ : ℕ→ℕ) (aF : ℝ→ℝ),StrictMono φ ∧ FisherMajorant p β d aF ∧
      (∫s in Ioi 0,aF s)≤(β:ℝ)^2/2 ∧
      (∀s,ContinuousWithinAt aF (Ici s) s) ∧
      Antitone (fun s => Real.exp (-ceilingRate p β (cutoff p)*s)*aF s) ∧
      (∀T : ℝ,Tendsto (fun n => ∫s in Ioc 0 T,
        |full (N:=dim (φ n)) (p:=p) β (dim (φ n)+1) (modelRadius_pos (dim (φ n))) s-aF s|)
        atTop (𝓝 0)) ∧
      Tendsto (FisherLimitClockDecay.lateSup aF) atTop (𝓝 0) := by
  obtain ⟨φ,aF,hφ,han,_,hac,hclock,hi,hmass,hFI⟩ :=
    ActualSphereFisherCompactData.actual_Fisher_subsequence p hp β dim (fun n => by have := hDim n;omega)
      hdim (fun n => dim n+1) (fun n => modelRadius_pos (dim n)) (fun n => modelRadius_sq (dim n))
  have hmajor := fisherMajorant_of_actual_rowPrimitive_limits (by omega) β h
    (fun n => dim (φ n)) (fun n => by have := hDim (φ n);omega)
    (fun n => dim (φ n)+1) (fun n => modelRadius_pos (dim (φ n)))
    (fun n => modelRadius_sq (dim (φ n))) han hi
    (stronglyMeasurable_of_exponential_clock hclock) hac hFI
    (fun t s hs hst => (actual_rowPrimitive_dimension_limit hp β dim hDim d h hmean hresponse hs hst).comp
      hφ.tendsto_atTop)
  have hK : 0≤ceilingRate p β (cutoff p) := by
    have hc : 0≤cutoff p := by
      unfold cutoff
      linarith [GaussianLandscape.landscapeThreshold_pos p]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) β.coe_nonneg) (sq_nonneg _)) hc
  exact ⟨φ,aF,hφ,hmajor,hmass,hac,hclock,hFI,
    FisherLimitClockDecay.lateSup_tendsto_zero hK han hi (hclock.antitoneOn (Ici 0))⟩

end SphericalAging.ActualSphereCKFisherMajorant
