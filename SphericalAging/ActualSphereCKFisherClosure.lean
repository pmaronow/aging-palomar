module

public import SphericalAging.ActualSphereFisherTheorem
public import SphericalAging.ActualSphereCKIncrementControls
public import SphericalAging.CKFisherEnergyIntegral
public import SphericalAging.SphereWaitingTheorem
public import SphericalAging.CKStationaryClusterExtraction

public section

/-! Actual-model closure of the Fisher, energy, waiting and stationary
compactness inputs. Every finite-model and dimension-limit premise has
been discharged from the constructed spherical diffusion. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
namespace SphericalAging.ActualSphereCKFisherClosure
open CKSpecification StrongBackwardDefect CKUniformLateEstimates SphereGoodEventFisherClock
open SphereBadEventFisherMass ActualSphereRestrictedFisherBudget ActualSphereFisherTheorem
open ActualSphereCKIncrementControls ActualSphereCKBridges AnnealedHamiltonianEnergyStein
open CKFisherEnergyIntegral SphereWaitingTheorem CKStationaryClusterExtraction
open StationaryMultiplierSelection
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency true

/-- All local limiting conclusions are realized by a Fisher function
extracted from the literal finite-dimensional spherical diffusion. -/
structure ActualFisherConclusions (p : ℕ) (β : ℝ≥0) (d : CKData) (aF : ℝ→ℝ) : Prop where
  nonneg : ∀s,0≤aF s
  majorant : FisherMajorant p β d aF
  mass : (∫s in Ioi 0,aF s)≤(β:ℝ)^2/2
  right_continuous : ∀s,ContinuousWithinAt aF (Ici s) s
  clock : Antitone (fun s => Real.exp (-ceilingRate p β (cutoff p)*s)*aF s)
  late_tail : Tendsto (FisherLimitClockDecay.lateSup aF) atTop (𝓝 0)
  local_conclusions : CKFisherLocalRegularity.LocalConclusions p β d aF (ceilingRate p β (cutoff p)) (cutoff p)
  energy_integral : ∀u v : ℝ,0≤u→u≤v→
    |energy p β d v-energy p β d u|≤(p:ℝ)*cutoff p*(∫s in u..v,Real.sqrt (aF s))
  waiting : LimitConclusions d aF (fun L => 1+Real.exp ((β:ℝ)*(p:ℝ)^2*cutoff p*L))

/-- The genuine Fisher subsequence supplies source5.3, source5.5 and
stationary cluster compactness together, with no analytic model inputs. -/
theorem actual_Fisher_closure {p : ℕ} (β : ℝ≥0) {d : CKData} (hd : CKEquations p β d)
    (dim : ℕ→ℕ) (hD : ∀n,3≤dim n) (hTop : Tendsto dim atTop atTop) :
    ClusterCompactness hd ∧ ∃ (φ : ℕ→ℕ) (aF : ℝ→ℝ),StrictMono φ ∧
      ActualFisherConclusions p β d aF ∧
      (∀T : ℝ,Tendsto (fun n => ∫s in Ioc 0 T,
        |full (N:=dim (φ n)) (p:=p) β (dim (φ n)+1) (modelRadius_pos (dim (φ n))) s-aF s|)
        atTop (𝓝 0)) := by
  obtain ⟨φ,aF,hφ,han,ha,hmass,hac,hclock,hFI,hlate⟩ := actual_FisherMajorant β hd dim hD hTop
  let D := dim∘φ
  have hD' n : 3≤D n := hD (φ n)
  have hTop' : Tendsto D atTop atTop := hTop.comp hφ.tendsto_atTop
  have he := actual_energyIncrementControl D hD' hTop' hd.spin_ge_three β hd.beta_pos d hd ha.integrable hFI
  have hm := canonical_MeanBridge hd.spin_ge_three β hd.beta_pos d hd D hTop'
  have hw := actual_waitingControl D hD' hTop' (by have := hd.spin_ge_three;omega) β d ha.integrable hFI hm
  have hA : 0≤cutoff p := by
    unfold cutoff
    linarith [GaussianLandscape.landscapeThreshold_pos p]
  have hK : 0≤ceilingRate p β (cutoff p) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) β.coe_nonneg) (sq_nonneg _)) hA
  obtain ⟨hlocal,henergy⟩ := CKFisherEnergyIntegral.source5_3 hd ha han hac hK hA hclock he
  have hwaiting := limit_conclusions_of_clock hw ha.integrable han (fun _ _ => by positivity) hac hK hclock
  have hc := clusterCompactness_of_Fisher_increment_controls hd ha han (fun _ _ => by positivity) hw
    (mul_nonneg (Nat.cast_nonneg p) hA) he
  exact ⟨hc,φ,aF,hφ,⟨han,ha,hmass,hac,hclock,hlate,hlocal,henergy,hwaiting⟩,hFI⟩

/-- No actual-model interface is needed to obtain stationary compactness
and a Fisher majorant for any printed CK solution. -/
theorem actual_stationary_compactness_and_Fisher {p : ℕ} {β : ℝ} {d : CKData}
    (hd : CKEquations p β d) :
    ClusterCompactness hd ∧ ∃aF : ℝ→ℝ,FisherMajorant p β d aF ∧
      (∀s,0≤aF s) ∧ (∫s in Ioi 0,aF s)≤β^2/2 := by
  let b : ℝ≥0 := ⟨β,hd.beta_pos.le⟩
  have hd' : CKEquations p b d := hd
  have hTop : Tendsto (fun n : ℕ => n+3) atTop atTop := tendsto_add_atTop_nat 3
  obtain ⟨hc,φ,aF,_,hF,_⟩ := actual_Fisher_closure b hd' (fun n => n+3) (fun n => by omega) hTop
  exact ⟨hc,aF,hF.majorant,hF.nonneg,hF.mass⟩

end SphericalAging.ActualSphereCKFisherClosure
