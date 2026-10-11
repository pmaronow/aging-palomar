module

public import SphericalAging.ActualSphereOnlyForkUniformL2
public import SphericalAging.ActualSphereFisherTheorem
public import SphericalAging.ActualForkMomentTheorem

public section

/-! Whole local source10.3: both printed assertions for the literal
two-independent-future actual sphere SDE endpoints. The density and waiting law are constructed from the actual SDE. The final
theorem derives the required Fisher subsequence and CK mean bridge. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace SphericalAging.ActualSphereOnlyForkMomentTheorem
open Set Filter MeasureTheory FiniteModel CKSpecification StationaryClusterInputs
open ActualForkOverlapLaw ActualSphereOnlyForkMomentComparison ActualForkL2Estimate ActualSphereOnlyForkUniformL2
open ActualForkMeanBridge ActualSphereForkEndpoints ActualModelOverlapVariance SphereFisherHelly
open SphereBadEventFisherMass ActualSphereRestrictedFisherBudget StrongBackwardDefect
open ActualSphereFisherTheorem ActualSphereCKBridges AnnealedHamiltonianEnergyStein
open scoped Topology NNReal

@[expose] def FiniteComparison {N p : ℕ} (β R : ℝ≥0) (hR : 0<(R:ℝ))
    : Prop :=
  ∀(T a b : ℝ≥0) (k : ℕ),1≤k→
    |(∫z,(forkOverlap (p:=p) β R hR T a b z)^k ∂forkLaw N p)-
      ∫z,(actualOverlap (p:=p) β R hR (T+a) ((T+a)+(a+b)) z)^k ∂AnnealedModelLaw.law N p|≤
      (2*(k:ℝ)*Real.exp ((β:ℝ)*(p:ℝ)^2*cutoff p*((a:ℝ)+b)))*
        Real.sqrt ((a:ℝ)*(∫w in (T:ℝ)..((T:ℝ)+a),full (N:=N) (p:=p) β R hR w))+2*Real.exp (-(N:ℝ))

@[expose] abbrev StationaryL2Conclusion := @ActualForkMomentTheorem.StationaryL2Conclusion

/-- Both printed clauses. The finite bound is additionally proved for
every k≥1. No fork moment, concentration or comparison conclusion is an input. -/
theorem source10_3 {p : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j) (hTop : Tendsto dim atTop atTop)
    (R : ℕ→ℝ≥0) (hR : ∀j,0<(R j:ℝ)) (hNR : ∀j,(dim j:ℝ)<(R j:ℝ)^2)
    (hbridge : MeanBridge (p:=p) β dim R hR d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|full (N:=dim j) (p:=p) β (R j) (hR j) w-f w|) atTop (𝓝 0)) :
    (∀j,FiniteComparison (N:=dim j) (p:=p) β (R j) (hR j)) ∧
      StationaryL2Conclusion (p:=p) β dim R hR T c := by
  constructor
  · intro j a b e k hk
    exact actual_fork_moment_comparison (hDim j) (by have hp:=h.spin_ge_three;omega)
      β (R j) (hR j) (hNR j) a b e hk
  · intro L hL
    exact actual_fork_overlap_concentration H hT dim hDim hTop R hR hNR hbridge hi hn hL1 hL

/-- Source10.3 on the actual Fisher dimension subsequence specified in
source5.3. All actual density, waiting-law, mean-convergence and Fisher
extraction hypotheses are discharged internally. -/
theorem actual_source10_3 {p : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j) (hTop : Tendsto dim atTop atTop) :
    ∃ (φ : ℕ→ℕ) (aF : ℝ→ℝ),StrictMono φ ∧ (∀s,0≤aF s) ∧
      FisherMajorant p β d aF ∧
      (∀t : ℝ,Tendsto (fun j => ∫w in Ioc 0 t,
        |full (N:=dim (φ j)) (p:=p) β (dim (φ j)+1)
          (modelRadius_pos (dim (φ j))) w-aF w|) atTop (𝓝 0)) ∧
      (∀j,FiniteComparison (N:=dim (φ j)) (p:=p) β
        (dim (φ j)+1) (modelRadius_pos (dim (φ j)))) ∧
      StationaryL2Conclusion (p:=p) β (fun j => dim (φ j))
        (fun j => dim (φ j)+1) (fun j => modelRadius_pos (dim (φ j))) T c := by
  obtain ⟨φ,aF,hφ,han,hF,_hmass,_hac,_hclock,hFI,_hlate⟩ :=
    actual_FisherMajorant β h dim hDim hTop
  have htop : Tendsto (fun j => dim (φ j)) atTop atTop :=
    hTop.comp hφ.tendsto_atTop
  have hd2 (j : ℕ) : 2≤dim (φ j) := by have hh:=hDim (φ j);omega
  have hbridge := canonical_MeanBridge h.spin_ge_three β h.beta_pos d h
    (fun j => dim (φ j)) htop
  have hc := source10_3 H hT (fun j => dim (φ j)) hd2 htop
    (fun j => dim (φ j)+1) (fun j => modelRadius_pos (dim (φ j)))
    (fun j => modelRadius_sq (dim (φ j))) hbridge hF.integrable han hFI
  exact ⟨φ,aF,hφ,han,hF,hFI,hc⟩

end SphericalAging.ActualSphereOnlyForkMomentTheorem
