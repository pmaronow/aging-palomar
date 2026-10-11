module

public import SphericalAging.ActualForkUniformL2

public section

/-! Whole local source10.3: both printed assertions for the literal
two-independent-future actual sphere SDE endpoints. The standing inputs
are the honest Fisher-density realization, its actual waiting law, the
preceding source5.3 Fisher extraction and source3.3 actual CK mean bridge. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace SphericalAging.ActualForkMomentTheorem
open Set Filter MeasureTheory FiniteModel CKSpecification StationaryClusterInputs
open ActualForkOverlapLaw ActualForkMomentComparison ActualForkL2Estimate ActualForkUniformL2
open ActualForkMeanBridge ActualSphereForkEndpoints ActualModelOverlapVariance SphereFisherHelly
open SphereBadEventFisherMass
open scoped Topology NNReal

@[expose] def FiniteComparison {N p : ℕ} (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (E : FisherDensity N p β) : Prop :=
  ∀(T a b : ℝ≥0) (k : ℕ),1≤k→
    |(∫z,(forkOverlap (p:=p) β R hR T a b z)^k ∂forkLaw N p)-
      ∫z,(actualOverlap (p:=p) β R hR (T+a) ((T+a)+(a+b)) z)^k ∂AnnealedModelLaw.law N p|≤
      (2*(k:ℝ)*Real.exp ((β:ℝ)*(p:ℝ)^2*cutoff p*((a:ℝ)+b)))*
        Real.sqrt ((a:ℝ)*(∫w in (T:ℝ)..((T:ℝ)+a),E.full w))+2*Real.exp (-(N:ℝ))

@[expose] def StationaryL2Conclusion {p : ℕ} (β : ℝ≥0) (dim : ℕ→ℕ)
    (R : ℕ→ℝ≥0) (hR : ∀j,0<(R j:ℝ)) (T : ℕ→ℝ) (c : ℝ→ℝ) : Prop :=
  ∀L : ℝ,0≤L→Tendsto (fun n => limsup (fun j => sSup ((fun z : ℝ×ℝ =>
    centeredError (N:=dim j) (p:=p) β (R j) (hR j) (T n) z.1 z.2 (c (z.1+z.2))) ''
      (Icc 0 L×ˢIcc 0 L))) atTop) atTop (𝓝 0)

/-- Both printed clauses. The finite bound is additionally proved for
every k≥1. No fork moment, concentration or comparison conclusion is an input. -/
theorem source10_3 {p : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j) (hTop : Tendsto dim atTop atTop)
    (R : ℕ→ℝ≥0) (hR : ∀j,0<(R j:ℝ)) (hNR : ∀j,(dim j:ℝ)<(R j:ℝ)^2)
    (E : ∀j,FisherDensity (dim j) p β)
    (hLaw : ∀j,WaitingDensityLaw β (R j) (hR j) (E j))
    (hbridge : MeanBridge (p:=p) β dim R hR d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|(E j).full w-f w|) atTop (𝓝 0)) :
    (∀j,FiniteComparison β (R j) (hR j) (E j)) ∧
      StationaryL2Conclusion (p:=p) β dim R hR T c := by
  constructor
  · intro j a b e k hk
    exact actual_fork_moment_comparison (hDim j) (by have hp:=h.spin_ge_three;omega)
      β (R j) (hR j) (hNR j) (E j) (hLaw j) a b e hk
  · intro L hL
    exact actual_fork_overlap_concentration H hT dim hDim hTop R hR hNR E hLaw hbridge hi hn hL1 hL

end SphericalAging.ActualForkMomentTheorem
