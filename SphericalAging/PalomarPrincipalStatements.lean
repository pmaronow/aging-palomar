module
public import SphericalAging.MainCubicGeometryTheorem
public import SphericalAging.CriticalEndpoint
public import SphericalAging.CausalRowSup
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Public pure CK principal statements

The definitions collect Theorem 1.1, the all-p Theorem 11.4, the inclusive
cubic Theorem 1.3 with every printed last-crossing consequence, and Theorem
1.5 with one common stationary profile. They contain no stochastic or
Fisher objects. Actual existence and all upstream interfaces are discharged
in PalomarPrincipalTheorems. This pure interface does not by itself certify
the separate physical-response and Fisher-production statements 1.2 and 1.4.
-/
public section
noncomputable section
open Set Filter MeasureTheory Asymptotics
open scoped Topology ENNReal Asymptotics
namespace SphericalAging.PalomarPrincipalStatements
open CKSpecification PlateauAlgebra AllTemperatureTheorem StationaryFamilySelection
open MainCubicGeometryTheorem

@[expose] def AgingConclusion (p : ℕ) (β : ℝ) (d : CKData)
    (ell q : ℝ) (c r : ℝ→ℝ) : Prop :=
    Tendsto d.multiplier atTop (𝓝 ell) ∧
    Tendsto (energy p β d) atTop (𝓝 ((ell-1)/((p:ℝ)*β))) ∧
    (∀A : ℝ,0≤A→Tendsto (windowSup d c r A) atTop (𝓝 0)) ∧
    c 0=1 ∧ r 0=1 ∧
    (∀t : ℝ,0≤t→HasDerivWithinAt c (-r t) (Ici 0) t) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) c (Ioi 0) ∧
    (∀n : ℕ,∀t : ℝ,0<t→0≤(-1:ℝ)^n*iteratedDeriv n c t) ∧
    (∀S : ℝ,0≤S→Tendsto (fun t : ℝ=>sSup
      ((fun s=>d.C t s+d.R t s) '' Icc 0 S)) atTop (𝓝 0)) ∧
    (transitionBetaSquared p≤β^2→
      0<q ∧ q=largerPlateau p β ∧ transitionPlateau p≤q ∧
      β^2*marginalityPolynomial p q=1 ∧ ell=multiplier p β q ∧
      (ell-1)/((p:ℝ)*β)=selectedEnergy p β q ∧
      Tendsto (fun τ : ℝ=>limUnder atTop (fun s : ℝ=>d.C (s+τ) s)) atTop (𝓝 q) ∧
      Tendsto (fun s : ℝ=>limUnder atTop (fun τ : ℝ=>d.C (s+τ) s)) atTop (𝓝 0))

@[expose] def ForwardConclusion (p : ℕ) (β : ℝ) (d : CKData)
    (c r : ℝ→ℝ) (q : ℝ) : Prop :=
    (∀L : ℝ,0<L→
      limsup (CausalRowSup.literalRowSup (correlationSlope p β d) L) atTop≤
        Real.sqrt (iteratedDeriv 2 c (2*L)) ∧
      Real.sqrt (iteratedDeriv 2 c (2*L))≤Real.sqrt (1-q)/(Real.exp 1*L)) ∧
    Tendsto (CausalRowSup.literalRowSup
      (fun t s => correlationSlope p β d t s+r (t-s)) 0) atTop (𝓝 0) ∧
    Tendsto (CausalRowSup.literalRowSup
      (fun t s => correlationSlope p β d t s+d.R t s) 0) atTop (𝓝 0) ∧
    (∀t : ℝ,0≤t→correlationSlope p β d t t= -1) ∧
    HasDerivWithinAt c (-1) (Ici 0) 0

@[expose] def TailConclusion (p : ℕ) (q : ℝ) (c r : ℝ→ℝ) : Prop :=
    ∃ a : ℝ,a∈Ioo 0 (1/2) ∧
      CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q ∧
      (∀ b : ℝ,b∈Ioo 0 (1/2) →
        CriticalEndpoint.exponentCoefficient b=CriticalEndpoint.relaxationParameter p q → b=a) ∧
      ∃Aβ : ℝ,0<Aβ ∧
        (fun t : ℝ=>c t-q) ~[atTop] (fun t : ℝ=>Aβ*t^(-a)) ∧
        (∀n : ℕ,1≤n→(fun t : ℝ=>(-1:ℝ)^n*iteratedDeriv n c t) ~[atTop]
          (fun t : ℝ=>(Aβ*(∏j∈Finset.range n,(a+(j:ℝ))))*t^(-(a+(n:ℝ))))) ∧
        (fun t : ℝ=>r t) ~[atTop] (fun t : ℝ=>(a*Aβ)*t^(-(a+1)))

/-- Inclusive cubic three-time conclusions on the same plateau. -/
@[expose] def CubicConclusion (p : ℕ) (β : ℝ) (d : CKData) (q : ℝ) : Prop :=
  p=3 → transitionBetaSquared 3≤β^2 →
    q=largerPlateau 3 β ∧ (1/2:ℝ)≤q ∧ PrintedProducts d q ∧
    ENNReal.ofReal (2*(1-q))≤liminf (fun t : ℝ=>ENNReal.ofReal (susceptibility d t 0)) atTop ∧
    OrderedAging d q ∧ LastCrossings d q ∧ (β^2=(4/3:ℝ)→q=1/2)

/-- A single set of CK/profile witnesses realizes every pure principal clause. -/
structure PrincipalConclusions (p : ℕ) (β : ℝ) (d : CKData)
    (ell q : ℝ) (c r : ℝ → ℝ) : Prop where
  plateau_bounds : 0≤q ∧ q<1
  plateau_limit : Tendsto c atTop (𝓝 q)
  correlation_continuous : ContinuousOn c (Ici 0)
  response_continuous : ContinuousOn r (Ici 0)
  profile_bounds : ∀t : ℝ,0≤t → 0≤r t ∧ r t≤c t ∧ c t≤1
  integrable_response : IntegrableOn r (Ioi 0)
  response_mass : (∫t in Ioi 0,r t)=1-q
  aging : AgingConclusion p β d ell q c r
  forward_derivative : ForwardConclusion p β d c r q
  cubic_geometry : CubicConclusion p β d q
  stationary_tail : transitionBetaSquared p≤β^2 → TailConclusion p q c r

end SphericalAging.PalomarPrincipalStatements
