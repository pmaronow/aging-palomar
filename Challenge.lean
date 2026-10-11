module
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-! Independent Mathlib-only mathematical statement of every principal
manuscript conclusion on one common set of witnesses. Every shared
definition below is copied verbatim from the canonical interfaces. -/
public section
noncomputable section
open Set Filter MeasureTheory Asymptotics
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Asymptotics

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.CKSpecification

/-- Nonnegative causal times `(t,s)` with `0 ≤ s ≤ t`, the domain of the response equation. -/
@[expose] def causalTriangle : Set (ℝ × ℝ) := {z | 0 ≤ z.2 ∧ z.2 ≤ z.1}

/-- Pairs of nonnegative times, the domain of the symmetric correlation kernel. -/
@[expose] def timeQuadrant : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2}

/-- Real-line representatives of the correlation, response and spherical multiplier, used on the stated physical time domains; equations and bounds are separate. -/
structure CKData where
  C : ℝ → ℝ → ℝ
  R : ℝ → ℝ → ℝ
  multiplier : ℝ → ℝ

/-- First derivative of the pure interaction covariance `ξ(x)=x^p`, in the standing range `p ≥ 3`. -/
@[expose] def xiPrime (p : ℕ) (x : ℝ) : ℝ := (p : ℝ) * x ^ (p - 1)

/-- Second derivative of `ξ(x)=x^p`, in the standing range `p ≥ 3`. -/
@[expose] def xiDoublePrime (p : ℕ) (x : ℝ) : ℝ :=
  (p : ℝ) * ((p : ℝ) - 1) * x ^ (p - 2)

/-- The CK memory integral `∫₀ᵗ C(t,u)^(p-1) R(t,u) du`, used at nonnegative times. -/
@[expose] def memoryMass (p : ℕ) (d : CKData) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, d.C t u ^ (p - 1) * d.R t u

/-- Limiting energy per coordinate `β p ∫₀ᵗ C(t,u)^(p-1)R(t,u) du`, with the increasing-Hamiltonian sign convention. -/
@[expose] def energy (p : ℕ) (β : ℝ) (d : CKData) (t : ℝ) : ℝ :=
  β * p * memoryMass p d t

/-- Response to a unit additive drift force applied from `s` to `t`: the oriented integral `∫ₛᵗ R(t,u) du`; a unit Hamiltonian field gives an extra factor `β`. -/
@[expose] def susceptibility (d : CKData) (t s : ℝ) : ℝ :=
  ∫ u in s..t, d.R t u

/-- Right-hand side of the CK equation for the later-time derivative `∂ₜR(t,s)` on the causal domain. -/
@[expose] def responseSlope (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  -d.multiplier t * d.R t s + β ^ 2 *
    ∫ u in s..t, xiDoublePrime p (d.C t u) * d.R t u * d.R u s

/-- Right-hand side of the CK equation for `∂ₜC(t,s)`, including response-memory and correlation-memory terms. -/
@[expose] def correlationSlope (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  -d.multiplier t * d.C t s + β ^ 2 *
    (∫ u in (0 : ℝ)..t, xiDoublePrime p (d.C t u) * d.R t u * d.C u s) +
    β ^ 2 * (∫ u in (0 : ℝ)..s, xiPrime p (d.C t u) * d.R s u)

/-- The continuous pure-spin CK system at `p ≥ 3`, `β > 0`, with diagonal values one and causal derivative equations.
Physical positivity, bounds and positive semidefiniteness are separate conclusions; negative-time values are ambient extensions. -/
structure CKEquations (p : ℕ) (β : ℝ) (d : CKData) : Prop where
  spin_ge_three : 3 ≤ p
  beta_pos : 0 < β
  correlation_continuous : ContinuousOn (Function.uncurry d.C) timeQuadrant
  response_continuous : ContinuousOn (Function.uncurry d.R) causalTriangle
  multiplier_continuous : ContinuousOn d.multiplier (Ici 0)
  correlation_symmetric : ∀ t s, 0 ≤ t → 0 ≤ s → d.C t s = d.C s t
  correlation_diagonal : ∀ t, 0 ≤ t → d.C t t = 1
  response_diagonal : ∀ t, 0 ≤ t → d.R t t = 1
  multiplier_eq : ∀ t, 0 ≤ t →
    d.multiplier t = 1 + β ^ 2 * (p : ℝ) ^ 2 * memoryMass p d t
  response_derivative : ∀ t s, 0 ≤ s → s ≤ t →
    HasDerivWithinAt (fun u => d.R u s) (responseSlope p β d t s) (Ici s) t
  correlation_derivative : ∀ t s, 0 ≤ s → s ≤ t →
    HasDerivWithinAt (fun u => d.C u s) (correlationSlope p β d t s) (Ici s) t
  response_slope_continuous : ContinuousOn
    (fun z : ℝ × ℝ => responseSlope p β d z.1 z.2) causalTriangle
  correlation_slope_continuous : ContinuousOn
    (fun z : ℝ × ℝ => correlationSlope p β d z.1 z.2) causalTriangle

/-- Correlation values lie in `[0,1]` at nonnegative times, and the causal response is nonnegative. -/
@[expose] def PhysicalBounds (d : CKData) : Prop :=
  (∀ t s, 0 ≤ t → 0 ≤ s → 0 ≤ d.C t s ∧ d.C t s ≤ 1) ∧
  (∀ t s, 0 ≤ s → s ≤ t → 0 ≤ d.R t s)

/-- Every finite correlation matrix at nonnegative observation times is positive semidefinite, tested against real coefficients. -/
@[expose] def PositiveSemidefiniteCorrelation (d : CKData) : Prop :=
  ∀ (n : ℕ) (t a : Fin n → ℝ), (∀ i, 0 ≤ t i) →
    0 ≤ ∑ i, ∑ j, a i * a j * d.C (t i) (t j)

end SphericalAging.CKSpecification

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.PlateauAlgebra

/-- Plateau factor `p(p-1)q^(p-2)(1-q)^2`; marginality means that `β²` times this factor equals one. -/
@[expose] def marginalityPolynomial (p : ℕ) (q : ℝ) : ℝ :=
  (p : ℝ) * ((p : ℝ) - 1) * q ^ (p - 2) * (1 - q) ^ 2

/-- Stationary spherical multiplier determined by plateau `q`, equal to `1/(1-q)+β²p(1-q^(p-1))`; used with `q < 1`. -/
@[expose] def multiplier (p : ℕ) (β q : ℝ) : ℝ :=
  1 / (1 - q) + β ^ 2 * p * (1 - q ^ (p - 1))

/-- Explicit marginal-plateau energy `β[1+(p-2)q^(p-1)-(p-1)q^p]` in the increasing-Hamiltonian convention. -/
@[expose] def selectedEnergy (p : ℕ) (β q : ℝ) : ℝ :=
  β * (1 + ((p : ℝ) - 2) * q ^ (p - 1) - ((p : ℝ) - 1) * q ^ p)

/-- Plateau `(p-2)/p` where the marginality polynomial attains its maximum in the standing range `p ≥ 3`. -/
@[expose] def spinodalPlateau (p : ℕ) : ℝ := ((p : ℝ) - 2) / p

/-- Dynamical-transition plateau `(p-2)/(p-1)` for the pure spherical model with `p ≥ 3`. -/
@[expose] def transitionPlateau (p : ℕ) : ℝ := ((p : ℝ) - 2) / ((p : ℝ) - 1)

/-- Squared dynamical transition inverse temperature `(p-1)^(p-1)/[p(p-2)^(p-2)]`, for `p ≥ 3`. -/
@[expose] def transitionBetaSquared (p : ℕ) : ℝ :=
  ((p : ℝ) - 1) ^ (p - 1) / ((p : ℝ) * ((p : ℝ) - 2) ^ (p - 2))

end SphericalAging.PlateauAlgebra

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.AllTemperatureTheorem
open PlateauAlgebra

/-- Choose a marginality root on the upper branch `[(p-2)/p,1)` when one exists; otherwise return zero.
In the standing range `p ≥ 3`, `β > 0`, the advertised sector `β² ≥ transitionBetaSquared p` supplies the unique upper-branch root. -/
@[expose] def largerPlateau (p : ℕ) (β : ℝ) : ℝ := by
  classical
  exact if H : ∃q : ℝ,q∈Ico (spinodalPlateau p) 1 ∧ β^2*marginalityPolynomial p q=1
    then Classical.choose H else 0

end SphericalAging.AllTemperatureTheorem

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.PrefixRectangleStability

/-- Compact nonnegative observation window `{(t,s) : 0 ≤ s ≤ t ≤ A}`. -/
@[expose] def triangle (A : ℝ) : Set (ℝ × ℝ) := {z | z.1 ∈ Icc 0 A ∧ z.2 ∈ Icc 0 z.1}

end SphericalAging.PrefixRectangleStability

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.StationaryFamilySelection
open CKSpecification PrefixRectangleStability

/-- Sum of correlation and response errors between a time-translated CK window and profiles depending only on the lag. -/
@[expose] def windowError (d : CKData) (c r : ℝ → ℝ) (T : ℝ) (z : ℝ×ℝ) : ℝ :=
  |d.C (T+z.1) (T+z.2)-c (z.1-z.2)|+
    |d.R (T+z.1) (T+z.2)-r (z.1-z.2)|

/-- Real supremum of the combined profile error on the compact causal window; convergence is asserted for `A ≥ 0`. -/
@[expose] def windowSup (d : CKData) (c r : ℝ → ℝ) (A T : ℝ) : ℝ :=
  sSup (windowError d c r T '' triangle A)

end SphericalAging.StationaryFamilySelection

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.CausalRowSup

/-- Real supremum of `|f(t,s)|` over `0 ≤ s ≤ t-L`, measuring an entire earlier-time row.
For fixed nonnegative lag cutoff, sufficiently late times make the interval nonempty; real suprema are totalized outside bounded cases. -/
@[expose] def literalRowSup (f : ℝ→ℝ→ℝ) (L t : ℝ) : ℝ :=
  sSup ((fun s => |f t s|) '' Icc 0 (t-L))

end SphericalAging.CausalRowSup

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.LastCrossing
open CKSpecification

/-- Absolute times at or after `s` when the correlation with the state at `s` is at least the chosen level. -/
@[expose] def crossingSet (d : CKData) (level s : ℝ) : Set ℝ :=
  {t | s≤t ∧ level≤d.C t s}

/-- Supremum of the level crossing set: an absolute last crossing time, allowing earlier returns.
The selected cubic sector including the transition gives nonempty bounded crossing sets and attained final crossings for `s ≥ 0`, level in `(0,q)`; real suprema are totalized elsewhere. -/
@[expose] def lastCrossing (d : CKData) (level s : ℝ) : ℝ := sSup (crossingSet d level s)

end SphericalAging.LastCrossing

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.LastCrossingChain
open CKSpecification LastCrossing

/-- Iterate absolute last-crossing times in list order, starting at `s`; the empty list leaves the starting time unchanged. -/
@[expose] def crossingChain (d : CKData) : List ℝ→ℝ→ℝ
  | [],s => s
  | level::levels,s => crossingChain d levels (lastCrossing d level s)

end SphericalAging.LastCrossingChain

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.MainCubicGeometryTheorem
open CKSpecification LastCrossing LastCrossingChain

/-- Three cyclic asymptotic product lower bounds for every ordered triple with diverging earliest time and adjacent gaps; individual correlations need not converge. -/
@[expose]  def PrintedProducts (d : CKData) (q : ℝ) : Prop :=
  ∀u s t : ℕ→ℝ,(∀n,u n<s n ∧ s n<t n) →
    Tendsto u atTop atTop → Tendsto (fun n => s n-u n) atTop atTop →
    Tendsto (fun n => t n-s n) atTop atTop →
    0≤liminf (fun n => q*d.C (t n) (u n)-d.C (t n) (s n)*d.C (s n) (u n)) atTop ∧
    0≤liminf (fun n => q*d.C (t n) (s n)-d.C (t n) (u n)*d.C (s n) (u n)) atTop ∧
    0≤liminf (fun n => q*d.C (s n) (u n)-d.C (t n) (s n)*d.C (t n) (u n)) atTop

/-- Waiting-time-first and lag-first ordered limits give respectively `q` and zero, written with Lean's totalized `limUnder`.
The complete conclusions also establish the inner limits through window convergence and forgetting. -/
@[expose]  def OrderedAging (d : CKData) (q : ℝ) : Prop :=
  Tendsto (fun τ : ℝ => limUnder atTop (fun s : ℝ => d.C (s+τ) s)) atTop (𝓝 q) ∧
  Tendsto (fun s : ℝ => limUnder atTop (fun τ : ℝ => d.C (s+τ) s)) atTop (𝓝 0)

/-- Existence and divergence of last crossings below `q`, together with composition and iterated-correlation lower bounds. -/
@[expose]  def LastCrossings (d : CKData) (q : ℝ) : Prop :=
  (∀level∈Ioo 0 q,∀s : ℝ,0≤s →
    s≤lastCrossing d level s ∧ d.C (lastCrossing d level s) s=level) ∧
  (∀level∈Ioo 0 q,Tendsto (fun s => lastCrossing d level s-s) atTop atTop) ∧
  (∀c₀ c₁ c₂ : ℝ,0<c₀ → c₁∈Ioo 0 q → c₂∈Ioo 0 q → c₀<c₁*c₂/q →
    ∀ᶠs : ℝ in atTop,lastCrossing d c₂ (lastCrossing d c₁ s)≤lastCrossing d c₀ s) ∧
  (∀levels : List ℝ,(∀level∈levels,level∈Ioo 0 q) →
    q^((1:ℤ)-(levels.length:ℤ))*levels.prod≤liminf (fun s => d.C (crossingChain d levels s) s) atTop)

end SphericalAging.MainCubicGeometryTheorem

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.CriticalEndpoint

/-- The pure-spin dynamical-transition plateau `(p-2)/(p-1)`, used with `p ≥ 3`. -/
@[expose] def dynamicalPlateau (p : ℕ) : ℝ := ((p : ℝ) - 2) / ((p : ℝ) - 1)

/-- Mode-coupling exponent parameter `(p-2)(1-q)/(2q)`, used in the positive-plateau sector. -/
@[expose] def relaxationParameter (p : ℕ) (q : ℝ) : ℝ :=
  ((p : ℝ) - 2) * (1 - q) / (2 * q)

/-- Gamma-function ratio `Γ(1-a)^2/Γ(1-2a)` in the stationary power-law exponent equation; conclusions restrict `0 < a < 1/2`. -/
@[expose] noncomputable def exponentCoefficient (a : ℝ) : ℝ :=
  Real.Gamma (1 - a) ^ 2 / Real.Gamma (1 - 2 * a)

end SphericalAging.CriticalEndpoint

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.PalomarPrincipalStatements
open CKSpecification PlateauAlgebra AllTemperatureTheorem StationaryFamilySelection
open MainCubicGeometryTheorem

/-- Energy and stationary-window convergence, complete monotonicity, and forgetting every bounded earlier-time window.
At or beyond the dynamical transition it also identifies the positive marginal plateau and the two noncommuting ordered limits. -/
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

/-- For every pure integer `p ≥ 3`, `β > 0`, later-time derivative bounds away from the diagonal and uniform later-time FDT over all earlier times.
The causal diagonal derivative, holding the earlier time fixed, is minus one; this does not differentiate `t ↦ C(t,t)`. -/
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

/-- Stationary-lag power law after the waiting-time limit, with a unique exponent in `(0,1/2)`, positive finite amplitude and each fixed derivative order.
The response has the corresponding derivative asymptotic; this exponent does not describe an aging clock. -/
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

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.CKSpecification

end SphericalAging.CKSpecification

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.PlateauAlgebra

end SphericalAging.PlateauAlgebra

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.AllTemperatureTheorem
open PlateauAlgebra

end SphericalAging.AllTemperatureTheorem

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.PrefixRectangleStability

end SphericalAging.PrefixRectangleStability

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.StationaryFamilySelection
open CKSpecification PrefixRectangleStability

end SphericalAging.StationaryFamilySelection

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.PalomarPrincipalStatements
open CKSpecification PlateauAlgebra AllTemperatureTheorem StationaryFamilySelection

end SphericalAging.PalomarPrincipalStatements

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.FiniteModel
open ProbabilityTheory

/-- The Euclidean configuration space `ℝ^N` with its usual inner product. -/
@[expose] abbrev Vector (N : ℕ) := EuclideanSpace ℝ (Fin N)

/-- Ordered interaction indices of length `p`; repetitions are included. -/
@[expose] abbrev TensorIndex (N p : ℕ) := Fin p → Fin N

/-- A real coupling for each ordered interaction index, with its independent Gaussian law specified separately. -/
@[expose] abbrev Disorder (N p : ℕ) := TensorIndex N p → ℝ

/-- Product law of independent standard Gaussian couplings on all ordered interaction indices. -/
@[expose] def disorderLaw (N p : ℕ) : Measure (Disorder N p) :=
  Measure.pi (fun _ : TensorIndex N p => gaussianReal 0 1)

/-- Coordinate monomial `∏ₖ x_{Iₖ}` corresponding to one ordered interaction index. -/
@[expose] def tensorMonomial {N p : ℕ} (x : Vector N) (I : TensorIndex N p) : ℝ :=
  ∏ k : Fin p, x (I k)

/-- Hamiltonian prefactor `N^(-(p-1)/2)`, used for positive dimensions and `p ≥ 3`. -/
@[expose] def normalization (N p : ℕ) : ℝ :=
  (N : ℝ) ^ (-((p - 1 : ℕ) : ℝ) / 2)

/-- Pure Gaussian spherical Hamiltonian with ordered couplings and normalization giving covariance `N(x·y/N)^p` for `N > 0`. -/
@[expose] def Hamiltonian (N p : ℕ) (J : Disorder N p) (x : Vector N) : ℝ :=
  normalization N p * ∑ I : TensorIndex N p, J I * tensorMonomial x I

end SphericalAging.FiniteModel

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.SphereInitialLaw
open FiniteModel ProbabilityTheory

/-- Standard Gaussian probability measure on the Euclidean configuration space. -/
@[expose] def gaussianLaw (N : ℕ) : Measure (Vector N) := stdGaussian (Vector N)

/-- Radially project a nonzero vector onto the sphere of radius `√N`; Lean's totalized division maps zero to zero. -/
@[expose] def normalize (N : ℕ) (x : Vector N) : Vector N := (Real.sqrt N / ‖x‖) • x

/-- Uniform spherical initial law, realized by radial normalization of a standard Gaussian for positive dimensions. -/
@[expose] def sphereLaw (N : ℕ) : Measure (Vector N) := (gaussianLaw N).map (normalize N)

end SphericalAging.SphereInitialLaw

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.HardSphereDynamics

/-- Euclidean state space of the hard-spherical diffusion, equal to `ℝ^N`. -/
@[expose] abbrev State (N : ℕ) := EuclideanSpace ℝ (Fin N)

/-- Signed squared-radius error `‖x‖²-N` from the hard spherical constraint. -/
@[expose] def radiusDefect {N : ℕ} (x : State N) : ℝ := ⟪x, x⟫_ℝ - N

/-- The hard constraint `‖x‖²=N`; density and forward equations below are asserted on this sphere. -/
@[expose] def OnSphere {N : ℕ} (x : State N) : Prop := ⟪x, x⟫_ℝ = N

/-- Orthogonal projection onto the tangent space at a sphere point: `v-(x·v/N)x`, for `N > 0`. -/
@[expose] def projection {N : ℕ} (x v : State N) : State N :=
  v - (⟪x, v⟫_ℝ / N) • x

/-- Standard coordinate unit vector of the Euclidean state space. -/
@[expose] def basisVector {N : ℕ} (i : Fin N) : State N := EuclideanSpace.single i 1

end SphericalAging.HardSphereDynamics

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.SphericalIntegrationByParts
open FiniteModel

/-- Continuous real linear operators on the Euclidean configuration space. -/
@[expose] abbrev Operator (N : ℕ) := Vector N →L[ℝ] Vector N

local instance {N : ℕ} : NormedAlgebra ℚ (Operator N) :=
  NormedAlgebra.restrictScalars ℚ ℝ (Operator N)

/-- Directional derivative of `f` along the linear vector field `x ↦ A x`, expressed using the Fréchet derivative. -/
@[expose] def lieDerivative {N : ℕ} (A : Operator N) (f : Vector N → ℝ) (x : Vector N) :=
  fderiv ℝ f x (A x)

end SphericalAging.SphericalIntegrationByParts

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.SphereGibbsEntropy
open FiniteModel SphereInitialLaw

/-- Gibbs partition function `∫ exp(βH) dσ` relative to the uniform spherical law. -/
@[expose] def partitionFunction (N p : ℕ) (β : ℝ) (J : Disorder N p) : ℝ :=
  ∫ x : Vector N,Real.exp (β*Hamiltonian N p J x) ∂sphereLaw N

end SphericalAging.SphereGibbsEntropy

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.SphereEntropyDissipation
open FiniteModel SphereInitialLaw SphereGibbsEntropy SphericalIntegrationByParts

/-- Logarithm of the density relative to the Gibbs law: `log ρ-βH+log Z`, used where `ρ` is positive on the sphere. -/
@[expose] def relativeLog {N p : ℕ} (β : ℝ) (J : Disorder N p) (ρ : Vector N → ℝ) (x : Vector N) : ℝ :=
  Real.log (ρ x)-β*Hamiltonian N p J x+Real.log (partitionFunction N p β J)

/-- Density flux along a linear field: its directional derivative minus `βρ` times the directional derivative of the Hamiltonian. -/
@[expose] def rotationFlux {N p : ℕ} (β : ℝ) (J : Disorder N p) (A : Operator N)
    (ρ : Vector N → ℝ) (x : Vector N) : ℝ :=
  lieDerivative A ρ x-β*ρ x*lieDerivative A (Hamiltonian N p J) x

/-- Sum of directional derivatives of rotation fluxes, with diffusivity factor `κ`: the rotation-form Kolmogorov forward operator. -/
@[expose] def forwardDensitySlope {N p : ℕ} {ι : Type*} [Fintype ι] (κ β : ℝ) (J : Disorder N p)
    (A : ι → Operator N) (ρ : Vector N → ℝ) (x : Vector N) : ℝ :=
  κ*∑ i,lieDerivative (A i) (rotationFlux β J (A i) ρ) x

end SphericalAging.SphereEntropyDissipation

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.SphereRotationGeometry
open FiniteModel SphereInitialLaw HardSphereDynamics SphericalIntegrationByParts SphereEntropyDissipation

/-- Coordinate rotation generator `Eᵢⱼ-Eⱼᵢ`, a skew-adjoint linear operator tangent to the sphere. -/
@[expose] def coordinateRotation {N : ℕ} (i j : Fin N) : Operator N :=
  InnerProductSpace.rankOne ℝ (basisVector i) (basisVector j)-
    InnerProductSpace.rankOne ℝ (basisVector j) (basisVector i)

/-- Tangent gradient of the log density relative to the Gibbs law, obtained by projecting its ambient gradient. -/
@[expose] def tangentScore {N p : ℕ} (β : ℝ) (J : Disorder N p) (ρ : Vector N → ℝ) (x : Vector N) :=
  projection x (gradient (relativeLog β J ρ) x)

/-- Relative spherical Fisher information: the integral of density times squared tangent score against the uniform sphere law. -/
@[expose] def fisherInformation {N p : ℕ} (β : ℝ) (J : Disorder N p) (ρ : Vector N → ℝ) : ℝ :=
  ∫ x : Vector N,ρ x*‖tangentScore β J ρ x‖^2 ∂sphereLaw N

end SphericalAging.SphereRotationGeometry

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.SphereCanonicalEntropy
open FiniteModel SphericalIntegrationByParts SphereEntropyDissipation SphereRotationGeometry

/-- Kolmogorov forward operator for generator `Δ_S+β∇_S H·∇_S`, using all coordinate rotations with factor `1/(2N)`. -/
@[expose] def sphericalForwardDensitySlope {N p : ℕ} (β : ℝ) (J : Disorder N p)
    (ρ : Vector N → ℝ) :=
  forwardDensitySlope (1/(2*(N : ℝ))) β J
    (fun ij : Fin N × Fin N => coordinateRotation ij.1 ij.2) ρ

end SphericalAging.SphereCanonicalEntropy

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.SphereAnnealedFisherBudget
open FiniteModel SphereRotationGeometry

/-- Spherical Fisher information averaged over Gaussian disorder and divided by the dimension, evaluated at time `t`. -/
@[expose] def annealedFisher {N p : ℕ} (β : ℝ) (ρ : Disorder N p → ℝ → Vector N → ℝ) (t : ℝ) : ℝ :=
  (∫ J : Disorder N p,fisherInformation β J (ρ J t) ∂disorderLaw N p)/(N : ℝ)

end SphericalAging.SphereAnnealedFisherBudget

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.GreenCovariance
open CKSpecification

/-- Extend the causal response by replacing the earlier time with `max(0,u)` and the later time with `max(t,0,u)`. -/
@[expose] def clampedResponse (d : CKData) (t u : ℝ) : ℝ :=
  d.R (max t (max 0 u)) (max 0 u)

/-- Extend the nonnegative-time correlation by clamping each time at zero. -/
@[expose] def clampedCorrelation (d : CKData) (t s : ℝ) : ℝ :=
  d.C (max 0 t) (max 0 s)

/-- Clamped CK memory kernel `β²ξ''(C)R`, equal to the physical kernel at nonnegative causal times. -/
@[expose] def clampedMemory (p : ℕ) (β : ℝ) (d : CKData) (t u : ℝ) : ℝ :=
  β ^ 2 * xiDoublePrime p (clampedCorrelation d t u) * clampedResponse d t u

end SphericalAging.GreenCovariance

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.BackwardResponse
open CKSpecification

/-- Extend the spherical multiplier to all real times by clamping its argument at zero. -/
@[expose] def clampedMultiplier (d : CKData) (t : ℝ) : ℝ := d.multiplier (max 0 t)

end SphericalAging.BackwardResponse

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.EarlierCovariance
open CKSpecification GreenCovariance BackwardResponse

/-- Response-propagated colored-noise term `∫₀ᵗ R(t,u) C(u,s)^(p-1) du`, using the clamped extensions. -/
@[expose] def coloredMemory (p : ℕ) (d : CKData) (t s : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, clampedResponse d t u*clampedCorrelation d u s^(p-1)

/-- White-noise and colored-noise forcing contribution `2R(t,s)+β²p∫₀ᵗR(t,u)C(u,s)^(p-1)du`. -/
@[expose] def earlierForcing (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  2*clampedResponse d t s+β^2*(p : ℝ)*coloredMemory p d t s

/-- Right-hand side giving the earlier-time correlation derivative `∂ₛC(t,s)` on `0 < s < t`. -/
@[expose] def earlierSlope (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  -d.multiplier s*d.C t s+2*d.R t s+
    (∫ u in (0 : ℝ)..s, clampedMemory p β d s u*d.C t u)+
    β^2*(p : ℝ)*coloredMemory p d t s

/-- Earlier-time derivative formula with all coefficient and correlation/response arguments clamped to nonnegative causal times. -/
@[expose] def clampedEarlierSlope (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  -clampedMultiplier d s*clampedCorrelation d t s+2*clampedResponse d t s+
    (∫ u in (0 : ℝ)..s, clampedMemory p β d s u*clampedCorrelation d t u)+
    β^2*(p : ℝ)*coloredMemory p d t s

end SphericalAging.EarlierCovariance

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.StrongBackwardDefect
open CKSpecification EarlierCovariance

/-- Earlier-time FDT defect `∂ₛC(t,s)-R(t,s)`, represented by its CK derivative formula on `0 < s < t`. -/
@[expose] def backwardDefect (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  earlierSlope p β d t s-d.R t s

/-- A nonnegative integrable function of the earlier time that bounds the square of the earlier-time FDT defect at every later time. -/
structure FisherMajorant (p : ℕ) (β : ℝ) (d : CKData) (a : ℝ → ℝ) : Prop where
  nonneg : ∀ s : ℝ, 0 < s → 0 ≤ a s
  integrable : Integrable a (volume.restrict (Ioi 0))
  dominates : ∀ t s : ℝ, 0 < s → s < t → (backwardDefect p β d t s)^2 ≤ a s

end SphericalAging.StrongBackwardDefect

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.BackwardRowL2
open CKSpecification EarlierCovariance GreenCovariance

/-- Lebesgue measure restricted to the positive lag axis `(0,∞)`. -/
@[expose] def rayMeasure : Measure ℝ := volume.restrict (Ioi 0)

/-- Causal response viewed as a function of lag, zero outside `(0,t]`; the lag-zero endpoint does not affect its L² class. -/
@[expose] def responseRow (d : CKData) (t : ℝ) : ℝ→ℝ :=
  (Ioc 0 t).indicator (fun v => clampedResponse d t (t-v))

end SphericalAging.BackwardRowL2

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.BackwardStrongTheorem
open CKSpecification EarlierCovariance

/-- Earlier-time correlation derivative viewed as a function of lag, zero outside `[0,t]`; endpoints do not affect its L² class. -/
@[expose] def sourceEarlierRow (p : ℕ) (β : ℝ) (d : CKData) (t : ℝ) : ℝ→ℝ :=
  (Icc 0 t).indicator (fun v => earlierSlope p β d t (t-v))

end SphericalAging.BackwardStrongTheorem

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.UniformResponseRows
open CKSpecification

/-- Absolute response-profile errors over `s ∈ [0,t]`, together with zero to keep the set nonempty at all times. -/
@[expose] def rowValues (d : CKData) (r : ℝ → ℝ) (t : ℝ) : Set ℝ :=
  {0} ∪ {a | ∃ s : ℝ,s∈Icc 0 t ∧ a=|d.R t s-r (t-s)|}

/-- Real supremum of the response-profile row errors; continuity and physical bounds give boundedness at nonnegative times. -/
@[expose] def rowSup (d : CKData) (r : ℝ → ℝ) (t : ℝ) : ℝ := sSup (rowValues d r t)

end SphericalAging.UniformResponseRows

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.WeightedSlowRatioTheorem
open CKSpecification

/-- Predicted slow fluctuation-dissipation ratio `(p-2)(1-q)/q`, used with positive plateau `q`. -/
@[expose] def slowRatio (p : ℕ) (q : ℝ) : ℝ := ((p:ℝ)-2)*(1-q)/q

/-- Plateau expression `(p-1)q^p-(p-2)q^(p-1)` for the limiting correlation-weighted FDT defect. -/
@[expose] def defectBudget (p : ℕ) (q : ℝ) : ℝ := ((p:ℝ)-1)*q^p-((p:ℝ)-2)*q^(p-1)

/-- Response weighted by `p C^(p-1)` over times up to the lag cutoff `t-A`, expressed as an oriented interval integral. -/
@[expose] def oldWeightedMass (p : ℕ) (d : CKData) (A t : ℝ) : ℝ :=
  (p:ℝ)*(∫ u in (0:ℝ)..t-A,d.C t u^(p-1)*d.R t u)

/-- Change `C(t,t-A)^p-C(t,0)^p` in the correlation-power scale over the old-memory interval. -/
@[expose] def ratioDenominator (p : ℕ) (d : CKData) (A t : ℝ) : ℝ :=
  d.C t (t-A)^p-d.C t 0^p

/-- Response weighted by `p C^(p-1)` before `t-A`, divided by `C(t,t-A)^p-C(t,0)^p`; division is totalized.
In the strict selected sector the denominator is eventually positive for each `A > 0`; the limit takes `t → ∞` before `A → ∞` and is an integrated moment, not a pointwise FDR. -/
@[expose] def weightedSlowRatio (p : ℕ) (d : CKData) (A t : ℝ) : ℝ :=
  oldWeightedMass p d A t/ratioDenominator p d A t

end SphericalAging.WeightedSlowRatioTheorem

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.SlowDefectConstants
open WeightedSlowRatioTheorem

/-- Real power `y^(1/p)`, representing the positive `p`th root in the standing domain `p ≥ 3`, `y > 0`. -/
@[expose] def root (p : ℕ) (y : ℝ) : ℝ := y^((p:ℝ)⁻¹)

/-- Positive slow-defect mass lower bound `q(1-x^(1/p))`, where `x` is the slow ratio and strict low temperature gives `q > 0`, `0 < x < 1`. -/
@[expose] def limitingMass (p : ℕ) (q : ℝ) : ℝ := q*(1-root p (slowRatio p q))

end SphericalAging.SlowDefectConstants

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.ActualDefectTransport
open CKSpecification StrongBackwardDefect

/-- Positive part of the earlier-time FDT defect, `max(∂ᵤC(t,u)-R(t,u),0)`, on the physical causal domain. -/
@[expose] def positive (p : ℕ) (β : ℝ) (d : CKData) (t u : ℝ) : ℝ :=
  max (backwardDefect p β d t u) 0

end SphericalAging.ActualDefectTransport

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.FisherLimitClockDecay

/-- Real supremum of a function on the tail `[T,∞)`; the Fisher conclusions supply bounded tails for `T ≥ 1`. -/
@[expose] def lateSup (f : ℝ → ℝ) (T : ℝ) : ℝ := sSup (f '' Ici T)

end SphericalAging.FisherLimitClockDecay

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.ActualFirstPassage
open CKSpecification

/-- Nonnegative lags at which the correlation with the state at time `s` has reached or fallen below the chosen level. -/
@[expose] def passageSet (d : CKData) (level s : ℝ) : Set ℝ :=
  {u | 0≤u ∧ d.C (s+u) s≤level}

/-- Infimum of the nonnegative crossing lags. The strict cubic conclusions prove a positive finite attained first hit for `s ≥ 0` and levels in `(0,q)`.
This is a totalized real infimum outside the stated crossing domain. -/
@[expose] def firstPassage (d : CKData) (level s : ℝ) : ℝ := sInf (passageSet d level s)

end SphericalAging.ActualFirstPassage

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.FisherCost

/-- Explicit cubic plateau margin `3b(2q-1)(q-z)^2`, with `b=β²` in the Fisher-cost theorem. -/
@[expose] def margin (b q z : ℝ) : ℝ := 3 * b * (2 * q - 1) * (q - z) ^ 2

/-- Cubic margin divided by `ell+15b`, whose positivity is established in the strictly low-temperature conclusion. -/
@[expose] def fisherRatio (b q c ell : ℝ) : ℝ :=
  margin b q c / (ell + 15 * b)

/-- Dimensionless lower bound `min(1,(margin/(ell+15b))²)` for passage time times integrated Fisher majorant. -/
@[expose] def fisherCost (b q c ell : ℝ) : ℝ :=
  min 1 (fisherRatio b q c ell ^ 2)

end SphericalAging.FisherCost

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.FisherPassageTheorem
open CKSpecification ActualFirstPassage FisherCost

/-- Cubic Fisher passage-cost conclusions: vanishing time-times-Fisher cost enforces plateau behavior,
and each level in `(0,q)` has diverging first passage times with explicit positive local and tail Fisher costs. -/
@[expose] def Conclusions (β q : ℝ) (d : CKData) (a : ℝ → ℝ) : Prop :=
  (∀s τ : ℕ → ℝ,Tendsto s atTop atTop → Tendsto τ atTop atTop →
    Tendsto (fun n => τ n*(∫ u in (s n)..(s n+τ n),a u)) atTop (𝓝 0) →
    Tendsto (fun n => d.C (s n+τ n) (s n)) atTop (𝓝 q) ∧
    Tendsto (fun n => susceptibility d (s n+τ n) (s n)) atTop (𝓝 (1-q))) ∧
  (∀level : ℝ,level∈Ioo 0 q →
    (∀s : ℝ,0≤s → 0<firstPassage d level s ∧
      d.C (s+firstPassage d level s) s=level ∧
      ∀u : ℝ,0≤u → u<firstPassage d level s → level<d.C (s+u) s) ∧
    Tendsto (firstPassage d level) atTop atTop ∧
    0<fisherCost (β^2) q level (PlateauAlgebra.multiplier 3 β q) ∧
    ENNReal.ofReal (fisherCost (β^2) q level (PlateauAlgebra.multiplier 3 β q))≤
      liminf (fun s : ℝ => ENNReal.ofReal (firstPassage d level s*(∫u in s..(s+firstPassage d level s),a u))) atTop ∧
    ENNReal.ofReal (fisherCost (β^2) q level (PlateauAlgebra.multiplier 3 β q))≤
      liminf (fun s : ℝ => ENNReal.ofReal (firstPassage d level s*(∫u in Ioi s,a u))) atTop)

end SphericalAging.FisherPassageTheorem

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.SphereOnlyActualMainClosure
open CKSpecification WeightedSlowRatioTheorem StrongBackwardDefect

/-- Fixed-cutoff weighted-response limits with eventually positive denominators, the iterated slow-ratio limit,
and the limiting total correlation-weighted FDT defect. -/
@[expose] def WeightedRatioConclusion (p : ℕ) (β : ℝ) (d : CKData)
    (c : ℝ→ℝ) (q : ℝ) : Prop :=
    (∀A : ℝ,0<A→
      (∀ᶠt : ℝ in atTop,0<ratioDenominator p d A t) ∧
      Tendsto (weightedSlowRatio p d A) atTop (𝓝 ((c A^p-defectBudget p q)/c A^p))) ∧
    Tendsto (fun A : ℝ => limUnder atTop (weightedSlowRatio p d A))
      atTop (𝓝 (slowRatio p q)) ∧
    Tendsto (fun t : ℝ => (p:ℝ)*(∫u in (0:ℝ)..t,
      d.C t u^(p-1)*backwardDefect p β d t u)) atTop (𝓝 (defectBudget p q))

end SphericalAging.SphereOnlyActualMainClosure

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.PalomarFisherStatements
open CKSpecification FiniteModel HardSphereDynamics SphereInitialLaw
open SphereRotationGeometry SphereCanonicalEntropy SphereAnnealedFisherBudget
open EarlierCovariance StrongBackwardDefect BackwardRowL2 BackwardStrongTheorem
open UniformResponseRows WeightedSlowRatioTheorem SlowDefectConstants
open ActualDefectTransport PlateauAlgebra AllTemperatureTheorem

/-- Ordinary forward density for the actual spherical diffusion, characterized
by its literal coordinate-rotation Kolmogorov forward equation. Conditions are
on the sphere; values of the ambient smooth extension are not probabilistic
density values off the sphere. -/
structure ForwardDensityConditions (N p : ℕ) (β : ℝ)
    (ρ : Disorder N p → ℝ → Vector N → ℝ) : Prop where
  spatial_C2 : ∀ J t, ContDiff ℝ 2 (ρ J t)
  joint_continuous : ∀ J, Continuous (Function.uncurry (ρ J))
  positive_on_sphere : ∀ J t x, 0≤t → OnSphere x → 0<ρ J t x
  initially_uniform : ∀ J x, OnSphere x → ρ J 0 x=1
  mass_one : ∀ J (t : ℝ≥0), (∫x,ρ J t x ∂sphereLaw N)=1
  forward_PDE : ∀ J t x, 0<t → OnSphere x →
    HasDerivAt (fun s=>ρ J s x) (sphericalForwardDensitySlope β J (ρ J t) x) t
  fisher_joint_measurable : StronglyMeasurable
    (fun z : Disorder N p × ℝ=>fisherInformation β z.1 (ρ z.1 z.2))
  fisher_disorder_integrable : ∀t : ℝ,0≤t→Integrable
    (fun J=>fisherInformation β J (ρ J t)/(N:ℝ)) (disorderLaw N p)
  fisher_product_integrable : Integrable
    (fun z : Disorder N p × ℝ=>fisherInformation β z.1 (ρ z.1 z.2))
    ((disorderLaw N p).prod (volume.restrict (Ioi 0)))
  fisher_time_integrable : IntegrableOn (annealedFisher β ρ) (Ioi 0)

/-- The complete late-time response and FDT-defect conclusion, including an
actual Fisher integral along one subsequence of dimensions. Explicit L²
membership prevents totalized extended norms from weakening the statement. -/
@[expose] def ResponseConclusion (p : ℕ) (β : ℝ) (d : CKData) (φ : ℕ→ℕ)
    (ρ : (N : ℕ)→Disorder N p→ℝ→Vector N→ℝ) (aF r : ℝ→ℝ) (q : ℝ) : Prop :=
    StrictMono φ ∧ FisherMajorant p β d aF ∧
    (∀s : ℝ, 0 ≤ s → 0 ≤ aF s) ∧ (∫s in Ioi 0,aF s)≤β^2/2 ∧
    (∀A : ℝ,Tendsto (fun n=>∫s in Ioc 0 A,
      |annealedFisher β (ρ (φ n+3)) s-aF s|) atTop (𝓝 0)) ∧
    Tendsto (FisherLimitClockDecay.lateSup aF) atTop (𝓝 0) ∧
    MemLp r 2 rayMeasure ∧
    (∀t : ℝ,0≤t→MemLp (responseRow d t) 2 rayMeasure ∧
      MemLp (sourceEarlierRow p β d t) 2 rayMeasure) ∧
    (∀t s : ℝ,0<s→s<t→HasDerivAt (fun u=>d.C t u) (earlierSlope p β d t s) s) ∧
    Tendsto (fun t=>(eLpNorm (fun v=>responseRow d t v-r v) 2 rayMeasure).toReal) atTop (𝓝 0) ∧
    Tendsto (fun t=>(eLpNorm (fun v=>sourceEarlierRow p β d t v-r v) 2 rayMeasure).toReal) atTop (𝓝 0) ∧
    Tendsto (rowSup d r) atTop (𝓝 0) ∧
    Tendsto (fun t=>susceptibility d t 0/Real.sqrt t) atTop (𝓝 0) ∧
    Tendsto (fun t=>∫s in (0:ℝ)..t,|backwardDefect p β d t s|^2) atTop (𝓝 0) ∧
    (transitionBetaSquared p<β^2→
      0<limitingMass p q ∧
      Tendsto (fun A : ℝ=>limUnder atTop (weightedSlowRatio p d A)) atTop (𝓝 (slowRatio p q)) ∧
      (∀S : ℝ,0≤S→∃M : ℝ≥0∞,ENNReal.ofReal (limitingMass p q)≤M ∧
        Tendsto (fun L : ℝ=>liminf (fun t : ℝ=>
          ENNReal.ofReal (∫u in S..t-L,positive p β d t u)) atTop) atTop (𝓝 M)) ∧
      ENNReal.ofReal (limitingMass p q^2)≤
        liminf (fun t : ℝ=>ENNReal.ofReal (t*(∫u in (0:ℝ)..t,positive p β d t u^2))) atTop) ∧
    Tendsto aF atTop (𝓝 0) ∧
    (∀T : ℝ,1≤T→BddAbove (aF '' Ici T))

/-- A coherent selected stationary profile and the SAME Fisher majorant in
response/FDT and in every cubic passage-cost conclusion. -/
structure FisherConclusions (p : ℕ) (β : ℝ) (d : CKData) (ell q : ℝ)
    (c r : ℝ→ℝ) (φ : ℕ→ℕ)
    (ρ : (N : ℕ)→Disorder N p→ℝ→Vector N→ℝ) (aF : ℝ→ℝ) : Prop where
  plateau_bounds : 0≤q ∧ q<1
  plateau_limit : Tendsto c atTop (𝓝 q)
  correlation_continuous : ContinuousOn c (Ici 0)
  response_continuous : ContinuousOn r (Ici 0)
  profile_bounds : ∀t : ℝ,0≤t→0≤r t ∧ r t≤c t ∧ c t≤1
  integrable_response : IntegrableOn r (Ioi 0)
  response_mass : (∫t in Ioi 0,r t)=1-q
  aging : PalomarPrincipalStatements.AgingConclusion p β d ell q c r
  actual_forward_densities : ∀N : ℕ,3≤N→ForwardDensityConditions N p β (ρ N)
  response : ResponseConclusion p β d φ ρ aF r q
  weighted_ratio : transitionBetaSquared p<β^2→
    SphereOnlyActualMainClosure.WeightedRatioConclusion p β d c q
  slow_ratio_range : transitionBetaSquared p<β^2→0<slowRatio p q ∧ slowRatio p q<1
  cubic_fisher_cost : p=3→transitionBetaSquared 3<β^2→
    q=largerPlateau 3 β ∧ (1/2:ℝ)<q ∧ FisherPassageTheorem.Conclusions β q d aF

end SphericalAging.PalomarFisherStatements

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.PalomarCompleteTheorems
open CKSpecification FiniteModel PalomarPrincipalStatements PalomarFisherStatements

/-- For every integer `p ≥ 3` and inverse temperature `β > 0`, one CK solution realizes all principal and Fisher conclusions.
The stationary profile, dimension subsequence, actual forward densities and Fisher majorant share the displayed witnesses;
critical cubic product bounds use `β ≥ β_d`, whereas positive Fisher costs require `β > β_d`. -/
theorem exists_complete_conclusions (p : ℕ) (hp : 3≤p) (β : ℝ) (hβ : 0<β) :
    ∃d : CKData, CKEquations p β d ∧ PhysicalBounds d ∧
      PositiveSemidefiniteCorrelation d ∧
      ∃(ell q : ℝ) (c r : ℝ→ℝ) (φ : ℕ→ℕ)
        (ρ : (N : ℕ)→Disorder N p→ℝ→Vector N→ℝ) (aF : ℝ→ℝ),
        PrincipalConclusions p β d ell q c r ∧
        FisherConclusions p β d ell q c r φ ρ aF := by
  sorry

end SphericalAging.PalomarCompleteTheorems

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.ResponseCompactness

/-- Pairs of real time offsets `(a,b)` with `b ≤ a`; offsets may be negative because the translating times tend to infinity. -/
abbrev CausalOffsets := {z : ℝ × ℝ // z.2 ≤ z.1}

end SphericalAging.ResponseCompactness

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.PalomarStationarity
attribute [local instance 2000] PolynormableSpace.continuousSMul
open CKSpecification ResponseCompactness

/-- A late translating sequence and locally uniform limits of its correlation, causal response and multiplier.
Compact offset sets include negative offsets; no stationarity or FDT is assumed in this definition. -/
structure RawTranslatedCluster (d : CKData) (T : ℕ → ℝ)
    (C : ℝ × ℝ → ℝ) (R : CausalOffsets → ℝ) (L : ℝ → ℝ) : Prop where
  late : Tendsto T atTop atTop
  correlation : ∀ K : Set (ℝ × ℝ), IsCompact K → TendstoUniformlyOn
    (fun n z => d.C (T n + z.1) (T n + z.2)) C atTop K
  response : ∀ K : Set CausalOffsets, IsCompact K → TendstoUniformlyOn
    (fun n z => d.R (T n + z.1.1) (T n + z.1.2)) R atTop K
  multiplier : ∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
    (fun n x => d.multiplier (T n + x)) L atTop K

/-- A raw translated cluster is stationary, with FDT and a monotone plateau profile on nonnegative lags, integrable response and a closed response equation.
The same original translating sequence converges locally uniformly to the global representatives of these profiles, the multiplier and the energy. -/
structure StationaryConclusions (p : ℕ) (β : ℝ) (d : CKData) (T : ℕ → ℝ)
    (C : ℝ × ℝ → ℝ) (R : CausalOffsets → ℝ) (L : ℝ → ℝ)
    (c r : ℝ → ℝ) (ell q e : ℝ) : Prop where
  correlation_form : ∀ x y, C (x,y) = c |x-y|
  response_form : ∀ z : CausalOffsets, R z = r (z.1.1-z.1.2)
  multiplier_form : ∀ x, L x = ell
  continuous_c : Continuous c
  continuous_r : Continuous r
  initial_c : c 0 = 1
  initial_r : r 0 = 1
  correlation_bounds : ∀ t, 0 ≤ t → 0 ≤ c t ∧ c t ≤ 1
  response_nonnegative : ∀ t, 0 ≤ t → 0 ≤ r t
  fdt : ∀ t, 0 ≤ t → HasDerivWithinAt c (-r t) (Ici 0) t
  correlation_antitone : AntitoneOn c (Ici 0)
  plateau : Tendsto c atTop (𝓝 q)
  plateau_bounds : 0 ≤ q ∧ q < 1
  integrable_response : IntegrableOn r (Ioi 0)
  response_mass : (∫ t in Ioi 0, r t) = 1-q
  correlation_uniform : ∀ K : Set (ℝ × ℝ), IsCompact K → TendstoUniformlyOn
    (fun n z => d.C (T n + z.1) (T n + z.2)) (fun z => c |z.1-z.2|) atTop K
  response_uniform : ∀ K : Set CausalOffsets, IsCompact K → TendstoUniformlyOn
    (fun n z => d.R (T n + z.1.1) (T n + z.1.2))
      (fun z => r (z.1.1-z.1.2)) atTop K
  multiplier_uniform : ∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
    (fun n x => d.multiplier (T n + x)) (fun _ => ell) atTop K
  energy_uniform : ∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
    (fun n x => energy p β d (T n + x)) (fun _ => e) atTop K
  multiplier_energy : ell = 1 + (p : ℝ)*β*e
  response_contDiff : ContDiffOn ℝ 1 r (Ici 0)
  response_equation : ∀ t, 0 ≤ t → HasDerivWithinAt r
    (-ell*r t+β^2*(p : ℝ)*((p : ℝ)-1)*
      (∫ u in (0 : ℝ)..t,c (t-u)^(p-2)*r (t-u)*r u)) (Ici 0) t

end SphericalAging.PalomarStationarity

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SphericalAging.PalomarStationarityCertificate
open CKSpecification PalomarStationarity

/-- Every CK solution admits a raw cluster along a subsequence of every late translating sequence.
Every raw cluster on its original sequence, not only a specially chosen cluster, has the displayed stationary and FDT conclusions. -/
theorem proposition5_7 {p : ℕ} {β : ℝ} {d : CKData} (hd : CKEquations p β d) :
    (∀ (T : ℕ → ℝ), Tendsto T atTop atTop →
      ∃ (C : ℝ × ℝ → ℝ) (R : ResponseCompactness.CausalOffsets → ℝ)
        (L : ℝ → ℝ) (φ : ℕ → ℕ),
        StrictMono φ ∧ RawTranslatedCluster d (T∘φ) C R L) ∧
    (∀ (T : ℕ → ℝ) (C : ℝ × ℝ → ℝ) (R : ResponseCompactness.CausalOffsets → ℝ)
      (L : ℝ → ℝ), RawTranslatedCluster d T C R L →
      ∃ (c r : ℝ → ℝ) (ell q e : ℝ), StationaryConclusions p β d T C R L c r ell q e) := by
  sorry

end SphericalAging.PalomarStationarityCertificate
