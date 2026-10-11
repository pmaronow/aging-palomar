module
public import SphericalAging.ActualCoherentMainTheorems
public import SphericalAging.PalomarPrincipalStatements

/-!
# Literal spherical Fisher production and the complete response/cost mains

The density is constrained by the positive normalized spherical forward PDE,
initial density one, and spatial C²/time continuity. The Fisher information
uses the explicit ordered Gaussian Hamiltonian, the normalized Gaussian sphere
law, and the tangent gradient of the logarithmic Gibbs density ratio. One
dimension subsequence and one aF witness both Theorems 1.2 and 1.4.

The matching standalone Challenge duplicates only the mathematical definitions
and imports Mathlib. No response, Fisher budget, or convergence hypothesis is
supplied as an input to the final theorem.
-/
public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal BigOperators

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
