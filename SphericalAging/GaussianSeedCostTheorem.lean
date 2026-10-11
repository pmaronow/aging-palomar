module

public import SphericalAging.SeedCostAsymptotic
public import SphericalAging.SeedAlgorithmEnergyBounds

public section

/-! Complete local Gaussian-seed cost argument. The only external input
is the literal preceding published single-field threshold10.1, from which
the actual independent-seed absolute-overlap cost is proved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.GaussianSeedCostTheorem
open Set Filter MeasureTheory ProbabilityTheory FiniteModel SphereInitialLaw
  GaussianSphereDirection GaussianSeedOverlapBounds SeedCostAsymptotic
  SeedAlgorithmEnergyBounds ExternalFieldSeededCost ExternalFieldUniformCost
  ExternalFieldSharpScalar ExternalFieldElementaryPenalty GaussianLandscape
open scoped Topology InnerProductSpace NNReal
universe u

theorem source11_9 {p : ℕ} (hp : 3≤p) {L : ℝ≥0} (H : PublishedFieldThreshold p L)
    (dim : ℕ→ℕ) (hDim : ∀n,1≤dim n) (hTop : Tendsto dim atTop atTop)
    {Ξ : ℕ→Type u} [∀n,MeasurableSpace (Ξ n)]
    (σ : ∀n,Measure (Ξ n)) [∀n,IsProbabilityMeasure (σ n)]
    (G : ∀n,Ξ n→Vector (dim n)) (hG : ∀n,HasLaw (G n) (gaussianLaw (dim n)) (σ n))
    (hGmeas : ∀n,Measurable (G n))
    (A : ∀n,Ξ n×Disorder (dim n) p→Vector (dim n)) (hA : ∀n,Measurable (A n))
    (hgood : ∀n,∀ᵐξ ∂σ n,LipschitzWith L
      (fun J : EuclideanSpace ℝ (TensorIndex (dim n) p) => A n (ξ,J.ofLp)) ∧
        ∀J,‖A n (ξ,J)‖≤Real.sqrt (dim n))
    {δ : ℝ} (hδ : 0≤δ)
    (heLow : thresholdEnergy p-δ≤liminf
      (fun n => ∫z,energy (A n) z ∂(σ n).prod (disorderLaw (dim n) p)) atTop) :
    (∀n,Integrable (fun z : Ξ n×Disorder (dim n) p =>
      |inner ℝ (A n z) (G n z.1)/(dim n:ℝ)|)
      ((σ n).prod (disorderLaw (dim n) p))) ∧
    limsup (fun n => ∫z : Ξ n×Disorder (dim n) p,
      |inner ℝ (A n z) (G n z.1)/(dim n:ℝ)|
      ∂(σ n).prod (disorderLaw (dim n) p)) atTop≤
        (betaD p)^(-((p:ℝ)⁻¹))*δ^((p:ℝ)⁻¹) := by
  have hn n : 0<dim n := by have hh := hDim n;omega
  let μ n := (σ n).prod (disorderLaw (dim n) p)
  let w n (ξ : Ξ n) := direction (dim n) (hn n) (G n ξ)
  let e n := ∫z,energy (A n) z ∂μ n
  let m n := ∫z : Ξ n×Disorder (dim n) p,
    |inner ℝ (A n z) (w n z.1)/(dim n:ℝ)|^p ∂μ n
  let s n := ∫z : Ξ n×Disorder (dim n) p,
    |inner ℝ (A n z) (w n z.1)/(dim n:ℝ)| ∂μ n
  let g n := ∫z : Ξ n×Disorder (dim n) p,
    |inner ℝ (A n z) (G n z.1)/(dim n:ℝ)| ∂μ n
  let err n := Real.sqrt (Real.pi^2/(2*(dim n:ℝ)))
  have hw n : Measurable (w n) := (direction_measurable (hn n)).comp (hGmeas n)
  have hgoodw n : ∀ᵐξ ∂σ n,LipschitzWith L
      (fun J : EuclideanSpace ℝ (TensorIndex (dim n) p) => A n (ξ,J.ofLp)) ∧
      (∀J,‖A n (ξ,J)‖≤Real.sqrt (dim n)) ∧ ‖w n ξ‖=Real.sqrt (dim n) :=
    (hgood n).mono fun ξ hξ => ⟨hξ.1,hξ.2,direction_norm (hn n) _⟩
  have hball n : ∀ᵐz ∂μ n,‖A n z‖≤Real.sqrt (dim n) := by
    filter_upwards [(measurePreserving_fst (μ := σ n) (ν := disorderLaw (dim n) p)).quasiMeasurePreserving.ae
      (hgood n)] with z hz
    simpa only [Prod.mk.eta] using hz.2 z.2
  have hGlaw n : HasLaw (fun z : Ξ n×Disorder (dim n) p => G n z.1)
      (gaussianLaw (dim n)) (μ n) :=
    (hG n).comp (measurePreserving_fst (μ := σ n) (ν := disorderLaw (dim n) p)).hasLaw
  have hs n := sphere_overlap_power_mean_le (hn n) (hA n).aestronglyMeasurable
    (hGlaw n).aemeasurable.aestronglyMeasurable (hball n) p
  have hg n := gaussian_seed_mean_comparison (hn n) (hA n).aestronglyMeasurable
    (hGlaw n) (hball n)
  have he n := energy_integrable_bound (hn n) (by omega : 1≤p) (σ n) (hA n)
    ((hgood n).mono fun _ hξ => hξ.2)
  have hcost : ∀ε>0,∀ᶠn in atTop,e n+betaD p*m n≤thresholdEnergy p+ε := by
    intro ε hε
    filter_upwards [seeded_cost_eventually hp H dim hDim hTop σ w A hw hA hgoodw ε hε] with n hc
    have hsplit : (∫z,seededCost (p:=p) (w n) (A n) z ∂μ n)=e n+betaD p*m n := by
      have hi := (hs n).2.1.const_mul (betaD p)
      have hpoint : (fun z : Ξ n×Disorder (dim n) p => seededCost (p:=p) (w n) (A n) z)=
          fun z => energy (A n) z+betaD p*|inner ℝ (A n z) (w n z.1)/(dim n:ℝ)|^p := by
        funext z
        unfold seededCost energy
        rw [real_inner_comm]
      rw [hpoint,integral_add (f := energy (A n))
        (g := fun z => betaD p*|inner ℝ (A n z) (w n z.1)/(dim n:ℝ)|^p) (he n).1 hi,
        integral_const_mul]
    rw [hsplit] at hc
    exact hc
  have heBound : IsBoundedUnder (·≥·) atTop e :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall fun n => neg_le_of_abs_le (he n).2)
  have herr : Tendsto err atTop (𝓝 0) := by
    have hi := (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp
      ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).comp hTop)
    have hh := (hi.const_mul (Real.pi^2/2)).sqrt
    convert hh using 1
    · funext n
      dsimp only [err,Function.comp_def]
      congr 1
      field_simp <;> ring
    · simp
  refine ⟨fun n => (hg n).1,?_⟩
  have hh := seed_overlap_limsup_le (by omega : 1≤p) (betaD_positive hp) hδ heBound heLow hcost
    (fun n => ⟨integral_nonneg fun _ => abs_nonneg _,(hs n).2.2⟩)
    (fun n => ⟨integral_nonneg fun _ => abs_nonneg _,(hg n).2⟩) herr
  have heq : (δ/betaD p)^((p:ℝ)⁻¹)=(betaD p)^(-((p:ℝ)⁻¹))*δ^((p:ℝ)⁻¹) := by
    rw [Real.div_rpow hδ (betaD_positive hp).le,div_eq_mul_inv,Real.rpow_neg (betaD_positive hp).le]
    ring
  rw [heq] at hh
  exact hh

end SphericalAging.GaussianSeedCostTheorem
