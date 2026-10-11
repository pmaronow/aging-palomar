module

public import SphericalAging.ExternalFieldUniformCost
public import SphericalAging.SeedConditionalIntegral

public section

/-! Source 10.2's actual independent-seed conditional absolute-field cost.
The only external research input is the preceding published theorem 10.1. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ExternalFieldSeededCost
open Set Filter MeasureTheory FiniteModel GaussianLandscape
open ExternalFieldElementaryPenalty ExternalFieldSharpScalar ExternalFieldProbabilityTransfer
open ExternalFieldUniformCost HamiltonianBallBounds SphereGibbsEntropy SeedConditionalIntegral
open scoped Topology InnerProductSpace NNReal ENNReal

@[expose]  def seededCost {N p : ℕ} {Ξ : Type*} (w : Ξ→Vector N)
    (A : Ξ×Disorder N p→Vector N) (z : Ξ×Disorder N p) : ℝ :=
  Hamiltonian N p z.2 (A z)/(N:ℝ)+betaD p*|⟪w z.1,A z⟫_ℝ/(N:ℝ)|^p

 theorem seededCost_measurable {N p : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    {w : Ξ→Vector N} {A : Ξ×Disorder N p→Vector N}
    (hw : Measurable w) (hA : Measurable A) : Measurable (seededCost (p:=p) w A) := by
  have he : Measurable (fun z : Ξ×Disorder N p => Hamiltonian N p z.2 (A z)/(N:ℝ)) :=
    ((Hamiltonian_joint_continuous N p).measurable.comp (measurable_snd.prodMk hA)).div_const _
  have hi : Measurable (fun z : Ξ×Disorder N p => ⟪w z.1,A z⟫_ℝ/(N:ℝ)) :=
    ((continuous_fst.inner continuous_snd : Continuous (fun z : Vector N×Vector N => ⟪z.1,z.2⟫_ℝ)).measurable.comp
      ((hw.comp measurable_fst).prodMk hA)).div_const _
  exact he.add (((continuous_abs.measurable.comp hi).pow_const p).const_mul (betaD p))

 theorem seededCost_integrable {N p : ℕ} (hN : 1≤N) (hp : 3≤p)
    {Ξ : Type*} [MeasurableSpace Ξ] (σ : Measure Ξ) [IsProbabilityMeasure σ]
    {w : Ξ→Vector N} {A : Ξ×Disorder N p→Vector N} (hw : Measurable w) (hA : Measurable A)
    (hgood : ∀ᵐξ ∂σ,(∀J,‖A (ξ,J)‖≤Real.sqrt N) ∧ ‖w ξ‖=Real.sqrt N) :
    Integrable (seededCost (p:=p) w A) (σ.prod (disorderLaw N p)) := by
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr (by omega : 0<N)
  have hQ := (landscapeNorm_integrable (show 0<N by omega) (show 1≤p by omega)).comp_snd σ
  apply (hQ.add (integrable_const (betaD p))).mono' (seededCost_measurable hw hA).aestronglyMeasurable
  filter_upwards [(measurePreserving_fst (μ:=σ) (ν:=disorderLaw N p)).quasiMeasurePreserving.ae hgood] with z hz
  have he := Hamiltonian_ball_bound (show 0<N by omega) (show 1≤p by omega) z.2 (hz.1 z.2)
  have ha := overlap_abs_le_one (show 0<N by omega) (w z.1) (A z) hz.2 (hz.1 z.2)
  have ha' : |⟪w z.1,A z⟫_ℝ/(N:ℝ)|^p≤1 := pow_le_one₀ (abs_nonneg _) ha
  have hb : 0≤betaD p*|⟪w z.1,A z⟫_ℝ/(N:ℝ)|^p :=
    mul_nonneg (betaD_positive hp).le (pow_nonneg (abs_nonneg _) _)
  have hα := mul_le_of_le_one_right (betaD_positive hp).le ha'
  calc
    ‖seededCost (p:=p) w A z‖ = |Hamiltonian N p z.2 (A z)/(N:ℝ)+betaD p*|⟪w z.1,A z⟫_ℝ/(N:ℝ)|^p| := rfl
    _ ≤ |Hamiltonian N p z.2 (A z)/(N:ℝ)|+|betaD p*|⟪w z.1,A z⟫_ℝ/(N:ℝ)|^p| := abs_add_le _ _
    _ ≤ landscapeNorm N p z.2+betaD p := by
      rw [abs_of_nonneg hb]
      exact add_le_add (by simpa only [abs_div,abs_of_pos hNr] using he) hα

 theorem conditional_seeded_cost_extended {N p : ℕ} (hN : 1≤N) (hp : 3≤p) {L : ℝ≥0}
    {Ξ : Type*} [MeasurableSpace Ξ] (σ : Measure Ξ) [IsProbabilityMeasure σ]
    {w : Ξ→Vector N} {A : Ξ×Disorder N p→Vector N} (hw : Measurable w) (hA : Measurable A)
    (hgood : ∀ᵐξ ∂σ,LipschitzWith L (fun J : EuclideanSpace ℝ (TensorIndex N p) => A (ξ,J.ofLp)) ∧
      (∀J,‖A (ξ,J)‖≤Real.sqrt N) ∧ ‖w ξ‖=Real.sqrt N) :
    ∀ᵐz ∂σ.prod (disorderLaw N p),
      ENNReal.ofReal ((σ.prod (disorderLaw N p))[seededCost (p:=p) w A |
        MeasurableSpace.comap Prod.fst inferInstance] z)≤ENNReal.ofReal (thresholdEnergy p)+phi p L N := by
  have hfi := seededCost_integrable hN hp σ hw hA (hgood.mono (fun ξ hξ => hξ.2))
  have hce := condExp_seed_product σ (disorderLaw N p) (seededCost_measurable hw hA).stronglyMeasurable hfi
  filter_upwards [hce,(measurePreserving_fst (μ:=σ) (ν:=disorderLaw N p)).quasiMeasurePreserving.ae hgood] with z hz hg
  let B : BallFieldAlgorithm N p L :=
    { output := fun J => A (z.1,J)
      measurable_output := hA.comp (measurable_const.prodMk measurable_id)
      lipschitz_output := hg.1
      ball_output := hg.2.1
      direction := w z.1
      norm_direction := hg.2.2 }
  rw [hz]
  exact actual_meanCost_extended_bound B

 theorem conditional_seeded_cost_real {N p : ℕ} (hN : 1≤N) (hp : 3≤p) {L : ℝ≥0}
    (hφ : phi p L N≠⊤) {Ξ : Type*} [MeasurableSpace Ξ] (σ : Measure Ξ) [IsProbabilityMeasure σ]
    {w : Ξ→Vector N} {A : Ξ×Disorder N p→Vector N} (hw : Measurable w) (hA : Measurable A)
    (hgood : ∀ᵐξ ∂σ,LipschitzWith L (fun J : EuclideanSpace ℝ (TensorIndex N p) => A (ξ,J.ofLp)) ∧
      (∀J,‖A (ξ,J)‖≤Real.sqrt N) ∧ ‖w ξ‖=Real.sqrt N) :
    ∀ᵐz ∂σ.prod (disorderLaw N p),
      ((σ.prod (disorderLaw N p))[seededCost (p:=p) w A |
        MeasurableSpace.comap Prod.fst inferInstance] z)≤thresholdEnergy p+(phi p L N).toReal := by
  have hfi := seededCost_integrable hN hp σ hw hA (hgood.mono (fun ξ hξ => hξ.2))
  have hce := condExp_seed_product σ (disorderLaw N p) (seededCost_measurable hw hA).stronglyMeasurable hfi
  filter_upwards [hce,(measurePreserving_fst (μ:=σ) (ν:=disorderLaw N p)).quasiMeasurePreserving.ae hgood] with z hz hg
  let B : BallFieldAlgorithm N p L :=
    { output := fun J => A (z.1,J)
      measurable_output := hA.comp (measurable_const.prodMk measurable_id)
      lipschitz_output := hg.1
      ball_output := hg.2.1
      direction := w z.1
      norm_direction := hg.2.2 }
  rw [hz]
  exact actual_meanCost_le_phi_real hφ B

 theorem seeded_meanCost_le_uniform {N p : ℕ} (hN : 1≤N) (hp : 3≤p) {L : ℝ≥0} {B : ℝ}
    (hbound : ∀A : BallFieldAlgorithm N p L,meanCost A≤B)
    {Ξ : Type*} [MeasurableSpace Ξ] (σ : Measure Ξ) [IsProbabilityMeasure σ]
    {w : Ξ→Vector N} {A : Ξ×Disorder N p→Vector N} (hw : Measurable w) (hA : Measurable A)
    (hgood : ∀ᵐξ ∂σ,LipschitzWith L (fun J : EuclideanSpace ℝ (TensorIndex N p) => A (ξ,J.ofLp)) ∧
      (∀J,‖A (ξ,J)‖≤Real.sqrt N) ∧ ‖w ξ‖=Real.sqrt N) :
    (∫z,seededCost (p:=p) w A z ∂σ.prod (disorderLaw N p))≤B := by
  have hfi := seededCost_integrable hN hp σ hw hA (hgood.mono (fun ξ hξ => hξ.2))
  have hb : ∀ᵐξ ∂σ,(∫J : Disorder N p,seededCost (p:=p) w A (ξ,J) ∂disorderLaw N p)≤B := by
    filter_upwards [hgood] with ξ hξ
    let C : BallFieldAlgorithm N p L :=
      { output := fun J => A (ξ,J)
        measurable_output := hA.comp (measurable_const.prodMk measurable_id)
        lipschitz_output := hξ.1
        ball_output := hξ.2.1
        direction := w ξ
        norm_direction := hξ.2.2 }
    exact hbound C
  rw [integral_prod _ hfi]
  have hh := integral_mono_ae hfi.integral_prod_left (integrable_const B) hb
  simpa only [integral_const,probReal_univ,one_smul] using hh

 theorem seeded_meanCost_le_phi_real {N p : ℕ} (hN : 1≤N) (hp : 3≤p) {L : ℝ≥0}
    (hφ : phi p L N≠⊤) {Ξ : Type*} [MeasurableSpace Ξ] (σ : Measure Ξ) [IsProbabilityMeasure σ]
    {w : Ξ→Vector N} {A : Ξ×Disorder N p→Vector N} (hw : Measurable w) (hA : Measurable A)
    (hgood : ∀ᵐξ ∂σ,LipschitzWith L (fun J : EuclideanSpace ℝ (TensorIndex N p) => A (ξ,J.ofLp)) ∧
      (∀J,‖A (ξ,J)‖≤Real.sqrt N) ∧ ‖w ξ‖=Real.sqrt N) :
    (∫z,seededCost (p:=p) w A z ∂σ.prod (disorderLaw N p))≤thresholdEnergy p+(phi p L N).toReal :=
  seeded_meanCost_le_uniform hN hp (fun C => actual_meanCost_le_phi_real hφ C) σ hw hA hgood

 theorem seeded_meanCost_extended {N p : ℕ} (hN : 1≤N) (hp : 3≤p) {L : ℝ≥0}
    {Ξ : Type*} [MeasurableSpace Ξ] (σ : Measure Ξ) [IsProbabilityMeasure σ]
    {w : Ξ→Vector N} {A : Ξ×Disorder N p→Vector N} (hw : Measurable w) (hA : Measurable A)
    (hgood : ∀ᵐξ ∂σ,LipschitzWith L (fun J : EuclideanSpace ℝ (TensorIndex N p) => A (ξ,J.ofLp)) ∧
      (∀J,‖A (ξ,J)‖≤Real.sqrt N) ∧ ‖w ξ‖=Real.sqrt N) :
    ENNReal.ofReal (∫z,seededCost (p:=p) w A z ∂σ.prod (disorderLaw N p))≤
      ENNReal.ofReal (thresholdEnergy p)+phi p L N := by
  by_cases ht : phi p L N=⊤
  · rw [ht,add_top];exact le_top
  · have hh := seeded_meanCost_le_phi_real hN hp ht σ hw hA hgood
    have hx := (ENNReal.ofReal_le_ofReal hh).trans ENNReal.ofReal_add_le
    simpa only [ENNReal.ofReal_toReal ht] using hx

 universe u

 /-- Unconditional source 10.2 bound along any dimension sequence and any
 independent probability seed spaces. The external input is only 10.1. -/
 theorem seeded_cost_eventually {p : ℕ} (hp : 3≤p) {L : ℝ≥0} (H : PublishedFieldThreshold p L)
    (dim : ℕ→ℕ) (hDim : ∀n,1≤dim n) (hDimTop : Tendsto dim atTop atTop)
    {Ξ : ℕ→Type u} [∀n,MeasurableSpace (Ξ n)] (σ : ∀n,Measure (Ξ n)) [∀n,IsProbabilityMeasure (σ n)]
    (w : ∀n,Ξ n→Vector (dim n)) (A : ∀n,Ξ n×Disorder (dim n) p→Vector (dim n))
    (hw : ∀n,Measurable (w n)) (hA : ∀n,Measurable (A n))
    (hgood : ∀n,∀ᵐξ ∂σ n,LipschitzWith L
        (fun J : EuclideanSpace ℝ (TensorIndex (dim n) p) => A n (ξ,J.ofLp)) ∧
      (∀J,‖A n (ξ,J)‖≤Real.sqrt (dim n)) ∧ ‖w n ξ‖=Real.sqrt (dim n)) :
    ∀ε>0,∀ᶠn in atTop,
      (∫z,seededCost (p:=p) (w n) (A n) z ∂(σ n).prod (disorderLaw (dim n) p))≤thresholdEnergy p+ε := by
  intro ε hε
  filter_upwards [hDimTop.eventually (uniform_meanCost_eventually hp H hε)] with n hn
  exact seeded_meanCost_le_uniform (hDim n) hp hn (σ n) (hw n) (hA n) (hgood n)

end SphericalAging.ExternalFieldSeededCost
