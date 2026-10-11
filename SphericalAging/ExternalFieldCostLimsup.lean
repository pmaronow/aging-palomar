module

public import SphericalAging.ExternalFieldCostTheorem

public section

/-! Exact energy/overlap integral splitting and the printed real limsup
clause of source10.2, with actual lower bounds discharged by Gaussian
landscape moments. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ExternalFieldCostLimsup
open Set Filter MeasureTheory FiniteModel GaussianLandscape GaussianLandscapeMoments
open ExternalFieldElementaryPenalty ExternalFieldSharpScalar ExternalFieldProbabilityTransfer
open ExternalFieldUniformCost ExternalFieldSeededCost HamiltonianBallBounds SphereGibbsEntropy
open scoped Topology InnerProductSpace NNReal ENNReal
universe u

@[expose]  def seededOverlapPower {N p : ℕ} {Ξ : Type*} (w : Ξ→Vector N)
    (A : Ξ×Disorder N p→Vector N) (z : Ξ×Disorder N p) : ℝ :=
  |⟪w z.1,A z⟫_ℝ/(N:ℝ)|^p

 theorem seededOverlapPower_integrable {N p : ℕ} (hN : 1≤N)
    {Ξ : Type*} [MeasurableSpace Ξ] (σ : Measure Ξ) [IsProbabilityMeasure σ]
    {w : Ξ→Vector N} {A : Ξ×Disorder N p→Vector N} (hw : Measurable w) (hA : Measurable A)
    (hgood : ∀ᵐξ ∂σ,(∀J,‖A (ξ,J)‖≤Real.sqrt N) ∧ ‖w ξ‖=Real.sqrt N) :
    Integrable (seededOverlapPower (p:=p) w A) (σ.prod (disorderLaw N p)) := by
  have hi : Measurable (fun z : Ξ×Disorder N p => ⟪w z.1,A z⟫_ℝ/(N:ℝ)) :=
    ((continuous_fst.inner continuous_snd : Continuous (fun z : Vector N×Vector N => ⟪z.1,z.2⟫_ℝ)).measurable.comp
      ((hw.comp measurable_fst).prodMk hA)).div_const _
  apply (integrable_const (1:ℝ)).mono'
    ((continuous_abs.measurable.comp hi).pow_const p).aestronglyMeasurable
  filter_upwards [(measurePreserving_fst (μ:=σ) (ν:=disorderLaw N p)).quasiMeasurePreserving.ae hgood] with z hz
  have hh := overlap_abs_le_one (show 0<N by omega) (w z.1) (A z) hz.2 (hz.1 z.2)
  change ‖|⟪w z.1,A z⟫_ℝ/(N:ℝ)|^p‖≤1
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  exact pow_le_one₀ (abs_nonneg _) hh

 theorem seededCost_integral_split {N p : ℕ} (hN : 1≤N) (hp : 3≤p)
    {Ξ : Type*} [MeasurableSpace Ξ] (σ : Measure Ξ) [IsProbabilityMeasure σ]
    {w : Ξ→Vector N} {A : Ξ×Disorder N p→Vector N} (hw : Measurable w) (hA : Measurable A)
    (hgood : ∀ᵐξ ∂σ,(∀J,‖A (ξ,J)‖≤Real.sqrt N) ∧ ‖w ξ‖=Real.sqrt N) :
    (∫z,seededCost (p:=p) w A z ∂σ.prod (disorderLaw N p))=
      (∫z,Hamiltonian N p z.2 (A z)/(N:ℝ) ∂σ.prod (disorderLaw N p))+
        betaD p*(∫z,seededOverlapPower (p:=p) w A z ∂σ.prod (disorderLaw N p)) := by
  have hci := seededCost_integrable hN hp σ hw hA hgood
  have hai := seededOverlapPower_integrable hN σ hw hA hgood
  have hei : Integrable (fun z : Ξ×Disorder N p => Hamiltonian N p z.2 (A z)/(N:ℝ))
      (σ.prod (disorderLaw N p)) :=
    (hci.sub (hai.const_mul (betaD p))).congr (Eventually.of_forall (fun z => by
      change seededCost (p:=p) w A z-betaD p*seededOverlapPower (p:=p) w A z=_
      unfold seededCost seededOverlapPower;ring))
  calc
    _ = (∫z,Hamiltonian N p z.2 (A z)/(N:ℝ) ∂σ.prod (disorderLaw N p))+
      (∫z,betaD p*seededOverlapPower (p:=p) w A z ∂σ.prod (disorderLaw N p)) :=
        integral_add hei (hai.const_mul (betaD p))
    _ = _ := by rw [integral_const_mul]

 theorem seeded_meanCost_ge_lower {N p : ℕ} (hN : 1≤N) (hp : 3≤p)
    {Ξ : Type*} [MeasurableSpace Ξ] (σ : Measure Ξ) [IsProbabilityMeasure σ]
    {w : Ξ→Vector N} {A : Ξ×Disorder N p→Vector N} (hw : Measurable w) (hA : Measurable A)
    (hgood : ∀ᵐξ ∂σ,(∀J,‖A (ξ,J)‖≤Real.sqrt N) ∧ ‖w ξ‖=Real.sqrt N) :
    -momentCeiling p 1≤∫z,seededCost (p:=p) w A z ∂σ.prod (disorderLaw N p) := by
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr (by omega : 0<N)
  have hQi := landscapeNorm_integrable (show 0<N by omega) (show 1≤p by omega)
  have hQ := hQi.comp_snd σ
  have hci := seededCost_integrable hN hp σ hw hA hgood
  have hpnt : ∀ᵐz ∂σ.prod (disorderLaw N p),-landscapeNorm N p z.2≤seededCost (p:=p) w A z := by
    filter_upwards [(measurePreserving_fst (μ:=σ) (ν:=disorderLaw N p)).quasiMeasurePreserving.ae hgood] with z hz
    have he := Hamiltonian_ball_bound (show 0<N by omega) (show 1≤p by omega) z.2 (hz.1 z.2)
    have he' : |Hamiltonian N p z.2 (A z)/(N:ℝ)|≤landscapeNorm N p z.2 := by
      simpa only [abs_div,abs_of_pos hNr] using he
    have hα : 0≤betaD p*|⟪w z.1,A z⟫_ℝ/(N:ℝ)|^p :=
      mul_nonneg (betaD_positive hp).le (pow_nonneg (abs_nonneg _) _)
    have hl := neg_abs_le (Hamiltonian N p z.2 (A z)/(N:ℝ))
    unfold seededCost
    linarith
  have hi := integral_mono_ae hQ.neg hci hpnt
  have hcomp : (∫z : Ξ×Disorder N p,landscapeNorm N p z.2 ∂σ.prod (disorderLaw N p))=
      ∫J : Disorder N p,landscapeNorm N p J ∂disorderLaw N p := by
    rw [integral_prod _ hQ]
    simp only [integral_const,probReal_univ,one_smul]
  change (∫z : Ξ×Disorder N p,-landscapeNorm N p z.2 ∂σ.prod (disorderLaw N p))≤_ at hi
  rw [integral_neg,hcomp] at hi
  have hm := (uniform_real_power_moment hN (show 0<p by omega) (k:=1) (by norm_num)).2
  simp only [Real.rpow_one] at hm
  linarith

 theorem seeded_cost_limsup {p : ℕ} (hp : 3≤p) {L : ℝ≥0} (H : PublishedFieldThreshold p L)
    (dim : ℕ→ℕ) (hDim : ∀n,1≤dim n) (hDimTop : Tendsto dim atTop atTop)
    {Ξ : ℕ→Type u} [∀n,MeasurableSpace (Ξ n)] (σ : ∀n,Measure (Ξ n)) [∀n,IsProbabilityMeasure (σ n)]
    (w : ∀n,Ξ n→Vector (dim n)) (A : ∀n,Ξ n×Disorder (dim n) p→Vector (dim n))
    (hw : ∀n,Measurable (w n)) (hA : ∀n,Measurable (A n))
    (hgood : ∀n,∀ᵐξ ∂σ n,LipschitzWith L
        (fun J : EuclideanSpace ℝ (TensorIndex (dim n) p) => A n (ξ,J.ofLp)) ∧
      (∀J,‖A n (ξ,J)‖≤Real.sqrt (dim n)) ∧ ‖w n ξ‖=Real.sqrt (dim n)) :
    limsup (fun n => (∫z,Hamiltonian (dim n) p z.2 (A n z)/(dim n:ℝ)
      ∂(σ n).prod (disorderLaw (dim n) p))+betaD p*(∫z,seededOverlapPower (p:=p) (w n) (A n) z
        ∂(σ n).prod (disorderLaw (dim n) p))) atTop≤thresholdEnergy p := by
  let f : ℕ→ℝ := fun n => ∫z,seededCost (p:=p) (w n) (A n) z ∂(σ n).prod (disorderLaw (dim n) p)
  have hs : (fun n => (∫z,Hamiltonian (dim n) p z.2 (A n z)/(dim n:ℝ)
      ∂(σ n).prod (disorderLaw (dim n) p))+betaD p*(∫z,seededOverlapPower (p:=p) (w n) (A n) z
        ∂(σ n).prod (disorderLaw (dim n) p)))=f := by
    funext n
    exact (seededCost_integral_split (hDim n) hp (σ n) (hw n) (hA n) ((hgood n).mono (fun _ h => h.2))).symm
  rw [hs]
  have hc := seeded_cost_eventually hp H dim hDim hDimTop σ w A hw hA hgood
  have hl n : -momentCeiling p 1≤f n := seeded_meanCost_ge_lower (hDim n) hp
    (σ n) (hw n) (hA n) ((hgood n).mono (fun _ h => h.2))
  have hu : IsBoundedUnder (·≤·) atTop f := isBoundedUnder_of_eventually_le (hc 1 (by norm_num))
  apply (limsup_le_iff (isCoboundedUnder_le_of_le atTop hl) hu).mpr
  intro b hb
  filter_upwards [hc ((b-thresholdEnergy p)/2) (by linarith)] with n hn
  dsimp [f]
  linarith

end SphericalAging.ExternalFieldCostLimsup
