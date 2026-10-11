module

public import SphericalAging.PrefixVectorC2Generator
public import SphericalAging.SphereRegularizedVariationBounds

public section

/-! The true predictable C² generator is the exact physical tangent norm
generator along the genuine physical variational equation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace BigOperators
namespace SphericalAging.SphereRegularizedPhysicalGenerator
open HardSphereDynamics FiniteModel LocalSDE PredictableDriftTime VectorIto
open PrefixVectorC2Generator SphereRegularizedNorm SphereRegularizedVariationBounds
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem generator_eq_variation_ae {ε : ℝ} (hε : 0<ε) (β : ℝ) (J : Disorder N p)
    (X Y : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (A : Fin N → PredictableProcessL2 F P) (U : Fin N → Fin N → PredictableProcessL2 F P)
    (hA : ∀ i,(A i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun s ω => (fderiv ℝ (hamiltonianDrift β J) (X s ω) (Y s ω)) i) T)
    (hU : ∀ i j,(U i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun s ω => (fderiv ℝ (fun z : State N => noiseColumn z j) (X s ω) (Y s ω)) i) T) :
    ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,q.1∈Ioc 0 T →
      generator (regularizedNorm ε) Y T A U q=variationGenerator ε β J (X q.1 q.2) (Y q.1 q.2) := by
  have hap := ae_all_iff.mpr hA
  have hup := ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hU i j))
  have hrp := ae_all_iff.mpr (fun i => representative_ae (A i))
  filter_upwards [hap,hup,hrp] with q ha hu hr
  intro hq
  have hqa : q∈Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) := ⟨hq,mem_univ _⟩
  have heA (i : Fin N) : cutRepresentative (A i) T q=
      (fderiv ℝ (hamiltonianDrift β J) (X q.1 q.2) (Y q.1 q.2)) i := by
    rw [cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame,indicator_of_mem hqa,hr i,ha i]
    exact ite_eq_left hq
  have heU (i j : Fin N) : (U i j : TimeProcessL2 P) q=
      (fderiv ℝ (fun z : State N => noiseColumn z j) (X q.1 q.2) (Y q.1 q.2)) i := by
    rw [hu i j]
    exact ite_eq_left hq
  simp only [generator,derivativeCut,hessianCut,FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true]
  simp_rw [heA,heU]
  rw [derivative_coordinates,hessian_coordinates]
  rfl

theorem generator_bound_ae (hN : 2≤N) (hp : 2≤p) {ε β : ℝ}
    (hε : 0<ε) (hβ : 0≤β) (J : Disorder N p) (X Y : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (A : Fin N → PredictableProcessL2 F P) (U : Fin N → Fin N → PredictableProcessL2 F P)
    (hA : ∀ i,(A i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun s ω => (fderiv ℝ (hamiltonianDrift β J) (X s ω) (Y s ω)) i) T)
    (hU : ∀ i j,(U i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun s ω => (fderiv ℝ (fun z : State N => noiseColumn z j) (X s ω) (Y s ω)) i) T)
    (hSphere : ∀ᵐ ω ∂P,∀ s,s≤T → OnSphere (X s ω))
    (hTangent : ∀ᵐ ω ∂P,∀ s,s≤T → ⟪X s ω,Y s ω⟫_ℝ=0) :
    ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,q.1∈Ioc 0 T →
      generator (regularizedNorm ε) Y T A U q≤
        (β*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J)*regularizedNorm ε (Y q.1 q.2)+
          Real.sqrt ε/(N:ℝ) := by
  have hsp := (Measure.quasiMeasurePreserving_snd (μ:=nonnegativeLebesgueMeasure) (ν:=P)).ae hSphere
  have htp := (Measure.quasiMeasurePreserving_snd (μ:=nonnegativeLebesgueMeasure) (ν:=P)).ae hTangent
  filter_upwards [generator_eq_variation_ae hε β J X Y T A U hA hU,hsp,htp] with q hg hs ht
  intro hq
  rw [hg hq]
  exact variationGenerator_tangent_le hN hp hε hβ J _ _ (hs q.1 hq.2) (ht q.1 hq.2)

end SphericalAging.SphereRegularizedPhysicalGenerator
