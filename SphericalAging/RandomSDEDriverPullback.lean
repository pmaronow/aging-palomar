module

public import SphericalAging.GlobalSDEDriverPullback
public import SphericalAging.RandomHamiltonianTerminal

public section

/-! Actual random-initial cutoff solutions and terminal classes commute
with filtered measure-preserving sampling. Initial states retain their
genuine initial sigma-algebra; their pullback is constructed in L². -/
noncomputable section
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.RandomSDEDriverPullback
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open HardSphereDynamics LocalSDE RandomSDEConversions RandomSDEStateClass
open FilteredRandomSDEPullback GlobalSDEDriverPullback RandomInitialDependence
open HamiltonianPicardDependence
open scoped NNReal ENNReal
variable {N p : ℕ} {Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ} {G : Filtration ℝ≥0 mΩ'} {φ : Ω'→Ω}

@[expose] def initialPullback (hφ : MeasurePreserving φ Q P)
    (hF : ∀t,@Measurable Ω' Ω (G t) (F t) φ) :
    InitialSpace N F P→L[ℝ]InitialSpace N G Q := by
  let L := (statePullback (N:=N) hφ).toContinuousLinearMap.comp
    (InitialSpace N F P).subtypeL
  refine L.codRestrict (InitialSpace N G Q) ?_
  intro Z
  let hZ := lpMeas.aestronglyMeasurable Z
  have hsm : StronglyMeasurable[G 0]
      (fun ω => hZ.mk (Z : Ω→State N) (φ ω)) :=
    hZ.stronglyMeasurable_mk.comp_measurable (hF 0)
  have he : (L Z : Ω'→State N)=ᵐ[Q]
      (fun ω => hZ.mk (Z : Ω→State N) (φ ω)) :=
    (Lp.coeFn_compMeasurePreserving (Z : Lp (State N) 2 P) hφ).trans
      (hφ.quasiMeasurePreserving.ae_eq_comp hZ.ae_eq_mk)
  exact hsm.aestronglyMeasurable.congr he.symm

theorem initialPullback_coe (hφ : MeasurePreserving φ Q P)
    (hF : ∀t,@Measurable Ω' Ω (G t) (F t) φ) (Z : InitialSpace N F P) :
    (initialPullback hφ hF Z : Ω'→State N)=ᵐ[Q]
      (fun ω => (Z : Lp (State N) 2 P) (φ ω)) :=
  Lp.coeFn_compMeasurePreserving (Z : Lp (State N) 2 P) hφ

theorem horizonProcess_pullback (hφ : MeasurePreserving φ Q P)
    (hF : ∀t,@Measurable Ω' Ω (G t) (F t) φ)
    (D : BrownianDriver N P F) (E : BrownianDriver N Q G)
    (hB : ∀i t,E.coordinate i t=ᵐ[Q](fun ω => D.coordinate i t (φ ω)))
    {Kb Ks : ℝ≥0} {b : Fin N→State N→ℝ} {σ : Fin N→Fin N→State N→ℝ}
    (hb : ∀i,LipschitzWith Kb (b i)) (hσ : ∀i j,LipschitzWith Ks (σ i j))
    (Z0 : Ω→State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hm : MemLp Z0 2 P)
    (T : ℝ≥0) :
    ∀ᵐω ∂Q,∀t,t≤T→RandomInitialSDE.horizonProcess E hb hσ
      (fun ω => Z0 (φ ω)) (hZ0.comp_measurable (hF 0)) (hm.comp_measurePreserving hφ) T t ω=
        RandomInitialSDE.horizonProcess D hb hσ Z0 hZ0 hm T t (φ ω) := by
  let X := RandomInitialSDE.horizonProcess E hb hσ (fun ω => Z0 (φ ω))
    (hZ0.comp_measurable (hF 0)) (hm.comp_measurePreserving hφ) T
  let Y : ℝ≥0→Ω'→State N := fun t ω =>
    RandomInitialSDE.horizonProcess D hb hσ Z0 hZ0 hm T t (φ ω)
  have hX := strongSolution_to_random (fun i => (hb i).continuous)
    (hZ0.comp_measurable (hF 0)) (RandomInitialSDE.horizonProcess_strongSolution E hb hσ
      (fun ω => Z0 (φ ω)) (hZ0.comp_measurable (hF 0)) (hm.comp_measurePreserving hφ) T)
  have hY := randomStrongSolution_pullback hφ hF D E hB
    (fun _ => b) (fun _ => σ) Z0 (RandomInitialSDE.horizonProcess D hb hσ Z0 hZ0 hm T) T
    (strongSolution_to_random (fun i => (hb i).continuous) hZ0
      (RandomInitialSDE.horizonProcess_strongSolution D hb hσ Z0 hZ0 hm T))
  exact randomStrongSolutions_unique E hb hσ (fun ω => Z0 (φ ω))
    (hm.comp_measurePreserving hφ) X Y T hX hY

theorem initialPullback_initialStateClass (hφ : MeasurePreserving φ Q P)
    (hF : ∀t,@Measurable Ω' Ω (G t) (F t) φ)
    (Z0 : Ω→State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hm : MemLp Z0 2 P) :
    initialPullback hφ hF (initialStateClass Z0 hZ0 hm)=
      initialStateClass (fun ω => Z0 (φ ω)) (hZ0.comp_measurable (hF 0))
        (hm.comp_measurePreserving hφ) := by
  apply Subtype.ext
  apply Lp.ext
  have hc := hφ.quasiMeasurePreserving.ae_eq_comp hm.coeFn_toLp
  filter_upwards [initialPullback_coe hφ hF (initialStateClass Z0 hZ0 hm),hc,
    (hm.comp_measurePreserving hφ).coeFn_toLp] with ω hp hc hrep
  exact hp.trans (hc.trans hrep.symm)

theorem terminalClass_pullback_initialStateClass (hφ : MeasurePreserving φ Q P)
    (hF : ∀t,@Measurable Ω' Ω (G t) (F t) φ)
    (D : BrownianDriver N P F) (E : BrownianDriver N Q G)
    (hB : ∀i t,E.coordinate i t=ᵐ[Q](fun ω => D.coordinate i t (φ ω)))
    (β R : ℝ) (hR : 0<R) (J : FiniteModel.Disorder N p)
    (Z0 : Ω→State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hm : MemLp Z0 2 P)
    (T t : ℝ≥0) (ht : t≤T) :
    RandomHamiltonianTerminal.terminalClass E β R hR T t
      (J,initialPullback hφ hF (initialStateClass Z0 hZ0 hm))=
        statePullback hφ (RandomHamiltonianTerminal.terminalClass D β R hR T t
          (J,initialStateClass Z0 hZ0 hm)) := by
  rw [initialPullback_initialStateClass]
  apply Lp.ext
  let hb := drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩
  let hs := noise_family_lipschitz N R hR
  have hcanonical := hφ.quasiMeasurePreserving.ae_eq_comp
    (RandomHamiltonianTerminal.terminalClass_ae D β R hR T t J Z0 hZ0 hm (‖J‖₊+1) (by simp))
  filter_upwards [RandomHamiltonianTerminal.terminalClass_ae E β R hR T t J
      (fun ω => Z0 (φ ω)) (hZ0.comp_measurable (hF 0)) (hm.comp_measurePreserving hφ)
        (‖J‖₊+1) (by simp),
    horizonProcess_pullback hφ hF D E hB hb hs Z0 hZ0 hm T,
    Lp.coeFn_compMeasurePreserving (RandomHamiltonianTerminal.terminalClass D β R hR T t
      (J,initialStateClass Z0 hZ0 hm)) hφ,hcanonical] with ω he hp hl hd
  exact he.trans ((hp t ht).trans (hd.symm.trans hl.symm))

theorem terminalClass_pullback (hφ : MeasurePreserving φ Q P)
    (hF : ∀t,@Measurable Ω' Ω (G t) (F t) φ)
    (D : BrownianDriver N P F) (E : BrownianDriver N Q G)
    (hB : ∀i t,E.coordinate i t=ᵐ[Q](fun ω => D.coordinate i t (φ ω)))
    (β R : ℝ) (hR : 0<R) (J : FiniteModel.Disorder N p)
    (Z : InitialSpace N F P) (T t : ℝ≥0) (ht : t≤T) :
    RandomHamiltonianTerminal.terminalClass E β R hR T t (J,initialPullback hφ hF Z)=
      statePullback hφ (RandomHamiltonianTerminal.terminalClass D β R hR T t (J,Z)) := by
  let hZ := lpMeas.aestronglyMeasurable Z
  let Z0 := hZ.mk (Z : Ω→State N)
  have hZ0 : StronglyMeasurable[F 0] Z0 := hZ.stronglyMeasurable_mk
  have hm : MemLp Z0 2 P := (Lp.memLp (Z : Lp (State N) 2 P)).ae_eq hZ.ae_eq_mk
  have he : Z=initialStateClass Z0 hZ0 hm := by
    apply Subtype.ext
    apply Lp.ext
    exact hZ.ae_eq_mk.trans hm.coeFn_toLp.symm
  rw [he]
  exact terminalClass_pullback_initialStateClass hφ hF D E hB β R hR J Z0 hZ0 hm T t ht

end SphericalAging.RandomSDEDriverPullback
