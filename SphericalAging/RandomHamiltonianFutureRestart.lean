module

public import SphericalAging.RandomSDEStateClass
public import SphericalAging.ActualSphereMarkovRestart
public import SphericalAging.RandomHamiltonianTerminal

public section

/-! True cutoff Hamiltonian restart at every correlated L² state known
at the waiting time. The future product law, actual filtered Itô pullback,
and genuine random-initial strong uniqueness derive the restart identity.
Projected perturbations need not remain on the sphere. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.RandomHamiltonianFutureRestart
open HardSphereDynamics ActualSphereTransition HamiltonianPicardDependence
open RandomInitialDependence AnnealedSDECore BrownianFuturePath BrownianFutureFiltered
open FilteredRandomSDEPullback RandomSDEConversions RandomSDEStateClass
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem terminalClass_ae_future (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : FiniteModel.Disorder N p) (s T t : ℝ≥0) (ht : t≤T)
    (Z : VectorBrownian.Space N → State N)
    (hZ : StronglyMeasurable[(NullAugmentation.augment (VectorBrownian.filtration N)
      (VectorBrownian.law N)) s] Z) (hm : MemLp Z 2 (VectorBrownian.law N)) :
    let hZ0 : StronglyMeasurable[ShiftedBrownian.filtration
      (NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)) s 0] Z :=
        by rw [ShiftedBrownian.filtration_zero];exact hZ
    RandomHamiltonianTerminal.terminalClass
      (ShiftedBrownian.driver (NullAugmentation.driver (VectorBrownian.driver N)) s)
      β R hR T t (J,initialStateClass Z hZ0 hm)=ᵐ[VectorBrownian.law N]
        (fun ω => jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR
          (J,Z ω) t (future s ω)) := by
  intro hZ0
  let P := VectorBrownian.law N
  let F := NullAugmentation.augment (VectorBrownian.filtration N) P
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let Ds := ShiftedBrownian.driver D s
  let W : VectorBrownian.Space N → AnnealedCutoffProcess.Parameter N p := fun ω => (J,Z ω)
  have hWa : Measurable[F s] W := measurable_const.prodMk hZ.measurable
  have hWm : Measurable W := hWa.mono (F.le s) le_rfl
  let ρ := P.map W
  letI : IsProbabilityMeasure ρ := (hasLaw_map hWm.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  have hdis : ∀ᵐ q ∂ρ,q.1=J := by
    apply (ae_map_iff hWm.aemeasurable (measurable_fst (MeasurableSet.singleton J))).mpr
    exact .of_forall (fun _ => rfl)
  have hJ : MemLp (fun q : AnnealedCutoffProcess.Parameter N p => q.1) 2 ρ :=
    MemLp.of_bound measurable_fst.aestronglyMeasurable ‖J‖ (hdis.mono (fun q h => by rw [h]))
  let E := IndependentBackgroundDriver.driver (ρ := ρ) D
  let Y := AnnealedCutoffProcess.process D β R hR hJ T
  let φ : VectorBrownian.Space N → AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N :=
    fun ω => (W ω,future s ω)
  have hφ : MeasurePreserving φ P (ρ.prod P) := waiting_future_measurePreserving s W hWa
  have hφF : ∀ u,@Measurable (VectorBrownian.Space N)
      (AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N)
      (ShiftedBrownian.filtration F s u)
      (IndependentBackgroundDriver.filtration (AnnealedCutoffProcess.Parameter N p) F u) φ :=
    waiting_future_filtered s W hWa
  have hB : ∀ i u,Ds.coordinate i u=ᵐ[P] (fun ω => E.coordinate i u (φ ω)) :=
    fun _ _ => .of_forall (fun _ => rfl)
  have hpull : IsRandomStrongSolutionOn Ds
      (fun _ => CutoffSDE.cutoffDrift β J R hR) (fun _ => CutoffSDE.cutoffNoise N R hR)
      Z (fun u ω => Y u (φ ω)) T :=
    randomStrongSolution_pullback hφ hφF E Ds hB _ _ _ _ T
      (AnnealedCutoffSDE.process_strongSolution D β R hR hJ T)
  let hb := drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩
  let hs := noise_family_lipschitz N R hR
  let X := RandomInitialSDE.horizonProcess Ds hb hs Z hZ0 hm T
  have hX := strongSolution_to_random (fun i => (hb i).continuous) hZ0
    (RandomInitialSDE.horizonProcess_strongSolution Ds hb hs Z hZ0 hm T)
  have he := randomStrongSolutions_unique Ds hb hs Z hm X (fun u ω => Y u (φ ω)) T hX hpull
  have hglobal := AnnealedCutoffProcess.process_slice_global D β R hR hJ T
  have hYa : StronglyMeasurable (Y t) := (AnnealedCutoffProcess.process_stronglyAdapted D β R hR hJ T t).mono
    ((IndependentBackgroundDriver.filtration (AnnealedCutoffProcess.Parameter N p) F).le t)
  have hja : StronglyMeasurable (fun q : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N =>
      jointProcess D β R hR q.1 t q.2) := (jointProcess_measurable D β R hR).comp_measurable
    (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have hj : Y t=ᵐ[ρ.prod P] (fun q => jointProcess D β R hR q.1 t q.2) := by
    apply (Measure.ae_prod_iff_ae_ae (hYa.measurableSet_eq_fun hja)).mpr
    filter_upwards [hglobal] with q hq
    filter_upwards [hq,jointProcess_ae D β R hR q] with ω hq hj
    exact (hq t ht).trans (hj t).symm
  have hterm := RandomHamiltonianTerminal.terminalClass_ae Ds β R hR T t J Z hZ0 hm
    (‖J‖₊+1) (by simp)
  filter_upwards [hterm,he,hφ.quasiMeasurePreserving.ae hj] with ω hc he hj
  exact hc.trans ((he t ht).trans hj)

end SphericalAging.RandomHamiltonianFutureRestart
