module

public import SphericalAging.RandomSDEDriverPullback
public import SphericalAging.TwoTimeResponseParameter
public import SphericalAging.TwoTimeResponseTrace
public import SphericalAging.ResponseMatrixEnergyContraction

public section

/-! The genuine restarted projected flow, its derivative, and expected
trace commute with filtered measure-preserving Wiener sampling. This
proves the response bridge for the actual spliced physical drivers. -/
noncomputable section
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.TwoTimeResponseDriverPullback
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open HardSphereDynamics FiniteModel LocalSDE BrownianDriverPullback
open GlobalSDEDriverPullback RandomSDEDriverPullback RandomInitialDependence
open RandomProjectedInitialContinuity TwoTimeResponseParameter HamiltonianPicardDependence
open ResponseMatrixEnergyContraction
open scoped NNReal ENNReal InnerProductSpace
variable {N p : ℕ} {Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ} {G : Filtration ℝ≥0 mΩ'} {φ : Ω'→Ω}

theorem noiseColumnClass_pullback (hφ : MeasurePreserving φ Q P)
    (hF : ∀t,@Measurable Ω' Ω (G t) (F t) φ) (R : ℝ≥0) (hR : 0<(R:ℝ))
    (j : Fin N) (Z : InitialSpace N F P) :
    noiseColumnClass R hR j (initialPullback hφ hF Z)=
      initialPullback hφ hF (noiseColumnClass R hR j Z) := by
  apply Subtype.ext
  apply Lp.ext
  have hc := hφ.quasiMeasurePreserving.ae_eq_comp (noiseColumnClass_ae R hR j Z)
  filter_upwards [noiseColumnClass_ae R hR j (initialPullback hφ hF Z),
    initialPullback_coe hφ hF Z,initialPullback_coe hφ hF (noiseColumnClass R hR j Z),hc]
      with ω hl hz hr hc
  change ((noiseColumnClass R hR j Z : Lp (State N) 2 P) (φ ω)) = _ at hc
  rw [hl,hr,hc,hz]
  rfl

theorem projectedParameterClass_pullback (hφ : MeasurePreserving φ Q P)
    (hF : ∀t,@Measurable Ω' Ω (G t) (F t) φ) (R : ℝ≥0) (hR : 0<(R:ℝ))
    (Z : InitialSpace N F P) (v : State N) :
    projectedParameterClass R hR (initialPullback hφ hF Z,v)=
      initialPullback hφ hF (projectedParameterClass R hR (Z,v)) := by
  simp only [projectedParameterClass,map_add,map_smul,map_sum,
    noiseColumnClass_pullback hφ hF]

theorem shifted_filtered (hF : ∀t,@Measurable Ω' Ω (G t) (F t) φ) (s : ℝ≥0) :
    ∀t,@Measurable Ω' Ω ((ShiftedBrownian.filtration G s) t)
      ((ShiftedBrownian.filtration F s) t) φ := fun t => hF (s+t)

theorem waitingClass_pullback (hφ : MeasurePreserving φ Q P)
    (hF : ∀t,@Measurable Ω' Ω (G t) (F t) φ)
    (D : BrownianDriver N P F) (E : BrownianDriver N Q G)
    (hB : ∀i t,E.coordinate i t=ᵐ[Q](fun ω => D.coordinate i t (φ ω)))
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R:ℝ)) (s T : ℝ≥0) (q : Disorder N p×State N) :
    waitingClass E β R hR s T q=
      initialPullback hφ (shifted_filtered hF s) (waitingClass D β R hR s T q) := by
  apply Subtype.ext
  apply Lp.ext
  have hc := hφ.quasiMeasurePreserving.ae_eq_comp (waitingClass_ae D β R hR s T q)
  have hp := process_pullback hφ hF D E hB
    (drift_family_lipschitz β R hR (‖q.1‖₊+1) ⟨q.1,by simp⟩)
    (noise_family_lipschitz N R hR) q.2
  filter_upwards [waitingClass_ae E β R hR s T q,
    initialPullback_coe hφ (shifted_filtered hF s) (waitingClass D β R hR s T q),hc,hp]
      with ω hl hr hc hp
  exact hl.trans ((hp s).trans (hc.symm.trans hr.symm))

theorem restartedClass_pullback (hφ : MeasurePreserving φ Q P)
    (hF : ∀t,@Measurable Ω' Ω (G t) (F t) φ)
    (D : BrownianDriver N P F) (E : BrownianDriver N Q G)
    (hB : ∀i t,E.coordinate i t=ᵐ[Q](fun ω => D.coordinate i t (φ ω)))
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R:ℝ)) (s T t : ℝ≥0) (ht : t≤T)
    (q : Disorder N p×State N) (v : State N) :
    restartedClass E β R hR s T t q v=
      statePullback hφ (restartedClass D β R hR s T t q v) := by
  have hShift : ∀i u,(ShiftedBrownian.driver E s).coordinate i u=ᵐ[Q]
      (fun ω => (ShiftedBrownian.driver D s).coordinate i u (φ ω)) := by
    intro i u
    filter_upwards [hB i (s+u),hB i s] with ω hu hs
    exact congrArg₂ (fun a b : ℝ => a-b) hu hs
  unfold restartedClass
  rw [waitingClass_pullback hφ hF D E hB β R hR s T q,
    projectedParameterClass_pullback]
  exact terminalClass_pullback hφ (shifted_filtered hF s)
    (ShiftedBrownian.driver D s) (ShiftedBrownian.driver E s) hShift β R hR q.1 _ T t ht

/-- The actual projected two-time response is transported by the genuine
L² isometry, proved by differentiating the entire restarted-flow family. -/
theorem physicalMatrix_pullback
    {ψ : Ω'→VectorBrownian.Space N}
    (hψ : MeasurePreserving ψ Q (VectorBrownian.law N)) (hN : N≠0)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (s T t : ℝ≥0) (ht : t≤T) (hT : 0<T)
    (q : Disorder N p×State N) (hx : OnSphere q.2) :
    physicalMatrix hN (driver (VectorBrownian.driver N) hψ) β R hR hNR s T t q hx=
      (statePullback hψ).toContinuousLinearMap.comp
        (physicalMatrix hN (VectorBrownian.driver N) β R hR hNR s T t q hx) := by
  have hc := restartedClass_hasFDerivAt_physicalMatrix hN (VectorBrownian.driver N)
    β R hR hNR s T t ht hT q hx
  have hp := (statePullback hψ).toContinuousLinearMap.hasFDerivAt.comp 0 hc
  have he : (fun v : State N => statePullback hψ
      (restartedClass (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s T t q v))=
      restartedClass (NullAugmentation.driver (driver (VectorBrownian.driver N) hψ))
        β R hR s T t q := by
    funext v
    exact (restartedClass_pullback hψ (fun u => augmented_filtered hψ u)
      (NullAugmentation.driver (VectorBrownian.driver N))
      (NullAugmentation.driver (driver (VectorBrownian.driver N) hψ))
      (fun _ _ => Eventually.of_forall (fun _ => rfl)) β R hR s T t ht q v).symm
  change HasFDerivAt (fun v => statePullback hψ
    (restartedClass (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s T t q v)) _ 0 at hp
  rw [he] at hp
  exact (restartedClass_hasFDerivAt_physicalMatrix hN
    (driver (VectorBrownian.driver N) hψ) β R hR hNR s T t ht hT q hx).unique hp

/-- All actual finite sample columns, hence their scalar trace, commute
with the sample pullback almost everywhere. -/
theorem sampleTrace_pullback (hφ : MeasurePreserving φ Q P)
    (M : State N→L[ℝ]Lp (State N) 2 P) :
    sampleTrace ((statePullback hφ).toContinuousLinearMap.comp M)=ᵐ[Q]
      (fun ω => sampleTrace M (φ ω)) := by
  have hc : ∀ᵐ ω ∂Q,∀i : Fin N,
      (((statePullback hφ).toContinuousLinearMap.comp M) (basisVector i)) ω=
        (M (basisVector i)) (φ ω) := by
    apply ae_all_iff.mpr
    intro i
    exact Lp.coeFn_compMeasurePreserving (M (basisVector i)) hφ
  filter_upwards [hc] with ω hω
  simp only [sampleTrace,hω]

theorem expected_sampleTrace_pullback (hφ : MeasurePreserving φ Q P)
    (M : State N→L[ℝ]Lp (State N) 2 P) :
    (∫ω,sampleTrace ((statePullback hφ).toContinuousLinearMap.comp M) ω ∂Q)=
      ∫ω,sampleTrace M ω ∂P := by
  rw [integral_congr_ae (sampleTrace_pullback hφ M)]
  exact hφ.hasLaw.integral_comp (TwoTimeResponseTrace.normalizedTrace_integrable M).aestronglyMeasurable

theorem physical_expected_sampleTrace_pullback
    {ψ : Ω'→VectorBrownian.Space N}
    (hψ : MeasurePreserving ψ Q (VectorBrownian.law N)) (hN : N≠0)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (s T t : ℝ≥0) (ht : t≤T) (hT : 0<T)
    (q : Disorder N p×State N) (hx : OnSphere q.2) :
    (∫ω,sampleTrace (physicalMatrix hN (driver (VectorBrownian.driver N) hψ)
      β R hR hNR s T t q hx) ω ∂Q)=
      ∫ω,sampleTrace (physicalMatrix hN (VectorBrownian.driver N)
        β R hR hNR s T t q hx) ω ∂VectorBrownian.law N := by
  rw [physicalMatrix_pullback hψ hN β R hR hNR s T t ht hT q hx]
  exact expected_sampleTrace_pullback hψ _

end SphericalAging.TwoTimeResponseDriverPullback
