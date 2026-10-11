module

public import SphericalAging.BrownianDriverPullback
public import SphericalAging.ActualSphereMarkovRestart
public import SphericalAging.QuenchedCoefficientDuhamel

public section

/-! The genuine physical solution under a sampled Wiener driver equals
the canonical physical solution evaluated at that path. Filtered Itô
pullback proves the equation, and sphere pathwise uniqueness identifies
the actual constructed terminal classes. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter
open scoped NNReal ENNReal
namespace SphericalAging.DriverProcessPullback
open FiniteModel HardSphereDynamics AnnealedSDECore ActualSphereTransition
  ActualSphereMarkovRestart BrownianDriverPullback FilteredRandomSDEPullback
  AnnealedPhysicalUniqueness HamiltonianDisorderTerminalDerivative
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {φ : Ω→VectorBrownian.Space N}

theorem jointProcess_pullback (hN : 0<N) (hφ : MeasurePreserving φ P (VectorBrownian.law N))
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) (x : State N) (hx : OnSphere x) :
    ∀ᵐomega ∂P,∀t,jointProcess
      (NullAugmentation.driver (driver (VectorBrownian.driver N) hφ)) β R hR (J,x) t omega=
        jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) t (φ omega) := by
  let D0 := driver (VectorBrownian.driver N) hφ
  let D := NullAugmentation.driver D0
  let X := jointProcess D β R hR (J,x)
  let Y : ℝ≥0→Ω→State N := fun t omega =>
    jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) t (φ omega)
  have hX T := jointProcess_physical (Nat.ne_of_gt hN) D0 β R hR hNR J x hx T
  have hY T : IsRandomStrongSolutionOn D
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i)
      (fun _ => x) Y T := by
    exact randomStrongSolution_pullback hφ (fun t => augmented_filtered hφ t)
      (NullAugmentation.driver (VectorBrownian.driver N)) D
      (fun _ _ => Eventually.of_forall (fun _ => rfl))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i)
      (fun _ => x) (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x)) T
      (jointProcess_physical (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR J x hx T)
  exact physical_global_pathwise_uniqueness D β (fun _ => J) stronglyMeasurable_const
    (fun _ => x) X Y hX hY
    (jointProcess_onSphere (Nat.ne_of_gt hN) D0 β R hR hNR J x hx)
    (hφ.quasiMeasurePreserving.ae (jointProcess_onSphere (Nat.ne_of_gt hN)
      (VectorBrownian.driver N) β R hR hNR J x hx))

theorem stateClass_pullback (hN : 0<N) (hφ : MeasurePreserving φ P (VectorBrownian.law N))
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) (x : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t≤T) :
    (stateClass (NullAugmentation.driver (driver (VectorBrownian.driver N) hφ)) β R hR J x T t :
      Ω→State N)=ᵐ[P]
        (fun omega => jointProcess (NullAugmentation.driver (VectorBrownian.driver N))
          β R hR (J,x) t (φ omega)) := by
  let D0 := driver (VectorBrownian.driver N) hφ
  have hs := stateClass_ae (NullAugmentation.driver D0) β R hR J x T t
  have hg := GlobalSDE.process_eq_horizon (NullAugmentation.driver D0)
    (HamiltonianPicardDependence.drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩)
    (HamiltonianPicardDependence.noise_family_lipschitz N R hR) x T
  have hj := jointProcess_ae (NullAugmentation.driver D0) β R hR (J,x)
  have hp := jointProcess_pullback hN hφ β R hR hNR J x hx
  filter_upwards [hs,hg,hj,hp] with omega hs hg hj hp
  exact hs.trans ((hg t ht).symm.trans ((hj t).symm.trans (hp t)))

end SphericalAging.DriverProcessPullback
