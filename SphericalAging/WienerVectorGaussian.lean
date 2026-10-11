module

public import SphericalAging.SphereInitialLaw
public import StochasticCalculus.WienerIntegral

public section

/-! The actual deterministic Wiener vector of the independent coordinate
Brownian paths. Its Gaussian law and disorder independence are derived. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory StochasticCalculus
open scoped ENNReal NNReal
namespace SphericalAging.WienerVectorGaussian
open HardSphereDynamics VectorBrownian FiniteModel

@[expose] abbrev TimeL2 := Lp ℝ 2 nonnegativeLebesgueMeasure

@[expose] def scalarIntegral (k : TimeL2) : Path → ℝ :=
  (Lp.aestronglyMeasurable (wienerIntegral scalar_isPreBrownian k)).mk
    (wienerIntegral scalar_isPreBrownian k)

theorem scalarIntegral_ae (k : TimeL2) :
    (wienerIntegral scalar_isPreBrownian k : Path → ℝ)=ᵐ[pathLaw] scalarIntegral k :=
  (Lp.aestronglyMeasurable (wienerIntegral scalar_isPreBrownian k)).ae_eq_mk

theorem scalarIntegral_measurable (k : TimeL2) : Measurable (scalarIntegral k) :=
  (Lp.aestronglyMeasurable (wienerIntegral scalar_isPreBrownian k)).stronglyMeasurable_mk.measurable

theorem scalarIntegral_law (k : TimeL2) (hk : ‖k‖=1) :
    HasLaw (scalarIntegral k) (gaussianReal 0 1) pathLaw := by
  refine ⟨(scalarIntegral_measurable k).aemeasurable,?_⟩
  rw [←Measure.map_congr (scalarIntegral_ae k),map_wienerIntegral_eq_gaussianReal]
  congr 1
  have hn : ‖k‖₊=1 := NNReal.eq hk
  simp [hn]

@[expose] def vectorIntegral {N : ℕ} (k : TimeL2) (ω : Space N) : Vector N :=
  WithLp.toLp 2 (fun i => scalarIntegral k (ω i))

theorem vectorIntegral_measurable (N : ℕ) (k : TimeL2) : Measurable (vectorIntegral (N:=N) k) := by
  exact (by fun_prop : Measurable (WithLp.toLp 2 : (Fin N → ℝ) → Vector N)).comp
    (measurable_pi_iff.mpr (fun i => (scalarIntegral_measurable k).comp (measurable_pi_apply i)))

theorem vectorIntegral_law {N : ℕ} (k : TimeL2) (hk : ‖k‖=1) :
    HasLaw (vectorIntegral (N:=N) k) (stdGaussian (Vector N)) (law N) := by
  refine ⟨(vectorIntegral_measurable N k).aemeasurable,?_⟩
  rw [←map_pi_eq_stdGaussian]
  have hm : Measurable (fun ω : Space N => fun i => scalarIntegral k (ω i)) :=
    measurable_pi_iff.mpr (fun i => (scalarIntegral_measurable k).comp (measurable_pi_apply i))
  change (Measure.pi (fun _ : Fin N => pathLaw)).map
    ((WithLp.toLp 2) ∘ (fun ω : Space N => fun i => scalarIntegral k (ω i)))=_
  rw [←Measure.map_map (by fun_prop) hm,Measure.pi_map_pi
    (fun _ => (scalarIntegral_measurable k).aemeasurable)]
  simp_rw [(scalarIntegral_law k hk).map_eq]

theorem vectorIntegral_independent {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (k : TimeL2) :
    IndepFun (fun ω : Ω×Space N => vectorIntegral k ω.2) Prod.fst (P.prod (law N)) :=
  (indepFun_prod measurable_id (vectorIntegral_measurable N k)).symm

theorem vectorIntegral_augmented_law {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (k : TimeL2) (hk : ‖k‖=1) :
    HasLaw (fun ω : Ω×Space N => vectorIntegral k ω.2)
      (stdGaussian (Vector N)) (P.prod (law N)) :=
  (vectorIntegral_law k hk).comp measurePreserving_snd.hasLaw

end SphericalAging.WienerVectorGaussian
