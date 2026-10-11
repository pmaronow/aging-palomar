module

public import SphericalAging.FiniteCorrelationEquation
public import SphericalAging.PastL2MartingaleOrthogonality

public section

/-! An actual projected-coordinate Itô increment is orthogonal to every
square-integrable observable measurable at the earlier full filtration. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualCoordinateNoiseOrthogonality
open HardSphereDynamics FiniteModel VectorIto FiniteCorrelationEquation
  PastL2MartingaleOrthogonality
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {X : ℝ≥0→Ω→State N}

 theorem coordinateNoiseValue_ae_vectorProcess (D : BrownianDriver N P F) (hN : 0<N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun u => X u ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ u, OnSphere (X u ω)) {u T : ℝ≥0} (hu : u≤T) (i : Fin N) :
    (coordinateNoiseValue D hN hXa hXc hSphere u i : Ω→ℝ)=ᵐ[P]
      vectorProcess D (matrixNoiseClass hN hXa hXc hSphere T i) u := by
  have he : vectorProcessLp D (matrixNoiseClass hN hXa hXc hSphere T i) u =
      coordinateNoiseValue D hN hXa hXc hSphere u i := by
    unfold vectorProcessLp coordinateNoiseValue
    rw [driverItoMap_apply]
    congr 1
    funext j
    exact matrixNoiseClass_restrict hN hXa hXc hSphere hu i j
  rw [←he]
  exact vectorProcessLp_ae_eq D _ u

 theorem actual_coordinate_noise_past_L2_mean_zero (D : BrownianDriver N P F) (hN : 0<N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun u => X u ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ u, OnSphere (X u ω)) {s t : ℝ≥0} (hst : s≤t) (i : Fin N)
    (Y : Ω→ℝ) (hY : StronglyMeasurable[F s] Y) (hY2 : MemLp Y 2 P) :
    Integrable (fun ω => Y ω*((coordinateNoiseValue D hN hXa hXc hSphere t i : Ω→ℝ) ω-
      (coordinateNoiseValue D hN hXa hXc hSphere s i : Ω→ℝ) ω)) P ∧
    (∫ ω,Y ω*((coordinateNoiseValue D hN hXa hXc hSphere t i : Ω→ℝ) ω-
      (coordinateNoiseValue D hN hXa hXc hSphere s i : Ω→ℝ) ω) ∂P)=0 := by
  have hh := past_L2_increment_mean_zero
    (vectorProcess D (matrixNoiseClass hN hXa hXc hSphere t i))
    (martingale_vectorProcess D _) s t hst
    (vectorProcess_memLp_two D _ s) (vectorProcess_memLp_two D _ t) Y hY hY2
  have he : (fun ω => Y ω*((coordinateNoiseValue D hN hXa hXc hSphere t i : Ω→ℝ) ω-
      (coordinateNoiseValue D hN hXa hXc hSphere s i : Ω→ℝ) ω))=ᵐ[P]
      (fun ω => Y ω*(vectorProcess D (matrixNoiseClass hN hXa hXc hSphere t i) t ω-
        vectorProcess D (matrixNoiseClass hN hXa hXc hSphere t i) s ω)) := by
    filter_upwards [coordinateNoiseValue_ae_vectorProcess D hN hXa hXc hSphere le_rfl i,
      coordinateNoiseValue_ae_vectorProcess D hN hXa hXc hSphere hst i] with ω ht hs
    rw [ht,hs]
  exact ⟨hh.1.congr he.symm,(integral_congr_ae he).trans hh.2⟩

end SphericalAging.ActualCoordinateNoiseOrthogonality
