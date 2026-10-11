module

public import SphericalAging.SphereEulerAlgorithm
public import SphericalAging.SphereEulerPhysicalError
public import SphericalAging.ActualSphereTransition

public section

/-! Genuine dimension-uniform strong Euler approximation of the actual
physical Hamiltonian endpoint, with final projection onto the sphere ball. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.SphereEulerStrongApproximation
open FiniteModel HardSphereDynamics SphereEulerPredictable SphereEulerInterpolationAlgebra
open SphereEulerPhysicalComparison SphereEulerPhysicalError SphereEulerAlgorithm SphereEulerMeshRate
open SphereEulerDimensionRate AdditiveSphereApproximationCoefficients ActualSphereTransition
open HamiltonianPicardDependence GlobalHamiltonianParameter
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

section Physical
variable (hN : 0<N) (hp : 2≤p) (D₀ : BrownianDriver N P F) (β T : ℝ≥0)
  (J : Disorder N p) (R : ℝ≥0) (hR : 0<(R:ℝ)) {Kb Ks : ℝ≥0}
  (hb : ∀i,LipschitzWith Kb (CutoffSDE.cutoffDrift (β:ℝ) J R hR i))
  (hs : ∀i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
  (x : State N) (M : ℕ) (hM : M≠0) (hNR : (N:ℝ)<(R:ℝ)^2) (hx : OnSphere x)

include hN hp hM hNR hx in
theorem projected_error_le :
    (∫omega,‖hardProcess D₀ β (mesh T M) J R hR hb hs x M T omega-
      endpoint (NullAugmentation.driver D₀) β T M J x omega‖^2 ∂P)≤
      comparisonBound N (driftRate β J) (SphereEulerLocalMoment.localCeiling β (mesh T M) J M) T T := by
  have ht : T≤grid (mesh T M) M := by rw [grid_mesh T hM]
  have he := differenceClass_ae hN D₀ β (mesh T M) J R hR hb hs x M T
  have hm : MemLp (fun omega => hardProcess D₀ β (mesh T M) J R hR hb hs x M T omega-
      interpolant (NullAugmentation.driver D₀) β (mesh T M) J x M T omega) 2 P :=
    (Lp.memLp (differenceClass hN D₀ β (mesh T M) J R hR hb hs x M T)).ae_eq he
  have hbound : ∀ᵐomega ∂P,‖hardProcess D₀ β (mesh T M) J R hR hb hs x M T omega-
      endpoint (NullAugmentation.driver D₀) β T M J x omega‖≤
      ‖hardProcess D₀ β (mesh T M) J R hR hb hs x M T omega-
        interpolant (NullAugmentation.driver D₀) β (mesh T M) J x M T omega‖ := by
    filter_upwards [hardProcess_onSphere hN D₀ β (mesh T M) J R hR hb hs x M hNR hx] with omega hsp
    have hh := SphereEulerCoefficients.clip_lipschitz.dist_le_mul
      (hardProcess D₀ β (mesh T M) J R hR hb hs x M T omega)
      (interpolant (NullAugmentation.driver D₀) β (mesh T M) J x M T omega)
    rw [SphereEulerCoefficients.clip_eq_onSphere _ (hsp T ht)] at hh
    have hz : interpolant (NullAugmentation.driver D₀) β (mesh T M) J x M T omega=
        node (NullAugmentation.driver D₀) β (mesh T M) J x M omega := by
      simpa only [grid_mesh T hM] using
        interpolant_grid (NullAugmentation.driver D₀) β (mesh T M) J x (M:=M) le_rfl omega
    simpa only [hz,endpoint,dist_eq_norm,NNReal.coe_one,one_mul] using hh
  have hX : AEStronglyMeasurable (hardProcess D₀ β (mesh T M) J R hR hb hs x M T) P :=
    ((GlobalSDE.horizonProcess_stronglyAdapted (NullAugmentation.driver D₀)
    hb hs x (grid (mesh T M) M) T).mono ((NullAugmentation.augment F P).le _)).aestronglyMeasurable
  have hY : AEStronglyMeasurable (endpoint (NullAugmentation.driver D₀) β T M J x) P :=
    (endpoint_measurable (NullAugmentation.driver D₀) β T M J x).aestronglyMeasurable
  have hv := hm.norm.mono' (hX.sub hY) hbound
  have hh := physical_euler_secondMoment hN hp D₀ β (mesh T M) J R hR hb hs x M hNR hx T ht
  rw [grid_mesh T hM] at hh
  calc
    _ ≤∫omega,‖hardProcess D₀ β (mesh T M) J R hR hb hs x M T omega-
        interpolant (NullAugmentation.driver D₀) β (mesh T M) J x M T omega‖^2 ∂P := by
      apply integral_mono_ae hv.integrable_norm_pow' hm.integrable_norm_pow'
      exact hbound.mono (fun _ hbnd => pow_le_pow_left₀ (norm_nonneg _) hbnd 2)
    _ ≤_ := hh

include hN hp hM hNR hx in
theorem normalized_projected_error_le (A : ℝ≥0) (hJ : GaussianLandscape.landscapeNorm N p J≤A) :
    (∫omega,‖hardProcess D₀ β (mesh T M) J R hR hb hs x M T omega-
      endpoint (NullAugmentation.driver D₀) β T M J x omega‖^2 ∂P)/(N:ℝ)≤
      (globalRate p β A T:ℝ)*(T:ℝ)/(M:ℝ) := by
  have hK : driftRate β J≤stateRate p β A := by
    change 1+(β:ℝ)*(p:ℝ)*GaussianLandscape.landscapeNorm N p J*2^(p-2)*(3*(p:ℝ)+5)≤
      1+(β:ℝ)*(p:ℝ)*(A:ℝ)*2^(p-2)*(3*(p:ℝ)+5)
    gcongr
  exact (div_le_div_of_nonneg_right (projected_error_le hN hp D₀ β T J R hR hb hs x M hM hNR hx)
    (Nat.cast_nonneg N)).trans (normalized_comparisonBound_mesh hN β A T J hJ hM _ hK)

end Physical

theorem actual_endpoint_error_le (hN : 0<N) (hp : 2≤p) (D₀ : BrownianDriver N P F)
    (β A T : ℝ≥0) (J : Disorder N p) (hJ : GaussianLandscape.landscapeNorm N p J≤A)
    (R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (x : State N) (hx : OnSphere x) {M : ℕ} (hM : M≠0) :
    (∫omega,‖jointProcess (NullAugmentation.driver D₀) β R hR (J,x) T omega-
      endpoint (NullAugmentation.driver D₀) β T M J x omega‖^2/(N:ℝ) ∂P)≤
      (globalRate p β A T:ℝ)*(T:ℝ)/(M:ℝ) := by
  let hb := drift_family_lipschitz (β:ℝ) R hR (‖J‖₊+1) ⟨J,by simp⟩
  let hs := noise_family_lipschitz N R hR
  have he : (fun omega => jointProcess (NullAugmentation.driver D₀) β R hR (J,x) T omega)=ᵐ[P]
      hardProcess D₀ β (mesh T M) J R hR hb hs x M T := by
    filter_upwards [jointProcess_ae (NullAugmentation.driver D₀) β R hR (J,x),
      GlobalSDE.process_eq_horizon (NullAugmentation.driver D₀) hb hs x (grid (mesh T M) M)] with omega hactual hhor
    exact (hactual T).trans (hhor T (by rw [grid_mesh T hM]))
  rw [integral_div]
  have hh := normalized_projected_error_le hN hp D₀ β T J R hR hb hs x M hM hNR hx A hJ
  have hEq : (∫omega,‖jointProcess (NullAugmentation.driver D₀) β R hR (J,x) T omega-
      endpoint (NullAugmentation.driver D₀) β T M J x omega‖^2 ∂P)=
      ∫omega,‖hardProcess D₀ β (mesh T M) J R hR hb hs x M T omega-
        endpoint (NullAugmentation.driver D₀) β T M J x omega‖^2 ∂P :=
    integral_congr_ae (he.mono (fun _ heq => by dsimp only at heq ⊢;rw [heq]))
  rw [hEq]
  exact hh

end SphericalAging.SphereEulerStrongApproximation
