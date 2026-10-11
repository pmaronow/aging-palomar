module

public import SphericalAging.SphereMixedDerivatives
public import SphericalAging.SphereEntropyBudget

public section

/-! Actual time differentiation of Fisher information for the genuine spherical
forward PDE. Mixed derivatives and differentiation under the compact sphere
integral are proved from smoothness, and the Γ₂ identity follows from actual IBP. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereFisherTimeDerivative

open MeasureTheory FiniteModel SphereInitialLaw SphericalIntegrationByParts SphereEntropyDissipation
open SphereGeneratorIntegrationByParts SphereForwardAdjoint SphereFDTAlgebra SphereLogDensityEquation
open SphereFisherDissipation SphereMixedDerivatives SphereEntropyBudget
open scoped BigOperators

/-- The actual rotation Fisher equals density times the squared actual Gibbs score. -/
theorem rotationFisher_eq_score_integral {N p : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    {ρ : Vector N → ℝ} (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x,0<ρ x) :
    rotationFisher κ β J A ρ=
      ∫ x : Vector N,ρ x*rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ) x ∂sphereLaw N := by
  classical
  have hψ := relativeLog_contDiff β J (hρ.of_le (by norm_num)) hpos
  have hi i : Integrable (fun x : Vector N =>
      (rotationFlux β J (A i) ρ x)^2/ρ x) (sphereLaw N) :=
    continuous_sphere_integrable hN
      (((rotationFlux_contDiff β J _ hρ).continuous.pow 2).div hρ.continuous
        (fun x => (hpos x).ne'))
  unfold rotationFisher
  rw [← integral_finsetSum Finset.univ (fun i _ => hi i),← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    unfold rotationGamma
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [relativeLog_lieDerivative β J _ (hρ.of_le (by norm_num)) hpos x]
    field_simp [(hpos x).ne']

/-- Γ differentiates in time using the proved Schwarz interchange. -/
theorem rotationGamma_time_hasDerivAt {N : ℕ} {ι : Type*} [Fintype ι]
    (κ : ℝ) (A : ι → Operator N) {f : ℝ → Vector N → ℝ}
    (hf : ContDiff ℝ 2 (Function.uncurry f)) (t : ℝ) (x : Vector N) :
    HasDerivAt (fun s => rotationGamma κ A (f s) (f s) x)
      (2*rotationGamma κ A (f t) (timeSlope f t) x) t := by
  classical
  have hd i := lieDerivative_time_hasDerivAt (A i) hf t x
  have hh := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hd i).mul (hd i))).const_mul κ
  convert hh using 1
  · rfl
  · unfold rotationGamma
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem joint_rotationGamma_continuous {N : ℕ} {ι : Type*} [Fintype ι]
    (κ : ℝ) (A : ι → Operator N) {f g : ℝ → Vector N → ℝ}
    (hf : ContDiff ℝ 2 (Function.uncurry f)) (hg : ContDiff ℝ 2 (Function.uncurry g)) :
    Continuous (fun z : ℝ × Vector N => rotationGamma κ A (f z.1) (g z.1) z.2) := by
  classical
  unfold rotationGamma
  exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
    (joint_lieDerivative_contDiff_order (A i) hf).continuous.mul
      (joint_lieDerivative_contDiff_order (A i) hg).continuous)

/-- Genuine differentiated Fisher score integral, with its actual time partials. -/
theorem fisher_score_integral_hasDerivAt {N : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ : ℝ) (A : ι → Operator N) {ρ f : ℝ → Vector N → ℝ}
    (hρ : ContDiff ℝ 2 (Function.uncurry ρ)) (hf : ContDiff ℝ 3 (Function.uncurry f))
    (t : ℝ) :
    HasDerivAt (fun s => ∫ x : Vector N,ρ s x*rotationGamma κ A (f s) (f s) x ∂sphereLaw N)
      (∫ x : Vector N,timeSlope ρ t x*rotationGamma κ A (f t) (f t) x+
        2*ρ t x*rotationGamma κ A (f t) (timeSlope f t) x ∂sphereLaw N) t := by
  have hf₂ : ContDiff ℝ 2 (Function.uncurry f) := hf.of_le (by norm_num)
  have hG := joint_rotationGamma_continuous κ A hf₂ hf₂
  have hdotρ := (timeSlope_contDiff_one hρ).continuous
  have hdotf : ContDiff ℝ 2 (Function.uncurry (timeSlope f)) := timeSlope_contDiff_order hf
  have hGdot := joint_rotationGamma_continuous κ A hf₂ hdotf
  apply hasDerivAt_sphere_parameter_integral hN
    (F := fun s x => ρ s x*rotationGamma κ A (f s) (f s) x)
    (F' := fun s x => timeSlope ρ s x*rotationGamma κ A (f s) (f s) x+
      2*ρ s x*rotationGamma κ A (f s) (timeSlope f s) x)
    (hρ.continuous.mul hG)
    ((hdotρ.mul hG).add ((continuous_const.mul hρ.continuous).mul hGdot))
  intro s x
  convert (timeSlope_hasDerivAt (hρ.of_le (by norm_num)) s x).mul
    (rotationGamma_time_hasDerivAt κ A hf₂ s x) using 1
  ring

/-- Exact Fisher dissipation from the actual forward density PDE. The time and
spatial derivatives are not assumed to commute, and no Fisher identity is assumed. -/
theorem rotationFisher_hasDerivAt_gamma2 {N p : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    (hA : ∀ i,star (A i)=-A i) {ρ : ℝ → Vector N → ℝ}
    (hρ : ContDiff ℝ 3 (Function.uncurry ρ)) (hpos : ∀ t x,0<ρ t x)
    (t : ℝ) (hPDE : ∀ x,timeSlope ρ t x=forwardDensitySlope κ β J A (ρ t) x) :
    HasDerivAt (fun s => rotationFisher κ β J A (ρ s))
      (-2*(∫ x : Vector N,ρ t x*rotationGamma2 κ β J A (relativeLog β J (ρ t)) x ∂sphereLaw N)) t := by
  let ψ : ℝ → Vector N → ℝ := fun s => relativeLog β J (ρ s)
  have hψ : ContDiff ℝ 3 (Function.uncurry ψ) :=
    ((hρ.log (fun z => (hpos z.1 z.2).ne')).sub
      (contDiff_const.mul (((Hamiltonian_contDiff J).of_le (by simp)).comp contDiff_snd))).add contDiff_const
  have hρspace s : ContDiff ℝ 3 (ρ s) := by
    simpa only [Function.comp_def,Function.uncurry,id_eq] using
      hρ.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 3 (fun x : Vector N => (s,x)))
  have hψspace : ContDiff ℝ 3 (ψ t) := by
    simpa only [Function.comp_def,Function.uncurry,id_eq] using
      hψ.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 3 (fun x : Vector N => (t,x)))
  have hlogPDE : timeSlope ψ t=(fun x => rotationGenerator κ β J A (ψ t) x+
      rotationGamma κ A (ψ t) (ψ t) x) := by
    funext x
    exact (timeSlope_hasDerivAt (hψ.of_le (by norm_num)) t x).unique
      (logarithmic_density_pde_hasDerivAt κ β J A ((hρspace t).of_le (by norm_num)) (hpos t)
        (fun y => timeSlope_hasDerivAt (hρ.of_le (by norm_num)) t y) hPDE x)
  have hd := fisher_score_integral_hasDerivAt hN κ A (hρ.of_le (by norm_num)) hψ t
  have hfisher : (fun s => rotationFisher κ β J A (ρ s))=
      (fun s => ∫ x : Vector N,ρ s x*rotationGamma κ A (ψ s) (ψ s) x ∂sphereLaw N) := by
    funext s
    exact rotationFisher_eq_score_integral hN κ β J A ((hρspace s).of_le (by norm_num)) (hpos s)
  rw [← hfisher] at hd
  apply hd.congr_deriv
  have hG : ContDiff ℝ 2 (rotationGamma κ A (ψ t) (ψ t)) :=
    rotationGamma_contDiff_order κ A hψspace hψspace
  have hGL : ContDiff ℝ 1 (fun x => rotationGenerator κ β J A (ψ t) x+
      rotationGamma κ A (ψ t) (ψ t) x) :=
    (rotationGenerator_contDiff_one κ β J A hψspace).add (hG.of_le (by norm_num))
  have hi₁ : Integrable (fun x : Vector N => timeSlope ρ t x*
      rotationGamma κ A (ψ t) (ψ t) x) (sphereLaw N) :=
    continuous_sphere_integrable hN
      (((timeSlope_contDiff_one (hρ.of_le (by norm_num))).continuous.comp
        (continuous_const.prodMk continuous_id)).mul hG.continuous)
  have hi₂ : Integrable (fun x : Vector N => 2*ρ t x*rotationGamma κ A (ψ t)
      (fun y => rotationGenerator κ β J A (ψ t) y+rotationGamma κ A (ψ t) (ψ t) y) x)
      (sphereLaw N) := continuous_sphere_integrable hN
    ((continuous_const.mul (hρspace t).continuous).mul
      (rotationGamma_continuous κ A (hψspace.of_le (by norm_num)) hGL))
  rw [hlogPDE]
  rw [integral_add hi₁ hi₂]
  have hadj := forward_density_adjoint hN κ β J A hA
    ((hρspace t).of_le (by norm_num)) (hpos t) hG
  have hf₁ : (fun x : Vector N => timeSlope ρ t x*rotationGamma κ A (ψ t) (ψ t) x)=
      (fun x => rotationGamma κ A (ψ t) (ψ t) x*forwardDensitySlope κ β J A (ρ t) x) := by
    funext x
    rw [hPDE x]
    ring
  rw [hf₁,hadj]
  have hf₂ : (fun x : Vector N => 2*ρ t x*rotationGamma κ A (ψ t)
      (fun y => rotationGenerator κ β J A (ψ t) y+rotationGamma κ A (ψ t) (ψ t) y) x)=
      (fun x => 2*(ρ t x*rotationGamma κ A (ψ t)
        (fun y => rotationGenerator κ β J A (ψ t) y+rotationGamma κ A (ψ t) (ψ t) y) x)) := by
    funext x
    ring
  rw [hf₂,integral_const_mul]
  exact fisher_production_gamma2 hN κ β J A hA (hρspace t) (hpos t)

/-- Actual source tangent Fisher information obeys the true canonical Γ₂
identity, with coefficient 1/(2N) and the genuine coordinate rotations. -/
theorem spherical_fisher_hasDerivAt_gamma2 {N p : ℕ} (hN : 0<N) (β : ℝ)
    (J : Disorder N p) {ρ : ℝ → Vector N → ℝ}
    (hρ : ContDiff ℝ 3 (Function.uncurry ρ)) (hpos : ∀ t x,0<ρ t x)
    (t : ℝ) (hPDE : ∀ x,timeSlope ρ t x=
      SphereCanonicalEntropy.sphericalForwardDensitySlope β J (ρ t) x) :
    HasDerivAt (fun s => SphereRotationGeometry.fisherInformation β J (ρ s))
      (-2*(∫ x : Vector N,ρ t x*rotationGamma2 (1/(2*(N : ℝ))) β J
        (SphereQuenchedFDT.canonicalRotations N) (relativeLog β J (ρ t)) x ∂sphereLaw N)) t := by
  have hd := rotationFisher_hasDerivAt_gamma2 hN (1/(2*(N : ℝ))) β J
    (SphereQuenchedFDT.canonicalRotations N)
    (fun ij => SphereRotationGeometry.coordinateRotation_skew ij.1 ij.2) hρ hpos t hPDE
  have heq : (fun s => rotationFisher (1/(2*(N : ℝ))) β J
      (SphereQuenchedFDT.canonicalRotations N) (ρ s))=
      (fun s => SphereRotationGeometry.fisherInformation β J (ρ s)) := by
    funext s
    apply SphereRotationGeometry.rotationFisher_eq_tangent hN β J
    · simpa only [Function.comp_def,Function.uncurry,id_eq] using
        (hρ.of_le (show (2 : WithTop ℕ∞) ≤ 3 by norm_num)).comp
          (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : Vector N => (s,x)))
    · exact hpos s
  rwa [heq] at hd

end SphericalAging.SphereFisherTimeDerivative
