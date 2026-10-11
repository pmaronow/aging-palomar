module

public import SphericalAging.SphereOnlyLocalParameterIntegral
public import SphericalAging.SphereOnlyGeneratorFDTLocalization
public import SphericalAging.SphereOnlyForwardAdjointLocalization
public import SphericalAging.SphereOnlyFisherCurrent
public import SphericalAging.SphereQuenchedFDT
public import SphericalAging.SphereSpatialGeneratorRegularity

public section

/-! Genuine causal FDT derivatives from spatial C² slices and true time
equations only on positive times and on the physical sphere. No ambient
mixed time-space smoothness or global density positivity is assumed. -/
noncomputable section
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.SphereOnlyOnSphereFDT
open MeasureTheory Set Filter
open scoped Topology BigOperators
open FiniteModel SphereInitialLaw HardSphereDynamics SphericalIntegrationByParts SphereEntropyDissipation
open SphereGeneratorIntegrationByParts SphereGeneratorRegularity SphereFiniteFDT SphereQuenchedFDT
open SphereGeneratorAlgebra
open SphereFDTAlgebra
open SphereCoordinateScore SphereFisherCurrent SphereRotationGeometry SphereCanonicalEntropy
open SphereOnlyParameterIntegral SphereOnlyLocalParameterIntegral SphereOnlyGeneratorFDTLocalization
open SphereOnlyForwardAdjointLocalization SphereOnlySpatialLocalization SphereOnlyGeneratorLocalization
open SphereOnlyFisherCurrent SmoothPositiveSpatialReplacement

theorem single_component_fdt_hasDerivAt_onSphere {N p : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    (hA : ∀ i,star (A i)=-A i) {ρ ρdot m : ℝ → Vector N → ℝ} {φ : Vector N → ℝ}
    (hρ : Continuous (Function.uncurry ρ)) (hspace : ∀v,ContDiff ℝ 2 (ρ v))
    (hdot : Continuous (Function.uncurry ρdot))
    (hderiv : ∀v,0<v→∀x,OnSphere x→HasDerivAt (fun w => ρ w x) (ρdot v x) v)
    (hm : Continuous (Function.uncurry m))
    (hslices : ∀v,ContDiff ℝ 2 (m v))
    (hgen : Continuous (fun z : ℝ × Vector N => rotationGenerator κ β J A (m z.1) z.2))
    (hφ : ContDiff ℝ 2 φ)
    (hback : ∀ v,0<v → ∀ x,OnSphere x → HasDerivAt (fun w => m w x) (rotationGenerator κ β J A (m v) x) v)
    {t s : ℝ} (hs : 0<s) (hst : s<t) (hpos : ∀x,OnSphere x→0<ρ s x)
    (hPDE : ∀ x,OnSphere x → ρdot s x=forwardDensitySlope κ β J A (ρ s) x) :
    HasDerivAt (fun v => correlationPairing ρ φ m t v)
      ((∫ x : Vector N,ρ s x*rotationGamma κ A φ (m (t-s)) x ∂sphereLaw N)-
        (∫ x : Vector N,ρ s x*m (t-s) x*rotationGamma κ A (relativeLog β J (ρ s)) φ x
          ∂sphereLaw N)) s := by
  let δ := min (s/2) ((t-s)/2)
  have hδ : 0<δ := lt_min (by linarith) (by linarith)
  have hδs : δ≤s/2 := min_le_left _ _
  have hδt : δ≤(t-s)/2 := min_le_right _ _
  let F (v : ℝ) (x : Vector N) := ρ v x*φ x*m (t-v) x
  let F' (v : ℝ) (x : Vector N) :=
    ρdot v x*φ x*m (t-v) x-ρ v x*φ x*rotationGenerator κ β J A (m (t-v)) x
  have hcomp : Continuous (fun z : ℝ × Vector N => (t-z.1,z.2)) :=
    (continuous_const.sub continuous_fst).prodMk continuous_snd
  have hmc := hm.comp hcomp
  have hLc := hgen.comp hcomp
  have hφc := hφ.continuous.comp (continuous_snd : Continuous (fun z : ℝ × Vector N => z.2))
  have hFc : Continuous (Function.uncurry F) := (hρ.mul hφc).mul hmc
  have hF'c : Continuous (Function.uncurry F') :=
    ((hdot.mul hφc).mul hmc).sub ((hρ.mul hφc).mul hLc)
  have hD v (hv : v ∈ Icc (s-δ) (s+δ)) (x : Vector N) (hx : OnSphere x) :
      HasDerivAt (fun w => F w x) (F' v x) v := by
    have hvpos : 0<v := by linarith [hv.1]
    have hlag : 0<t-v := by linarith [hv.2]
    have hd := (hback (t-v) hlag x hx).comp v ((hasDerivAt_const v t).sub (hasDerivAt_id v))
    have hh := ((hderiv v hvpos x hx).mul_const (φ x)).mul hd
    convert hh using 1
    · rfl
    · dsimp only [F',Function.comp_def]
      ring
  have hh := hasDerivAt_integral_of_sphere_derivative hN hFc hF'c
    (by linarith : s-δ<s) (by linarith : s<s+δ) hD
  have hρs : ContDiff ℝ 2 (ρ s) := hspace s
  have hms : ContDiff ℝ 2 (m (t-s)) := hslices (t-s)
  have hφm := hφ.mul hms
  have hfirst : (∫ x : Vector N,ρdot s x*φ x*m (t-s) x ∂sphereLaw N)=
      (∫ x : Vector N,ρ s x*rotationGenerator κ β J A (fun y => φ y*m (t-s) y) x ∂sphereLaw N) := by
    rw [← forward_density_adjoint_onSphere hN κ β J A hA hρs hpos hφm]
    apply integral_congr_ae
    filter_upwards [sphereLaw_support hN] with x hx
    rw [hPDE x ((onSphere_iff_norm_sq x).mpr hx)]
    ring
  have hi₀ := continuous_sphere_integrable hN
    (((hdot.comp (continuous_const.prodMk continuous_id : Continuous (fun x : Vector N => (s,x)))).mul
      hφ.continuous).mul hms.continuous)
  have hi₁ := continuous_sphere_integrable hN
    ((hρs.continuous.mul hφ.continuous).mul (rotationGenerator_continuous κ β J A hms))
  have hi₂ := continuous_sphere_integrable hN
    (hρs.continuous.mul (rotationGenerator_continuous κ β J A hφm))
  have he : (∫ x : Vector N,F' s x ∂sphereLaw N)=
      ((∫ x : Vector N,ρ s x*rotationGamma κ A φ (m (t-s)) x ∂sphereLaw N)-
        (∫ x : Vector N,ρ s x*m (t-s) x*rotationGamma κ A (relativeLog β J (ρ s)) φ x
          ∂sphereLaw N)) := by
    dsimp only [F']
    rw [integral_sub (f := fun x : Vector N => ρdot s x*φ x*m (t-s) x)
      (g := fun x => ρ s x*φ x*rotationGenerator κ β J A (m (t-s)) x) hi₀ hi₁,hfirst]
    rw [← integral_sub (f := fun x : Vector N => ρ s x*
      rotationGenerator κ β J A (fun y => φ y*m (t-s) y) x)
      (g := fun x => ρ s x*φ x*rotationGenerator κ β J A (m (t-s)) x) hi₂ hi₁]
    have hfun : (fun x : Vector N => ρ s x*rotationGenerator κ β J A (fun y => φ y*m (t-s) y) x-
        ρ s x*φ x*rotationGenerator κ β J A (m (t-s)) x)=
        (fun x => ρ s x*(rotationGenerator κ β J A (fun y => φ y*m (t-s) y) x-
          φ x*rotationGenerator κ β J A (m (t-s)) x)) := by funext x;ring
    rw [hfun]
    exact generator_fdt_bracket_onSphere hN κ β J A hA (hρs.of_le (by norm_num)) hpos hφ hms
  rw [he] at hh
  exact hh


/-- Supported spatial localization identifies the genuine vector current. -/
theorem coordinate_integrated_current_onSphere {N p : ℕ} (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : Vector N→ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀x,OnSphere x→0<ρ x) {m : Vector N→Vector N} (hm : Continuous m) :
    (∑i : Fin N,∫x : Vector N,ρ x*m x i*rotationGamma (1/(2*(N:ℝ))) (canonicalRotations N)
      (relativeLog β J ρ) (coordinateObservable i) x ∂sphereLaw N)/(N:ℝ)=
      currentDefect β J ρ m := by
  classical
  obtain ⟨g,hg,hgpos,hnear⟩ := exists_positive_near_sphere hρ hpos
  have hh := coordinate_integrated_current hN β J hg hgpos hm
  have he (i : Fin N) :
      (∫x : Vector N,g x*m x i*rotationGamma (1/(2*(N:ℝ))) (canonicalRotations N)
        (relativeLog β J g) (coordinateObservable i) x ∂sphereLaw N)=
      (∫x : Vector N,ρ x*m x i*rotationGamma (1/(2*(N:ℝ))) (canonicalRotations N)
        (relativeLog β J ρ) (coordinateObservable i) x ∂sphereLaw N) := by
    apply integral_congr_ae
    filter_upwards [physicalSphere_ae hN] with x hx
    rw [(hnear x hx).eq_of_nhds,
      (rotationGamma_eventuallyEq (1/(2*(N:ℝ))) (canonicalRotations N)
        (relativeLog_eventuallyEq β J (hnear x hx)) EventuallyEq.rfl).eq_of_nhds]
  simp_rw [he] at hh
  rwa [currentDefect_eq_of_near hN β J m hnear] at hh

/-- Causal vector FDT from the true positive-time sphere forward/backward equations. -/
theorem quenched_fdt_hasDerivAt_onSphere {N p : ℕ} (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ ρdot : ℝ→Vector N→ℝ} {m : ℝ→Vector N→Vector N}
    (hρ : Continuous (Function.uncurry ρ)) (hspace : ∀v,ContDiff ℝ 2 (ρ v))
    (hdot : Continuous (Function.uncurry ρdot))
    (hderiv : ∀v,0<v→∀x,OnSphere x→HasDerivAt (fun w => ρ w x) (ρdot v x) v)
    (hm : Continuous (Function.uncurry m)) (hslices : ∀v,ContDiff ℝ 2 (m v))
    (hgen : ∀i : Fin N,Continuous (fun z : ℝ×Vector N => rotationGenerator (1/(2*(N:ℝ)))
      β J (canonicalRotations N) (fun y => m z.1 y i) z.2))
    (hback : ∀i : Fin N,∀v,0<v→∀x,OnSphere x→HasDerivAt (fun w => m w x i)
      (rotationGenerator (1/(2*(N:ℝ))) β J (canonicalRotations N) (fun y => m v y i) x) v)
    {t s : ℝ} (hs : 0<s) (hst : s<t) (hpos : ∀x,OnSphere x→0<ρ s x)
    (hPDE : ∀x,OnSphere x→ρdot s x=sphericalForwardDensitySlope β J (ρ s) x) :
    HasDerivAt (fun v => quenchedCorrelation ρ m t v)
      (quenchedResponse ρ m t s-currentDefect β J (ρ s) (m (t-s))) s := by
  classical
  have hmcoord (i : Fin N) : Continuous (Function.uncurry (fun τ x => m τ x i)) :=
    (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin N => ℝ) i).continuous.comp hm
  have hmrow (i : Fin N) (v : ℝ) : ContDiff ℝ 2 (fun x => m v x i) :=
    (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin N => ℝ) i).contDiff.comp (hslices v)
  have hmrowc : Continuous (m (t-s)) :=
    hm.comp (show Continuous (fun x : Vector N => (t-s,x)) from continuous_const.prodMk continuous_id)
  have hc i := single_component_fdt_hasDerivAt_onSphere hN (1/(2*(N:ℝ))) β J (canonicalRotations N)
    (fun ij => coordinateRotation_skew ij.1 ij.2) hρ hspace hdot hderiv (hmcoord i) (hmrow i) (hgen i)
    ((coordinateObservable_contDiff i).of_le (by simp)) (hback i) hs hst hpos hPDE
  have hd := (HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => hc i)).div_const (N:ℝ)
  simp only [Finset.sum_sub_distrib,sub_div] at hd
  rw [coordinate_integrated_current_onSphere hN β J (hspace s) hpos hmrowc] at hd
  exact hd

end SphericalAging.SphereOnlyOnSphereFDT
