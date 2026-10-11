module

public import SphericalAging.SphereFisherTimeDerivative
public import SphericalAging.ResponseTransport

public section

/-! Genuine finite quenched integrated FDT from the actual density and backward
mean PDEs. The diagonal, FTC and interval Cauchy bound are all derived. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereIntegratedFDT

open MeasureTheory Set FiniteModel SphereInitialLaw HardSphereDynamics
open SphericalIntegrationByParts SphereEntropyDissipation SphereEntropyBudget
open SphereRotationGeometry SphereFisherCurrent SphereGeneratorIntegrationByParts
open SphereQuenchedFDT SphereFisherTimeDerivative SphereCoordinateScore
open scoped Topology BigOperators InnerProductSpace

theorem joint_tangentScore_continuous {N p : ℕ} (β : ℝ) (J : Disorder N p)
    {ρ : ℝ → Vector N → ℝ} (hρ : ContDiff ℝ 2 (Function.uncurry ρ))
    (hpos : ∀ t x,0<ρ t x) :
    Continuous (fun z : ℝ × Vector N => tangentScore β J (ρ z.1) z.2) := by
  have hψ : ContDiff ℝ 2 (Function.uncurry (fun t => relativeLog β J (ρ t))) :=
    ((hρ.log (fun z => (hpos z.1 z.2).ne')).sub
      (contDiff_const.mul (((Hamiltonian_contDiff J).of_le (by simp)).comp contDiff_snd))).add contDiff_const
  have hpartial : ContDiff ℝ 2 (Function.uncurry
      (fun z : ℝ × Vector N => fun x : Vector N => relativeLog β J (ρ z.1) x)) :=
    hψ.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hfd : ContDiff ℝ 1 (fun z : ℝ × Vector N =>
      fderiv ℝ (relativeLog β J (ρ z.1)) z.2) := hpartial.fderiv contDiff_snd (by norm_num)
  have hg : Continuous (fun z : ℝ × Vector N => gradient (relativeLog β J (ρ z.1)) z.2) :=
    (InnerProductSpace.toDual ℝ (Vector N)).symm.continuous.comp hfd.continuous
  unfold tangentScore projection
  exact hg.sub (((continuous_snd.inner hg).div_const (N : ℝ)).smul continuous_snd)

theorem currentDefect_row_continuous {N p : ℕ} (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : ℝ → Vector N → ℝ} {m : ℝ → Vector N → Vector N}
    (hρ : ContDiff ℝ 2 (Function.uncurry ρ)) (hpos : ∀ v x,0<ρ v x)
    (hm : Continuous (Function.uncurry m)) (t : ℝ) :
    Continuous (fun s => currentDefect β J (ρ s) (m (t-s))) := by
  unfold currentDefect
  apply Continuous.div_const
  apply continuous_sphere_parameter_integral hN
  exact hρ.continuous.mul
    ((hm.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)).inner
      (joint_tangentScore_continuous β J hρ hpos))

theorem quenchedCorrelation_row_continuous {N : ℕ} (hN : 0<N)
    {ρ : ℝ → Vector N → ℝ} {m : ℝ → Vector N → Vector N}
    (hρ : Continuous (Function.uncurry ρ)) (hm : Continuous (Function.uncurry m)) (t : ℝ) :
    Continuous (fun s => quenchedCorrelation ρ m t s) := by
  have heq : (fun s => quenchedCorrelation ρ m t s)=
      (fun s => (∫ x : Vector N,ρ s x*⟪x,m (t-s) x⟫_ℝ ∂sphereLaw N)/(N : ℝ)) := by
    funext s
    exact quenchedCorrelation_eq_inner hN hρ hm t s
  rw [heq]
  apply Continuous.div_const
  apply continuous_sphere_parameter_integral hN
  exact hρ.mul (continuous_snd.inner
    (hm.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)))

theorem quenchedResponse_row_continuous {N : ℕ} (hN : 0<N)
    {ρ : ℝ → Vector N → ℝ} {m : ℝ → Vector N → Vector N}
    (hρ : Continuous (Function.uncurry ρ)) (hm : ContDiff ℝ 2 (Function.uncurry m)) (t : ℝ) :
    Continuous (fun s => quenchedResponse ρ m t s) := by
  classical
  unfold quenchedResponse
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  apply continuous_sphere_parameter_integral hN
  have hφ : ContDiff ℝ 2 (Function.uncurry (fun _ : ℝ => coordinateObservable i)) :=
    ((SphereCoordinateScore.coordinateObservable_contDiff i).of_le (by simp)).comp contDiff_snd
  have hmcoord : ContDiff ℝ 2 (Function.uncurry (fun s x => m (t-s) x i)) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).contDiff.comp
      (hm.comp ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd))
  exact hρ.mul (joint_rotationGamma_continuous (1/(2*(N : ℝ))) (canonicalRotations N) hφ hmcoord)

theorem quenchedCorrelation_diagonal {N : ℕ} (hN : 0<N)
    {ρ : ℝ → Vector N → ℝ} {m : ℝ → Vector N → Vector N}
    (hρ : Continuous (Function.uncurry ρ)) (hm : Continuous (Function.uncurry m))
    (hinit : ∀ x,m 0 x=x) (t : ℝ) (hmass : (∫ x : Vector N,ρ t x ∂sphereLaw N)=1) :
    quenchedCorrelation ρ m t t=1 := by
  rw [quenchedCorrelation_eq_inner hN hρ hm t t]
  have heq : (∫ x : Vector N,ρ t x*⟪x,m (t-t) x⟫_ℝ ∂sphereLaw N)=
      (N : ℝ)*(∫ x : Vector N,ρ t x ∂sphereLaw N) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [sphereLaw_support hN] with x hx
    simp only [sub_self,hinit,real_inner_self_eq_norm_sq,hx]
    ring
  rw [heq,hmass,mul_one,div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))]

/-- Actual density/mean equations give the full signed integrated current formula.
The correlation diagonal follows from mass and m0=id; the off-diagonal derivative
is integrated using the genuine endpoint FTC. -/
theorem quenched_integrated_fdt_current {N p : ℕ} (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ ρdot : ℝ → Vector N → ℝ} {m : ℝ → Vector N → Vector N}
    (hρ : ContDiff ℝ 2 (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hderiv : ∀ v x,HasDerivAt (fun w => ρ w x) (ρdot v x) v)
    (hpos : ∀ v x,0<ρ v x) (hinitρ : ∀ x,ρ 0 x=1)
    (hm : ContDiff ℝ 2 (Function.uncurry m)) (hinitm : ∀ x,m 0 x=x)
    (hback : ∀ i : Fin N,∀ v,0<v → ∀ x,HasDerivAt (fun w => m w x i)
      (SphereGeneratorIntegrationByParts.rotationGenerator (1/(2*(N : ℝ))) β J
        (canonicalRotations N) (fun y => m v y i) x) v)
    (hPDE : ∀ v,0≤v → ∀ x,ρdot v x=SphereCanonicalEntropy.sphericalForwardDensitySlope β J (ρ v) x)
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    1-quenchedCorrelation ρ m t s-(∫ u in s..t,quenchedResponse ρ m t u)=
      -(∫ u in s..t,currentDefect β J (ρ u) (m (t-u))) := by
  have hC := quenchedCorrelation_row_continuous hN hρ.continuous hm.continuous t
  have hR := quenchedResponse_row_continuous hN hρ.continuous hm t
  have hD := currentDefect_row_continuous hN β J hρ hpos hm.continuous t
  have hder u (hu : u ∈ Ioo s t) := quenched_fdt_hasDerivAt hN β J hρ hdot hderiv hm hback
    hu.2 (hpos u) (hPDE u (by linarith [hu.1]))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hC.continuousOn hder
    ((hR.sub hD).intervalIntegrable s t)
  have ht : 0≤t := hs.trans hst
  have hmass := density_mass_one hN (1/(2*(N : ℝ))) β J (canonicalRotations N)
    (fun ij => coordinateRotation_skew ij.1 ij.2) hρ hdot hderiv hinitρ ht
    (fun v hv => hPDE v hv.1)
  rw [quenchedCorrelation_diagonal hN hρ.continuous hm.continuous hinitm t hmass,
    intervalIntegral.integral_sub (hR.intervalIntegrable s t) (hD.intervalIntegrable s t)] at hFTC
  linarith only [hFTC]

/-- The actual finite quenched integrated FDT defect has its true Fisher budget.
No integrated-FDT or Fisher-domination premise is supplied. -/
theorem quenched_integrated_fdt_fisher_bound {N p : ℕ} (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ ρdot : ℝ → Vector N → ℝ} {m : ℝ → Vector N → Vector N}
    (hρ : ContDiff ℝ 2 (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hderiv : ∀ v x,HasDerivAt (fun w => ρ w x) (ρdot v x) v)
    (hpos : ∀ v x,0<ρ v x) (hinitρ : ∀ x,ρ 0 x=1)
    (hm : ContDiff ℝ 2 (Function.uncurry m)) (hinitm : ∀ x,m 0 x=x)
    (hback : ∀ i : Fin N,∀ v,0<v → ∀ x,HasDerivAt (fun w => m w x i)
      (rotationGenerator (1/(2*(N : ℝ))) β J (canonicalRotations N) (fun y => m v y i) x) v)
    (hPDE : ∀ v,0≤v → ∀ x,ρdot v x=SphereCanonicalEntropy.sphericalForwardDensitySlope β J (ρ v) x)
    (hmean : ∀ v,0≤v → ∀ x,OnSphere x → ‖m v x‖^2 ≤ (N : ℝ))
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    (1-quenchedCorrelation ρ m t s-(∫ u in s..t,quenchedResponse ρ m t u))^2 ≤
      (t-s)*(∫ u in s..t,fisherInformation β J (ρ u)/(N : ℝ)) := by
  rw [quenched_integrated_fdt_current hN β J hρ hdot hderiv hpos hinitρ hm hinitm hback hPDE hs hst,
    neg_sq]
  rcases hst.eq_or_lt with heq | hlt
  · subst t
    simp
  have hD := currentDefect_row_continuous hN β J hρ hpos hm.continuous t
  have hFI : Continuous (fun u => fisherInformation β J (ρ u)/(N : ℝ)) := by
    have heq : (fun u => fisherInformation β J (ρ u))=(fun u =>
        rotationFisher (1/(2*(N : ℝ))) β J (canonicalRotations N) (ρ u)) := by
      funext u
      symm
      apply rotationFisher_eq_tangent hN β J
      · simpa only [Function.comp_def,Function.uncurry,id_eq] using
          hρ.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : Vector N => (u,x)))
      · exact hpos u
    have hFC : Continuous (fun u => fisherInformation β J (ρ u)) := by
      rw [heq]
      exact rotationFisher_continuous hN (1/(2*(N : ℝ))) β J (canonicalRotations N) hρ hpos
    exact hFC.div_const _
  have hpoint u (hu : u ∈ Icc s t) : (currentDefect β J (ρ u) (m (t-u)))^2 ≤
      fisherInformation β J (ρ u)/(N : ℝ) := by
    have hu0 : 0≤u := hs.trans hu.1
    have hmass := density_mass_one hN (1/(2*(N : ℝ))) β J (canonicalRotations N)
      (fun ij => coordinateRotation_skew ij.1 ij.2) hρ hdot hderiv hinitρ hu0
      (fun v hv => hPDE v hv.1)
    apply currentDefect_fisher_bound hN β J _ (hpos u) hmass
      (hm.continuous.comp (continuous_const.prodMk continuous_id)) (hmean (t-u) (by linarith [hu.2]))
    simpa only [Function.comp_def,Function.uncurry,id_eq] using
      hρ.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : Vector N => (u,x)))
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hst ((hD.pow 2).intervalIntegrable s t)
    (hFI.intervalIntegrable s t) hpoint
  exact (ResponseTransport.interval_square_bound hlt (hD.intervalIntegrable s t)
    ((hD.pow 2).intervalIntegrable s t)).trans
      (mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hst))

end SphericalAging.SphereIntegratedFDT
