module

public import SphericalAging.SphereActualWaitingCurrent
public import SphericalAging.SphereActualMeanFisherChain
public import SphericalAging.FisherIncrementIntegralBound

public section

/-! Complete local source 5.5: the sharp actual mean derivative, the actual
waiting observable gradient and exact density current, and the dimension
limit shift estimate with the integral of the square root of the extracted
Fisher clock. The positive density and preceding CK dimension limits remain
explicit analytic inputs. No gradient, current or shift estimate is assumed. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace SphericalAging.SphereWaitingTheorem
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open FiniteModel HardSphereDynamics ActualSphereTransition SphereInitialLaw
open PhysicalVariationalBounds LandscapeDerivatives
open SphereFisherHelly SphereOnSphereCurrent SphereActualWaitingCurrent
open SphereSharpMeanGradient SphereActualMeanFisherChain SphereWaitingLimitTransfer
open SphereEnergyLimitTransfer SphereGoodEventFisherClock SphereBadEventFisherMass
open CKSpecification StrongBackwardDefect SphereCKFisherMajorant
open CKUniformLateEstimates FisherLimitLocalBounds FisherIncrementIntegralBound
open SphereAnnealedCurrentFDT (rowPrimitive)
open scoped Topology NNReal InnerProductSpace
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

structure FiniteConclusions (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (E : FisherDensity N p β) : Prop where
  mean_gradient : ∀J : Disorder N p,∀τ : ℝ≥0,∀x : State N,OnSphere x →
    ‖(fderiv ℝ (mean (NullAugmentation.driver D₀) β R hR J τ) x).comp (tangentProjection x)‖≤
      Real.exp ((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J*(τ:ℝ))
  waiting_gradient : ∀J : Disorder N p,∀τ : ℝ≥0,∀x : State N,OnSphere x →
    ‖projection x (gradient (actualWaitingObservable D₀ β R hR J τ) x)‖≤
      (1+Real.exp ((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J*(τ:ℝ)))/Real.sqrt N
  waiting_current : ∀J : Disorder N p,∀τ : ℝ≥0,∀w : ℝ,0≤w →
    HasDerivAt (actualWaitingCorrelation D₀ β R hR E J τ)
      (actualWaitingCurrent D₀ β R hR E J τ w) w
  current_fisher : ∀J : Disorder N p,∀τ : ℝ≥0,∀w : ℝ,0≤w →
    (actualWaitingCurrent D₀ β R hR E J τ w)^2≤
      (1+Real.exp ((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J*(τ:ℝ)))^2*
        (SphereRotationGeometry.fisherInformation β J (E.ρ J w)/(N:ℝ))

theorem source5_5_finite (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (E : FisherDensity N p β) :
    FiniteConclusions D₀ β R hR E := by
  refine ⟨?_,?_,?_,?_⟩
  · intro J τ x hx
    simpa only [mul_assoc] using actual_mean_projected_operator_bound hN hp D₀ β R hR hNR J x hx τ
  · exact fun J τ x hx => actualWaitingObservable_gradient_bound hN hp D₀ β R hR hNR J τ x hx
  · exact fun J τ w hw => actualWaitingCorrelation_hasDerivAt hN D₀ β R hR E J τ hw
  · exact fun J τ w hw => actualWaitingCurrent_square_bound hN hp D₀ β R hR hNR E J τ hw

theorem quenched_waiting_hasDerivAt_actual_current (hN : 0<N)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (E : FisherDensity N p β) (M : SphereBackwardMean N p β)
    (J : Disorder N p) (τ : ℝ≥0) {w : ℝ} (hw : 0≤w)
    (heq : ∀x,OnSphere x → M.m J τ x=mean (NullAugmentation.driver D₀) β R hR J τ x) :
    HasDerivAt (fun v => SphereQuenchedFDT.quenchedCorrelation (E.ρ J) (M.m J) (v+(τ:ℝ)) v)
      (actualWaitingCurrent D₀ β R hR E J τ w) w := by
  have hd := actualWaitingCorrelation_hasDerivAt hN D₀ β R hR E J τ hw
  have he : actualWaitingCorrelation D₀ β R hR E J τ=
      fun v => SphereQuenchedFDT.quenchedCorrelation (E.ρ J) (M.m J) (v+(τ:ℝ)) v := by
    funext v
    exact actualWaitingCorrelation_eq_quenched hN D₀ β R hR E M J τ v heq
  rw [he] at hd
  exact hd

structure LimitConclusions (d : CKData) (a : ℝ→ℝ) (B : ℝ→ℝ) : Prop where
  waiting_absolute_continuity : ∀L τ T : ℝ,0≤L → 0≤τ → τ≤L → 0≤T →
    AbsolutelyContinuousOnInterval (fun s => d.C (s+τ) s) 0 T
  waiting_integral_bound : ∀L τ u v : ℝ,0≤L → 0≤τ → τ≤L → 0≤u → u≤v →
    |d.C (v+τ) v-d.C (u+τ) u|≤B L*(∫s in u..v,Real.sqrt (a s))
  shift_integral_bound : ∀L t s θ : ℝ,0≤L → 0≤s → s≤t → t-s≤L → 0≤θ →
    |d.C (t+θ) (s+θ)-d.C t s|≤B L*(∫u in s..(s+θ),Real.sqrt (a u))

theorem limit_conclusions_of_clock {d : CKData} {a : ℝ→ℝ} {B : ℝ→ℝ}
    (hw : WaitingControl d a B) (hi : IntegrableOn a (Ioi 0)) (han : ∀s,0≤a s)
    (hB : ∀L,0≤L → 0≤B L) (hac : ∀s,ContinuousWithinAt a (Ici s) s)
    {K : ℝ} (hK : 0≤K) (hclock : Antitone (fun s => Real.exp (-K*s)*a s)) :
    LimitConclusions d a B := by
  have hlocal := locally_bounded_on_ray hK han (hclock.antitoneOn (Ici 0))
  have hb : ∀T : ℝ,0≤T → ∃M : ℝ,0≤M ∧ ∀s∈Icc 0 T,a s≤M := by
    intro T hT
    obtain ⟨M,hM,hh⟩ := hlocal T hT
    exact ⟨M,hM,fun s hs => (le_abs_self _).trans (hh s hs)⟩
  have ham := stronglyMeasurable_of_exponential_clock hclock
  have hInt : ∀L τ u v : ℝ,0≤L → 0≤τ → τ≤L → 0≤u → u≤v →
      |d.C (v+τ) v-d.C (u+τ) u|≤B L*(∫s in u..v,Real.sqrt (a s)) := by
    intro L τ u v hL hτ hτL hu huv
    exact waiting_integral_sqrt_bound hw hi han hB hb ham hac hL hτ hτL hu huv
  refine ⟨?_,hInt,?_⟩
  · intro L τ T hL hτ hτL hT
    exact FisherIncrementRegularity.absolutelyContinuous_of_increment_control
      (hw L hL τ hτ hτL) hi (hB L hL) hT (hb T hT)
  · intro L t s θ hL hs hst hLag hθ
    have hh := hInt L (t-s) s (s+θ) hL (sub_nonneg.mpr hst) hLag hs (by linarith)
    have hv : s+θ+(t-s)=t+θ := by ring
    have hu : s+(t-s)=t := by ring
    simpa only [hv,hu] using hh

theorem source5_5_from_density_and_dimension_limits {p : ℕ} {β : ℝ≥0} {d : CKData}
    (h : CKEquations p β d)
    (dim : ℕ→ℕ) (hDim : ∀n,2≤dim n) (hTop : Tendsto dim atTop atTop)
    (radius : ℕ→ℝ≥0) (hR : ∀n,0<(radius n:ℝ))
    (hNR : ∀n,(dim n:ℝ)<(radius n:ℝ)^2)
    (E : ∀n,FisherDensity (dim n) p β) (M : ∀n,SphereBackwardMean (dim n) p β)
    (hmean : ∀n J τ,0≤τ → ∀x,OnSphere x → (M n).m J τ x=
      mean (NullAugmentation.driver (VectorBrownian.driver (dim n))) β (radius n) (hR n) J τ.toNNReal x)
    (hmeas : ∀n t s,AEStronglyMeasurable
      (fun J => rowPrimitive ((E n).ρ J) ((M n).m J) t s) (disorderLaw (dim n) p))
    (hlimit : ∀t s,0≤s → s≤t → Tendsto (fun n => annealedRowPrimitive (E n) (M n) t s)
      atTop (𝓝 (ckRowPrimitive d t s)))
    (hemeas : ∀n t,AEStronglyMeasurable
      (fun J => SphereEnergyCurrent.energy (E n) J t) (disorderLaw (dim n) p))
    (helimit : ∀t,0≤t → Tendsto (fun n => annealedEnergy (E n) t)
      atTop (𝓝 (CKSpecification.energy p β d t)))
    (hcmeas : ∀n τ,0≤τ → ∀s,0≤s → AEStronglyMeasurable
      (fun J => SphereQuenchedFDT.quenchedCorrelation ((E n).ρ J) ((M n).m J) (s+τ) s)
        (disorderLaw (dim n) p))
    (hclimit : ∀τ,0≤τ → ∀s,0≤s → Tendsto
      (fun n => annealedCorrelation (E n) (M n) (s+τ) s) atTop (𝓝 (d.C (s+τ) s))) :
    ∃ (χ : ℕ→ℕ) (aF : ℝ→ℝ),StrictMono χ ∧ (∀s,0≤aF s) ∧
      FisherMajorant p β d aF ∧ (∫s in Ioi 0,aF s)≤(β:ℝ)^2/2 ∧
      (∀s,ContinuousWithinAt aF (Ici s) s) ∧
      Antitone (fun s => Real.exp (-ceilingRate p β (cutoff p)*s)*aF s) ∧
      (∀A : ℝ,Tendsto (fun n => ∫s in Ioc 0 A,|(E (χ n)).full s-aF s|) atTop (𝓝 0)) ∧
      Tendsto (FisherLimitClockDecay.lateSup aF) atTop (𝓝 0) ∧
      (∀n,FiniteConclusions (VectorBrownian.driver (dim n)) β (radius n) (hR n) (E n)) ∧
      (∀n J,∀τ : ℝ≥0,∀w : ℝ,0≤w →
        HasDerivAt (fun v => SphereQuenchedFDT.quenchedCorrelation ((E n).ρ J) ((M n).m J) (v+(τ:ℝ)) v)
          (actualWaitingCurrent (VectorBrownian.driver (dim n)) β (radius n) (hR n) (E n) J τ w) w) ∧
      LimitConclusions d aF (fun L => 1+Real.exp ((β:ℝ)*(p:ℝ)^2*cutoff p*L)) := by
  obtain ⟨χ,aF,hχ,han,ha,hmass,hac,hclock,hFI,hlate,_,hw⟩ :=
    actual_Fisher_chain_of_mean_dimensions h dim hDim hTop radius hR hNR E M hmean
      hmeas hlimit hemeas helimit hcmeas hclimit
  have hp : 2≤p := by have hh := h.spin_ge_three;omega
  refine ⟨χ,aF,hχ,han,ha,hmass,hac,hclock,hFI,hlate,?_,?_,?_⟩
  · intro n
    exact source5_5_finite (by have hh := hDim n;omega) hp (VectorBrownian.driver (dim n)) β
      (radius n) (hR n) (hNR n) (E n)
  · intro n J τ w hw
    apply quenched_waiting_hasDerivAt_actual_current (by have hh := hDim n;omega)
      (VectorBrownian.driver (dim n)) β (radius n) (hR n) (E n) (M n) J τ hw
    intro x hx
    simpa only [Real.toNNReal_coe] using hmean n J (τ:ℝ) τ.coe_nonneg x hx
  · apply limit_conclusions_of_clock hw ha.integrable han (fun _ _ => by positivity) hac _ hclock
    have hc : 0≤cutoff p := by
      unfold cutoff
      linarith [GaussianLandscape.landscapeThreshold_pos p]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) β.coe_nonneg) (sq_nonneg _)) hc

end SphericalAging.SphereWaitingTheorem
