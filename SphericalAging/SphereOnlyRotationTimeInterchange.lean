module

public import SphericalAging.CompactIntervalParameterDerivative
public import SphericalAging.SphereSpatialGeneratorRegularity

public section

/-! Intrinsic time/rotation interchange from the actual sphere equation.
The proof uses the fundamental theorem of calculus along time and genuine
rotation curves. Ambient time differentiability is never assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SphericalAging.SphereOnlyRotationTimeInterchange
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphericalIntegrationByParts SphereSpatialGeneratorRegularity
open CompactIntervalParameterDerivative
open scoped Topology
variable {N : ℕ}

theorem operatorFlow_mem_physicalSphere (A : Operator N) (hA : star A=-A)
    {x : Vector N} (hx : x∈physicalSphere N) (t : ℝ) :
    operatorFlow A t x∈physicalSphere N := by
  apply (onSphere_iff_norm_sq _).mpr
  rw [operatorFlow_norm A hA t x]
  exact (onSphere_iff_norm_sq x).mp hx

theorem lieDerivative_time_integral (A : Operator N) (hA : star A=-A)
    {ρ ρdot : ℝ→Vector N→ℝ}
    (hρ : Continuous (Function.uncurry ρ))
    (hdot : Continuous (Function.uncurry ρdot))
    (hDdot : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρdot z.1) z.2))
    (hspace : ∀t,ContDiff ℝ 1 (ρ t)) (hdotSpace : ∀t,ContDiff ℝ 1 (ρdot t))
    (hd : ∀t,0<t→∀x,x∈physicalSphere N→HasDerivAt (fun s => ρ s x) (ρdot t x) t)
    {a t : ℝ} (ha : 0<a) (hat : a≤t) {x : Vector N} (hx : x∈physicalSphere N) :
    lieDerivative A (ρ t) x=lieDerivative A (ρ a) x+
      ∫u in a..t,lieDerivative A (ρdot u) x := by
  have hflow : Continuous (fun θ : ℝ => operatorFlow A θ x) :=
    (operatorFlow_continuous A).clm_apply continuous_const
  have hLd := joint_lieDerivative_continuous A hDdot
  let F := fun θ u : ℝ => ρdot u (operatorFlow A θ x)
  let F' := fun θ u : ℝ => lieDerivative A (ρdot u) (operatorFlow A θ x)
  have hFc : Continuous (Function.uncurry F) :=
    hdot.comp (continuous_snd.prodMk (hflow.comp continuous_fst))
  have hF'c : Continuous (Function.uncurry F') :=
    hLd.comp (continuous_snd.prodMk (hflow.comp continuous_fst))
  have hI := hasDerivAt_intervalIntegral hFc hF'c (θ:=0) hat
    (fun u _ θ => flow_function_hasDerivAt A (hdotSpace u) θ x)
  have he (θ : ℝ) : (∫u in a..t,F θ u)=
      ρ t (operatorFlow A θ x)-ρ a (operatorFlow A θ x) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro u hu
      rw [uIcc_of_le hat] at hu
      exact hd u (ha.trans_le hu.1) _ (operatorFlow_mem_physicalSphere A hA hx θ)
    · exact (hdot.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a t
  have hI' := hI.congr_of_eventuallyEq (Eventually.of_forall fun θ => (he θ).symm)
  have hR := (flow_function_hasDerivAt A (hspace t) 0 x).sub
    (flow_function_hasDerivAt A (hspace a) 0 x)
  have hh := hR.unique hI'
  simp only [F',operatorFlow_zero] at hh
  linarith only [hh]

theorem lieDerivative_time_hasDerivAt (A : Operator N) (hA : star A=-A)
    {ρ ρdot : ℝ→Vector N→ℝ}
    (hρ : Continuous (Function.uncurry ρ))
    (hdot : Continuous (Function.uncurry ρdot))
    (hDdot : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρdot z.1) z.2))
    (hspace : ∀t,ContDiff ℝ 1 (ρ t)) (hdotSpace : ∀t,ContDiff ℝ 1 (ρdot t))
    (hd : ∀t,0<t→∀x,x∈physicalSphere N→HasDerivAt (fun s => ρ s x) (ρdot t x) t)
    {t₀ : ℝ} (ht₀ : 0<t₀) {x : Vector N} (hx : x∈physicalSphere N) :
    HasDerivAt (fun t => lieDerivative A (ρ t) x) (lieDerivative A (ρdot t₀) x) t₀ := by
  let a := t₀/2
  have ha : 0<a := by dsimp [a];linarith
  have hat : a<t₀ := by dsimp [a];linarith
  have hG : Continuous (fun u : ℝ => lieDerivative A (ρdot u) x) :=
    (joint_lieDerivative_continuous A hDdot).comp (continuous_id.prodMk continuous_const)
  have hI := intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable a t₀)
    hG.stronglyMeasurable.stronglyMeasurableAtFilter hG.continuousAt
  have hI' : HasDerivAt (fun t => lieDerivative A (ρ a) x+
      ∫u in a..t,lieDerivative A (ρdot u) x) (lieDerivative A (ρdot t₀) x) t₀ := by
    simpa only [zero_add] using (hasDerivAt_const t₀ (lieDerivative A (ρ a) x)).fun_add hI
  apply hI'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hat] with t ht
  exact lieDerivative_time_integral A hA hρ hdot hDdot hspace hdotSpace hd ha ht.le hx

end SphericalAging.SphereOnlyRotationTimeInterchange
