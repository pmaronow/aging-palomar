module

public import SphericalAging.WaitingAlgorithmOrthogonality
public import SphericalAging.ProfileForkForgettingEventually
public import SphericalAging.RemoteResponseTheorem

public section

/-! The complete local general-spin fixed-wait transfer along an arbitrary
diverging sequence. All actual fork algorithms, energies, projection errors
and normalized saturation are constructed from the precise preceding10.4
input. Only preceding3.3's actual overlap bridge and the proved admissible-algorithm
waiting-state orthogonality estimate remain inputs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
namespace SphericalAging.ActualForkForgettingSequence
open MeasureTheory ProbabilityTheory Filter Set FiniteModel CKSpecification
  WienerForkTransfer ForkSeedCoordinates FiniteForkMoments PhysicalForkWaitingTransfer
  ForkNormalizedEnergy ForkEnergyComparison RandomGaussianPairing RandomVectorBounds
  ForkParameterBounds ForkParameterLimits ProfileCenterEnergy ForkOrderedParameters
  AlgorithmEnergyDeficit ExternalFieldElementaryPenalty
open scoped NNReal ENNReal Topology InnerProductSpace

variable {dim : ℕ→ℕ} {p : ℕ} {β ell e q : ℝ} {c r : ℝ→ℝ}

theorem source10_10_sequence (hp : 3≤p) (hβ : 0<β)
    {d : CKData} (h : CKEquations p β d) (H : Profile c r q) (hq : 0<q) (hq1 : q<1)
    (hell : ell=PlateauAlgebra.multiplier p β q) (he : e=(ell-1)/((p:ℝ)*β))
    (hr : ∀u,0<u→0≤r u) (hm : β^2*PlateauAlgebra.marginalityPolynomial p q=1)
    (hDim : ∀n,1≤dim n) (F : PhysicalForkStanding.Forks dim p β e c r)
    (s : ℝ≥0) (t : ℕ→ℝ) (ht : Tendsto t atTop atTop)
    (hBridge : ∀u : ℝ≥0,s≤u→Tendsto (fun n => expectedOverlap (dim n) p β u s) atTop
      (𝓝 (d.C u s)))
    (hWaiting : WaitingAlgorithmOrthogonality.Input dim p β s) :
    Tendsto (fun n => d.C (t n) s) atTop (𝓝 0) := by
  have hn n : 0<dim n := by have hh := hDim n;omega
  let B (θ : Parameters×ℕ) := F.branches (branches θ.1) (age θ.1)
    (trunkTime t s (age θ.1) θ.2)
  let Q (a : Parameters) := forkNorm c (branches a) (age a)
  let A (θ : Parameters×ℕ) := ForkApproximationSelection.choose F.toForks (branches_positive θ.1)
    (age θ.1) (trunkTime t s (age θ.1) θ.2) (trunkTime_positive t s (age θ.1) θ.2)
    (error θ.1) (error_positive θ.1)
  let μ := WaitingAlgorithmOrthogonality.measure dim p
  let alg θ n := (A θ).output n
  let mean θ n := seededMean (B θ n)
  let wait (θ : Parameters×ℕ) n := seededWaiting (N:=dim n) (p:=p) (K:=branches θ.1) β s
  let γ (θ : Parameters×ℕ) := FiniteForkStanding.energyError dim
    (forkEnergy p β e c r (branches θ.1) (age θ.1)) (B θ)
  let ζ (θ : Parameters×ℕ) := FiniteForkStanding.normError (Q θ.1) (B θ)
  let κ (θ : Parameters×ℕ) := Real.sqrt (ζ θ)/(Q θ.1)
  let f (θ : Parameters×ℕ) := d.C (trunkTime t s (age θ.1) θ.2+age θ.1) s
  have hKn a : 0<branches a := by have hh := branches_positive a;omega
  have hB θ n : ForkJointLaw β (trunkTime t s (age θ.1) θ.2+age θ.1)
      (trunkTime t s (age θ.1) θ.2) (B θ n) :=
    F.branch_law _ _ _ n
  have hQ a : 0<Q a := hq.trans_le
    ((fork_norm_bounds H hr (branches_positive a) (age a).coe_nonneg).1.trans
      (fork_norm_bounds H hr (branches_positive a) (age a).coe_nonneg).2.1)
  have hγ θ : 0≤γ θ := RemoteResponseTheorem.energyError_nonneg hDim hp (hKn θ.1) (hB θ) _
  have hζ θ : 0≤ζ θ := RemoteResponseTheorem.normError_nonneg hDim (hKn θ.1) (hB θ) _
  have hκ θ : 0≤κ θ := div_nonneg (Real.sqrt_nonneg _) (hQ θ.1).le
  have hγlim a : Tendsto (fun n => γ (a,n)) atTop (𝓝 0) := F.energy_limit _
    (branches_positive a) (age a) (trunkTime t s (age a))
      (trunkTime_positive t s (age a)) (trunkTime_tendsto ht s (age a))
  have hκlim a : Tendsto (fun n => κ (a,n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,zero_div] using (F.concentration_limit _ (branches_positive a)
      (age a) (trunkTime t s (age a)) (trunkTime_positive t s (age a))
        (trunkTime_tendsto ht s (age a))).sqrt.div_const (Q a)
  have hAM θ n : MemLp (alg θ n) 2 (μ θ n) := ForkApproximationSelection.output_memLp (A θ) n
  have hAB θ n : ∀ᵐω ∂μ θ n,‖alg θ n ω‖≤Real.sqrt (dim n) :=
    ForkApproximationSelection.output_ball (A θ) n
  have hMM θ n : MemLp (mean θ n) 2 (μ θ n) := seededMean_memLp (hB θ n)
  have hMB θ n : ∀ᵐω ∂μ θ n,‖mean θ n ω‖≤Real.sqrt (dim n) := seededMean_bound (hKn θ.1) (hB θ n)
  have hWM θ n : MemLp (wait θ n) 2 (μ θ n) := seededWaiting_memLp _ _ _ β s
  have hWB θ n : ∀ᵐω ∂μ θ n,‖wait θ n ω‖≤Real.sqrt (dim n) := seededWaiting_bound (hn n) β s
  have hMean θ : limsup (fun n => |expectedEnergy (μ:=μ θ n) Prod.snd (mean θ n)-
      forkEnergy p β e c r (branches θ.1) (age θ.1)|) atTop≤γ θ := by
    simpa only [mean,γ,FiniteForkStanding.energyError,energy_transfer] using le_refl (γ θ)
  have hApprox θ : limsup (fun n => distanceRoot (μ θ n) (dim n)
      (alg θ n) (projected (Q θ.1) (mean θ n))) atTop≤error θ.1 :=
    ForkApproximationSelection.distance_limsup_le hn (hB θ) (error_positive θ.1).le (A θ)
  have hProjection θ : limsup (fun n => distanceRoot (μ θ n) (dim n)
      (projected (Q θ.1) (mean θ n)) (normalized (Q θ.1) (mean θ n))) atTop≤κ θ :=
    FiniteForkProjectionLimits.projection_limsup_le hn (hKn θ.1) (hQ θ.1) (hB θ) (by
      simpa only [ζ,FiniteForkStanding.normError,defect_transfer] using le_refl (ζ θ))
  have hnonneg θ : 0≤f θ := (CKPhysicalConsequences.physical_bounds_of_equations h).1 _ _
    (by positivity) s.coe_nonneg |>.1
  have hPair θ : Tendsto (fun n => pairing (μ:=μ θ n) (mean θ n) (wait θ n)) atTop (𝓝 (f θ)) :=
    PhysicalForkStanding.mean_waiting_CK_limit F (hKn θ.1) (age θ.1)
      (trunkTime t s (age θ.1) θ.2) s (waiting_le_trunkTime t s (age θ.1) θ.2)
      (hBridge _ ((waiting_le_trunkTime t s (age θ.1) θ.2).trans (le_self_add)))
  apply ProfileForkForgettingEventually.sequence_forgetting_from_eventual_profile_forks hp hβ H hq hq1
    hell he hr hm (fun a => (age a:ℝ)) branches (fun a => (age a).coe_nonneg) branches_positive
    age_branches_tendsto dim hn μ (fun _ _ => Prod.snd) (fun θ n => disorder_hasLaw _ _ _)
    alg mean wait (fun _ => wait)
    (fun θ n => (hAM θ n).aestronglyMeasurable) (fun θ n => (hMM θ n).aestronglyMeasurable)
    (fun θ n => (hWM θ n).aestronglyMeasurable) (fun _ θ n => (hWM θ n).aestronglyMeasurable)
    hAB hMB hWB (fun _ => hWB) hγ (fun a => (error_positive a).le) hκ hnonneg (by norm_num : (0:ℝ)≤0)
    hMean hApprox hProjection hγlim error_tendsto_zero hκlim
    (fun _ _ hδ => hWaiting alg (fun θ => (A θ).Lip) (fun θ => (A θ).measurable) (fun θ => (A θ).good) hδ)
    (by intro m hm θ; simp only [sub_self,norm_zero,zero_pow (by omega : 2≠0),zero_div,integral_zero];simp)
    hPair ?_
  change ∀ᶠθ in orderedFilter.curry atTop,f θ=d.C (t θ.2) s
  rw [eventually_curry_iff]
  exact Eventually.of_forall fun a => (trunk_end_eventually ht s (age a)).mono fun n he => by
    simp only [f,NNReal.coe_add]
    rw [he]

end SphericalAging.ActualForkForgettingSequence
