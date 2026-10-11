module

public import SphericalAging.ActualGammaPredictorMartingale
public import SphericalAging.LinearSDELocalization

public section

/-! The genuine strong SDE and Brownian law identify the backward Γ
predictor's initial value as deterministic, hence its variance is zero. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualGammaPredictorInitialValue
open FiniteModel HardSphereDynamics AnnealedSDECore ActualSphereTransition
open ActualGammaPredictorMartingale ActualGammaBackwardPredictor ActualDisorderGammaVariance
open BrownianVectorMoments ActualSphereMarkovRestart
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The actual integral SDE at time zero fixes its initial value. -/
theorem random_solution_initial {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (D : BrownianDriver N P F) (b : Ω→Fin N→State N→ℝ)
    (σ : Ω→Fin N→Fin N→State N→ℝ) (Z0 : Ω→State N)
    (X : ℝ≥0→Ω→State N) (T : ℝ≥0) (hX : IsRandomStrongSolutionOn D b σ Z0 X T) :
    X 0=ᵐ[P] Z0 := by
  obtain ⟨A,U,_,_,hEq⟩ := hX.2.2.2
  have hall := ae_all_iff.mpr (fun i : Fin N => hEq 0 bot_le i)
  have hi : ∀ᵐ ω ∂P,∀i : Fin N,(VectorIto.vectorProcessLp D (U i) 0 : Ω→ℝ) ω=0 :=
    ae_all_iff.mpr (fun i => by
      rw [LinearSDELocalization.vectorProcessLp_zero_time]
      exact Lp.coeFn_zero ℝ 2 P)
  filter_upwards [hall,hi] with ω hω hiω
  apply PiLp.ext
  intro i
  have he := hω i
  simp only [NNReal.coe_zero,intervalIntegral.integral_same,add_zero] at he
  change (X 0 ω) i=(Z0 ω) i+(VectorIto.vectorProcessLp D (U i) 0 : Ω→ℝ) ω at he
  rw [hiω i,add_zero] at he
  exact he

theorem brownianVector_zero_ae (N : ℕ) :
    brownianVector (N:=N) 0=ᵐ[VectorBrownian.law N] fun _ => 0 := by
  have hn : ‖brownianClass (N:=N) 0‖^2=0 := by simpa using brownianClass_norm_sq (N:=N) 0
  have hc : brownianClass (N:=N) 0=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  have he := brownianClass_ae (N:=N) 0
  rw [hc] at he
  filter_upwards [he,Lp.coeFn_zero (State N) 2 (VectorBrownian.law N)] with ω he h0
  exact he.symm.trans h0

variable {N p : ℕ}

theorem backwardProcess_zero_ae (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p)
    (x : State N) (X : ℝ≥0→VectorBrownian.Space N→State N)
    (hX : ∀H,IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) (fun _ => x) X H)
    (T t s : ℝ≥0) :
    backwardProcess β R hR J X T t s 0=ᵐ[VectorBrownian.law N] fun _ => gammaMean β R hR x T t s J := by
  have hx := random_solution_initial (NullAugmentation.driver (VectorBrownian.driver N))
    _ _ (fun _ => x) X 0 (hX 0)
  filter_upwards [hx,brownianVector_zero_ae N] with ω hx hb
  simp only [backwardProcess,min_eq_left (show (0 : ℝ≥0)≤s from bot_le),predictor,hx,hb,
    inner_zero_left,zero_div,zero_add,tsub_zero]

theorem backwardProcess_variance_zero (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p)
    (x : State N) (X : ℝ≥0→VectorBrownian.Space N→State N)
    (hX : ∀H,IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) (fun _ => x) X H)
    (T t s : ℝ≥0) :
    variance (backwardProcess β R hR J X T t s 0) (VectorBrownian.law N)=0 := by
  rw [variance_congr (backwardProcess_zero_ae β R hR J x X hX T t s)]
  simp [variance,evariance]

theorem joint_backwardProcess_variance_zero (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p) (x : State N) (hx : OnSphere x)
    (T t s : ℝ≥0) :
    variance (backwardProcess β R hR J (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x)) T t s 0)
      (VectorBrownian.law N)=0 :=
  backwardProcess_variance_zero β R hR J x _
    (fun H => jointProcess_physical (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR J x hx H) T t s

end SphericalAging.ActualGammaPredictorInitialValue
