module

public import SphericalAging.ActualSphereMeanTimeC2
public import SphericalAging.ActualC2Martingale
public import Mathlib.Probability.Moments.Variance

public section

/-! Genuine terminal-conditioned backward transition martingales for the
actual sphere SDE. The conditional identity is derived from actual Brownian
future independence and restart, and continuity comes from the actual
transition family. No backward PDE or martingale identity is a premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualSphereBackwardMartingale
open HardSphereDynamics LocalSDE ActualSphereTransition ActualSphereMarkovProperty ActualSphereSemigroup
open ActualSphereContinuousSemigroup ActualSphereJointTransitionContinuity ActualSphereTimeLipschitz
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- Actual backward transition evaluated along the stopped original path. -/
@[expose] def backwardProcess (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (J : FiniteModel.Disorder N p)
    (X : ℝ≥0 → VectorBrownian.Space N → State N) (T : ℝ≥0) (f : State N → ℝ) :
    ℝ≥0 → VectorBrownian.Space N → ℝ :=
  fun s ω => transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (T-s) f (X (min s T) ω)

section Actual
variable (hN : N≠0) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
  (J : FiniteModel.Disorder N p) (X : ℝ≥0 → VectorBrownian.Space N → State N)
  {Z0 : VectorBrownian.Space N → State N}
  (hX : ∀ T,AnnealedSDECore.IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
    (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X T)
  (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ t,OnSphere (X t ω))
  (T : ℝ≥0) (f : State N → ℝ) (hf : Continuous f)

include hX hf in
theorem backwardProcess_stronglyAdapted :
    StronglyAdapted (NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N))
      (backwardProcess β R hR J X T f) := by
  intro s
  have hXs := ((hX 0).2.1 (min s T)).mono
    ((NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)).mono (min_le_left s T))
  exact (transition_measurable _ β R hR J (T-s) f hf).comp_measurable hXs.measurable

include hN hNR hX hSphere hf

/-- Actual conditional terminal value in the full Brownian filtration,
including after the deterministic terminal time. -/
theorem backwardProcess_eq_condExp (s : ℝ≥0) :
    backwardProcess β R hR J X T f s=ᵐ[VectorBrownian.law N]
      (VectorBrownian.law N)[(fun ω => f (X T ω)) |
        NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N) s] := by
  let P := VectorBrownian.law N
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let F := NullAugmentation.augment (VectorBrownian.filtration N) P
  let g : State N → ℝ := fun y => coefficientBump (N := N) R hR y*f y
  have hg : Continuous g := (coefficientBump (N := N) R hR).continuous.mul hf
  have hgc : HasCompactSupport g := (coefficientBump (N := N) R hR).hasCompactSupport.mul_right
  obtain ⟨C,hC⟩ := hgc.exists_bound_of_continuous hg
  have hgf (y : State N) (hy : OnSphere y) : g y=f y := by
    have hn : ‖y‖^2=(N : ℝ) := by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hy
    have hr : ‖y‖≤R := by nlinarith [norm_nonneg y]
    have hm : y ∈ Metric.closedBall (0 : State N) (coefficientBump (N := N) R hR).rIn := by
      simpa only [coefficientBump,Metric.mem_closedBall,dist_zero_right] using hr
    simp only [g,(coefficientBump (N := N) R hR).one_of_mem_closedBall hm,one_mul]
  have hterminal : (fun ω => g (X T ω))=ᵐ[P] fun ω => f (X T ω) :=
    hSphere.mono (fun _ h => hgf _ (h T))
  by_cases hs : s≤T
  · have hmarkov := conditional_transition hN β R hR hNR J X hX hSphere s (T-s) g hg
      (Real.toNNReal C) (fun y => (hC y).trans (Real.le_coe_toNNReal C))
    rw [add_tsub_cancel_of_le hs] at hmarkov
    have hwait : backwardProcess β R hR J X T f s=ᵐ[P]
        fun ω => transition D β R hR J (T-s) g (X s ω) := by
      filter_upwards [hSphere] with ω hω
      dsimp only [backwardProcess]
      rw [min_eq_left hs]
      exact (transition_congr_onSphere hN β R hR hNR J (T-s) (X s ω) (hω s) g f hgf).symm
    exact hwait.trans (hmarkov.symm.trans (condExp_congr_ae hterminal))
  · have hTs : T≤s := le_of_not_ge hs
    have hfi : Integrable (fun ω => f (X T ω)) P := by
      apply (Integrable.of_bound
        (hg.comp_stronglyMeasurable (((hX 0).2.1 T).mono (F.le T))).aestronglyMeasurable
        (Real.toNNReal C) (.of_forall (fun ω => (hC _).trans (Real.le_coe_toNNReal C)))).congr hterminal
    have hfa : StronglyMeasurable[F s] (fun ω => f (X T ω)) :=
      hf.comp_stronglyMeasurable (((hX 0).2.1 T).mono (F.mono hTs))
    have he := condExp_of_stronglyMeasurable (F.le s) hfa hfi
    apply EventuallyEq.trans _ (.of_forall (fun ω => congrFun he.symm ω))
    exact .of_forall (fun ω => by
      simp only [backwardProcess,tsub_eq_zero_of_le hTs,min_eq_right hTs]
      exact transition_zero D β R hR J f _)

/-- The actual backward transition along the same original physical path
is a genuine martingale, derived without a backward PDE premise. -/
theorem backwardProcess_martingale :
    Martingale (backwardProcess β R hR J X T f)
      (NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)) (VectorBrownian.law N) := by
  let P := VectorBrownian.law N
  let F := NullAugmentation.augment (VectorBrownian.filtration N) P
  have he (s : ℝ≥0) := backwardProcess_eq_condExp hN β R hR hNR J X hX hSphere T f hf s
  refine ⟨backwardProcess_stronglyAdapted β R hR J X hX T f hf,?_⟩
  intro s t hst
  exact (condExp_congr_ae (he t)).trans
    ((condExp_condExp_of_le (F.mono hst) (F.le t)).trans (he s).symm)

/-- Actual backward C² test martingales have continuous paths, obtained
from true joint transition continuity on the physical sphere. -/
theorem backwardProcess_continuous (hfC2 : ContDiff ℝ 2 f) :
    ∀ᵐ ω ∂VectorBrownian.law N,Continuous (fun s => backwardProcess β R hR J X T f s ω) := by
  have hc := transition_C2_jointContinuous_sphere hN β R hR hNR J hfC2
  filter_upwards [(hX 0).2.2.1,hSphere] with ω hω hS
  let q : ℝ≥0 → ℝ≥0 × {y : State N // OnSphere y} :=
    fun s => (T-s,⟨X (min s T) ω,hS _⟩)
  have hq : Continuous q := by
    apply Continuous.prodMk
    · fun_prop
    · apply Continuous.subtype_mk
      exact hω.comp (continuous_id.min continuous_const)
  exact hc.comp hq

end Actual

end SphericalAging.ActualSphereBackwardMartingale
