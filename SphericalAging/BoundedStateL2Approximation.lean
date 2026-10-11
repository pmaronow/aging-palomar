module

public import SphericalAging.GaussianObservableDerivative
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

/-! Genuine bounded truncations of an arbitrary vector L² class, with
literal integral pairings converging and uniform L² bounds. This lets
bounded disorder Stein identities pass to an unbounded Brownian vector. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.BoundedStateL2Approximation
open HardSphereDynamics GaussianObservableDerivative
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

@[expose] def truncField (K : ℝ≥0) (Y : Lp (State N) 2 P) (ω : Ω) : State N :=
  if ‖Y ω‖≤K then Y ω else 0

lemma truncField_stronglyMeasurable (K : ℝ≥0) (Y : Lp (State N) 2 P) :
    StronglyMeasurable (truncField K Y) := by
  classical
  have hs : MeasurableSet {ω : Ω | ‖Y ω‖≤K} :=
    measurableSet_le (Lp.stronglyMeasurable Y).norm.measurable measurable_const
  have he : truncField K Y={ω : Ω | ‖Y ω‖≤K}.indicator Y := by
    funext ω
    simp only [truncField,Set.indicator,mem_setOf_eq]
  rw [he]
  exact (Lp.stronglyMeasurable Y).indicator hs

lemma truncField_norm_le (K : ℝ≥0) (Y : Lp (State N) 2 P) (ω : Ω) :
    ‖truncField K Y ω‖≤‖Y ω‖ := by
  unfold truncField
  split_ifs <;> simp

lemma truncField_norm_le_cut (K : ℝ≥0) (Y : Lp (State N) 2 P) (ω : Ω) :
    ‖truncField K Y ω‖≤K := by
  unfold truncField
  split_ifs with h
  · exact h
  · simpa using K.2

lemma truncField_memLp (K : ℝ≥0) (Y : Lp (State N) 2 P) : MemLp (truncField K Y) 2 P :=
  (Lp.memLp Y).of_le (truncField_stronglyMeasurable K Y).aestronglyMeasurable
    (.of_forall (truncField_norm_le K Y))

@[expose] def truncClass (K : ℝ≥0) (Y : Lp (State N) 2 P) : Lp (State N) 2 P :=
  (truncField_memLp K Y).toLp (truncField K Y)

lemma truncClass_ae (K : ℝ≥0) (Y : Lp (State N) 2 P) :
    (truncClass K Y : Ω → State N)=ᵐ[P] truncField K Y :=
  (truncField_memLp K Y).coeFn_toLp

lemma truncClass_norm_le (K : ℝ≥0) (Y : Lp (State N) 2 P) : ‖truncClass K Y‖≤‖Y‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [truncClass_ae K Y] with ω hω
  rw [hω]
  exact truncField_norm_le K Y ω

lemma truncClass_ae_bound (K : ℝ≥0) (Y : Lp (State N) 2 P) :
    ∀ᵐ ω ∂P,‖truncClass K Y ω‖≤K := by
  filter_upwards [truncClass_ae K Y] with ω hω
  rw [hω]
  exact truncField_norm_le_cut K Y ω

lemma truncField_tendsto (Y : Lp (State N) 2 P) (ω : Ω) :
    Tendsto (fun n : ℕ => truncField n Y ω) atTop (𝓝 (Y ω)) := by
  have he : ∀ᶠ n : ℕ in atTop,‖Y ω‖≤(n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with n hn
  simp only [truncField,NNReal.coe_natCast,hn,ite_true]

 theorem truncClass_pairing_tendsto (V Y : Lp (State N) 2 P) :
    Tendsto (fun n : ℕ => ∫ ω,inner ℝ (V ω) (truncClass n Y ω) ∂P) atTop
      (𝓝 (∫ ω,inner ℝ (V ω) (Y ω) ∂P)) := by
  have hi : Integrable (fun ω => ‖V ω‖*‖Y ω‖) P :=
    memLp_one_iff_integrable.mp ((Lp.memLp V).norm.mul (Lp.memLp Y).norm)
  apply tendsto_integral_of_dominated_convergence (fun ω => ‖V ω‖*‖Y ω‖)
  · intro n
    exact (Lp.aestronglyMeasurable V).inner (Lp.aestronglyMeasurable (truncClass n Y))
  · exact hi
  · intro n
    filter_upwards [truncClass_ae n Y] with ω hω
    rw [hω]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (truncField_norm_le n Y ω) (norm_nonneg _))
  · filter_upwards [ae_all_iff.mpr (fun n : ℕ => truncClass_ae n Y)] with ω hω
    have ht := (innerSL ℝ (V ω)).continuous.continuousAt.tendsto.comp (truncField_tendsto Y ω)
    simpa only [Function.comp_def,innerSL_apply_apply,hω] using ht

 theorem truncClass_pairing_abs_bound (V Y : Lp (State N) 2 P) (K : ℝ≥0) :
    |∫ ω,inner ℝ (V ω) (truncClass K Y ω) ∂P|≤‖V‖*‖Y‖ := by
  rw [← L2.inner_def (𝕜 := ℝ)]
  exact (norm_inner_le_norm (𝕜 := ℝ) V (truncClass K Y)).trans
    (mul_le_mul_of_nonneg_left (truncClass_norm_le K Y) (norm_nonneg _))

end SphericalAging.BoundedStateL2Approximation
