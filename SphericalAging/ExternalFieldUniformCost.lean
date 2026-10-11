module

public import SphericalAging.ExternalFieldSharpProbabilityTransfer

public section

/-! Uniform absolute-overlap cost from the explicitly preceding external
research theorem 10.1. The algorithm class uses the genuine Euclidean
ordered coefficient norm. No overlap-cost conclusion is a hypothesis. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ExternalFieldUniformCost
open Set Filter MeasureTheory FiniteModel GaussianLandscape
open ExternalFieldElementaryPenalty ExternalFieldSharpScalar ExternalFieldProbabilityTransfer
open ExternalFieldSharpProbabilityTransfer
open scoped Topology InnerProductSpace NNReal ENNReal

structure BallFieldAlgorithm (N p : ℕ) (L : ℝ≥0) where
  output : Disorder N p→Vector N
  measurable_output : Measurable output
  lipschitz_output : LipschitzWith L (fun J : EuclideanSpace ℝ (TensorIndex N p) => output J.ofLp)
  ball_output : ∀J,‖output J‖≤Real.sqrt N
  direction : Vector N
  norm_direction : ‖direction‖=Real.sqrt N

@[expose]  def meanCost {N p : ℕ} {L : ℝ≥0} (A : BallFieldAlgorithm N p L) : ℝ :=
  ∫J : Disorder N p,ballEnergy A.output J+betaD p*|ballOverlap A.direction A.output J|^p
    ∂disorderLaw N p

/-- Literal preceding theorem 10.1, kept as a research input. Its constants
are uniform in the actual direction and Lipschitz algorithm. -/
@[expose]  def PublishedFieldThreshold (p : ℕ) (L : ℝ≥0) : Prop :=
  ∀κ≥0,∀η>0,∃c>0,∃N0 : ℕ,∀N, N0≤N→1≤N→∀A : BallFieldAlgorithm N p L,
    (disorderLaw N p).real {J | algorithmicField p κ+η≤
      ballEnergy A.output J+κ*ballOverlap A.direction A.output J}≤Real.exp (-c*(N:ℝ))

@[expose]  def negDirection {N p : ℕ} {L : ℝ≥0} (A : BallFieldAlgorithm N p L) : BallFieldAlgorithm N p L :=
  { A with direction := -A.direction, norm_direction := by simpa only [norm_neg] using A.norm_direction }

 theorem field_tail_from_published {p : ℕ} {L : ℝ≥0} (H : PublishedFieldThreshold p L)
    (dim : ℕ→ℕ) (hDim : ∀n,1≤dim n) (hDimTop : Tendsto dim atTop atTop)
    (A : ∀n,BallFieldAlgorithm (dim n) p L) {κ η : ℝ} (hκ : 0≤κ) (hη : 0<η) :
    Tendsto (fun n => (disorderLaw (dim n) p).real {J | algorithmicField p κ+η≤
      ballEnergy (A n).output J+κ*ballOverlap (A n).direction (A n).output J}) atTop (𝓝 0) ∧
    Tendsto (fun n => (disorderLaw (dim n) p).real {J | algorithmicField p κ+η≤
      ballEnergy (A n).output J-κ*ballOverlap (A n).direction (A n).output J}) atTop (𝓝 0) := by
  obtain ⟨c,hc,N0,hN0⟩ := H κ hκ η hη
  have he : Tendsto (fun n => Real.exp (-c*(dim n:ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_natCast_atTop_atTop.comp hDimTop).const_mul_atTop_of_neg (by linarith))
  have hp : ∀B : ∀n,BallFieldAlgorithm (dim n) p L,
      Tendsto (fun n => (disorderLaw (dim n) p).real {J | algorithmicField p κ+η≤
        ballEnergy (B n).output J+κ*ballOverlap (B n).direction (B n).output J}) atTop (𝓝 0) := by
    intro B
    apply squeeze_zero' (Eventually.of_forall (fun n => measureReal_nonneg)) _ he
    filter_upwards [hDimTop.eventually_ge_atTop N0] with n hn
    exact hN0 (dim n) hn (hDim n) (B n)
  refine ⟨hp A,?_⟩
  have hh := hp (fun n => negDirection (A n))
  simpa only [negDirection,ballOverlap,inner_neg_left,neg_div,mul_neg,sub_eq_add_neg] using hh

 theorem uniform_meanCost_eventually {p : ℕ} (hp : 3≤p) {L : ℝ≥0}
    (H : PublishedFieldThreshold p L) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠN in atTop,∀A : BallFieldAlgorithm N p L,meanCost A≤thresholdEnergy p+ε := by
  classical
  by_contra h
  rw [eventually_atTop] at h
  push_neg at h
  have hx : ∀n,∃N,max n 1≤N ∧ ∃A : BallFieldAlgorithm N p L,
      thresholdEnergy p+ε<meanCost A := by
    intro n
    obtain ⟨N,hN,A,hA⟩ := h (max n 1)
    exact ⟨N,hN,A,hA⟩
  choose dim hd A hA using hx
  have hDim n : 1≤dim n := (le_max_right _ _).trans (hd n)
  have hDimTop : Tendsto dim atTop atTop := tendsto_atTop_mono (fun n => (le_max_left _ _).trans (hd n)) tendsto_id
  have ht := actual_ball_algorithm_sharp_penalty hp dim hDim
    (fun n => (A n).direction) (fun n => (A n).norm_direction)
    (fun n => (A n).output) (fun n => (A n).measurable_output)
    (fun n => (A n).ball_output)
    (fun κ hk η hη => field_tail_from_published H dim hDim hDimTop A hk hη) ε hε
  obtain ⟨n,hn⟩ := ht.exists
  exact (not_lt_of_ge hn) (hA n)

/-- The source's dimension-only extended error, defined from actual algorithm
costs. It is uniform in directions, outputs, and independent seeds. -/
@[expose]  def phi (p : ℕ) (L : ℝ≥0) (N : ℕ) : ℝ≥0∞ :=
  ⨆A : BallFieldAlgorithm N p L,ENNReal.ofReal (meanCost A-thresholdEnergy p)

 theorem actual_meanCost_le_phi {N p : ℕ} {L : ℝ≥0} (A : BallFieldAlgorithm N p L) :
    ENNReal.ofReal (meanCost A-thresholdEnergy p)≤phi p L N :=
  le_iSup_of_le A le_rfl

 theorem phi_tendsto_zero {p : ℕ} (hp : 3≤p) {L : ℝ≥0} (H : PublishedFieldThreshold p L) :
    Tendsto (phi p L) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases ht : ε=⊤
  · subst ε;exact Eventually.of_forall (fun _ => le_top)
  have hr : 0<ε.toReal := ENNReal.toReal_pos hε.ne' ht
  filter_upwards [uniform_meanCost_eventually hp H (show 0<ε.toReal/2 by linarith)] with N hN
  apply (iSup_le (fun A => ENNReal.ofReal_le_ofReal (show meanCost A-thresholdEnergy p≤ε.toReal/2 by linarith [hN A]))).trans
  calc
    ENNReal.ofReal (ε.toReal/2)≤ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal (by linarith)
    _ = ε := ENNReal.ofReal_toReal ht

 theorem eventual_uniform_real_bound {p : ℕ} (hp : 3≤p) {L : ℝ≥0} (H : PublishedFieldThreshold p L) :
    ∀ε>0,∀ᶠN in atTop,∀A : BallFieldAlgorithm N p L,
      ∫J : Disorder N p,ballEnergy A.output J+betaD p*|ballOverlap A.direction A.output J|^p
        ∂disorderLaw N p≤thresholdEnergy p+ε :=
  fun _ hε => uniform_meanCost_eventually hp H hε

 theorem actual_meanCost_le_phi_real {N p : ℕ} {L : ℝ≥0}
    (hφ : phi p L N≠⊤) (A : BallFieldAlgorithm N p L) :
    meanCost A≤thresholdEnergy p+(phi p L N).toReal := by
  have hh := (ENNReal.ofReal_le_iff_le_toReal hφ).mp (actual_meanCost_le_phi A)
  linarith

 theorem actual_meanCost_extended_bound {N p : ℕ} {L : ℝ≥0} (A : BallFieldAlgorithm N p L) :
    ENNReal.ofReal (meanCost A)≤ENNReal.ofReal (thresholdEnergy p)+phi p L N := by
  have hh := ENNReal.ofReal_add_le (p:=thresholdEnergy p) (q:=meanCost A-thresholdEnergy p)
  rw [show thresholdEnergy p+(meanCost A-thresholdEnergy p)=meanCost A by ring] at hh
  exact hh.trans (add_le_add le_rfl (actual_meanCost_le_phi A))

end SphericalAging.ExternalFieldUniformCost
