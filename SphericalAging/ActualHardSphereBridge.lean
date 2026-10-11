module

public import SphericalAging.ActualCKSource33Convergence

public section

/-! Complete actual-model Proposition 3.3, in the manuscript's noise-√2
normalization and with its literal causal response integral. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ActualHardSphereBridge
open ActualCKSource33Suprema ActualCKSource33Convergence ActualCKMeanKernelConvergence
  ActualCompactCKMemoryLimit ActualModelOverlapVariance ActualBrownianPrimitiveTimeModulus
  AnnealedHamiltonianEnergyStein CompactKernelMemoryLimit
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

@[expose]  def hardBridgeExpectedError (N p : ℕ) (β : ℝ≥0) (d : CKSpecification.CKData) (T : ℝ≥0)
    (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) : ℝ :=
  sSup ((fun z : ℝ≥0×ℝ≥0 =>
    |actualOverlap β (N+1) (modelRadius_pos N) z.1 z.2 ω-d.C z.1 z.2|^2+
    |actualGamma β (N+1) (modelRadius_pos N) z.1 z.2 ω-(∫u in (0:ℝ)..(z.2:ℝ),d.R z.1 u)|) '' triangle T)

@[expose]  def hardBridgeProbabilityError (N p : ℕ) (β : ℝ≥0) (d : CKSpecification.CKData) (T : ℝ≥0)
    (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) : ℝ :=
  sSup ((fun z : ℝ≥0×ℝ≥0 =>
    |actualOverlap β (N+1) (modelRadius_pos N) z.1 z.2 ω-d.C z.1 z.2|+
    |actualGamma β (N+1) (modelRadius_pos N) z.1 z.2 ω-(∫u in (0:ℝ)..(z.2:ℝ),d.R z.1 u)|) '' triangle T)

 theorem actual_source33_expected_sup_literal {p : ℕ} (dim : ℕ→ℕ)
    (hdim : Tendsto dim atTop atTop) (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    Tendsto (fun n => ∫ω,hardBridgeExpectedError (dim n) p β d T ω
      ∂AnnealedModelLaw.law (dim n) p) atTop (𝓝 0) := by
  have he n : hardBridgeExpectedError (dim n) p β d T=
      bridgeExpectationSup (dim n) p β (dim n+1) (modelRadius_pos (dim n)) d T :=
    funext (fun ω => (bridgeExpectationSup_eq_causal β _ _ d T ω).symm)
  simp_rw [he]
  exact actual_source33_expected_sup_tendsto_zero dim hdim hp β hβ d hd T

 theorem actual_source33_probability_literal {p : ℕ} (dim : ℕ→ℕ)
    (hdim : Tendsto dim atTop atTop) (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0)
    {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun n => AnnealedModelLaw.law (dim n) p
      {ω | ε<hardBridgeProbabilityError (dim n) p β d T ω}) atTop (𝓝 0) := by
  have he n : hardBridgeProbabilityError (dim n) p β d T=
      bridgeProbabilitySup (dim n) p β (dim n+1) (modelRadius_pos (dim n)) d T :=
    funext (fun ω => (bridgeProbabilitySup_eq_causal β _ _ d T ω).symm)
  simp_rw [he]
  exact actual_source33_ennreal_probability_tendsto_zero dim hdim hp β hβ d hd T hε

 /-- Every conclusion of manuscript Proposition 3.3, for the literal model. -/
 structure HardSphereBridge (p : ℕ) (β : ℝ≥0) (dim : ℕ→ℕ)
    (d : CKSpecification.CKData) (T : ℝ≥0) : Prop where
  uniform_probability : ∀ε : ℝ,0<ε→Tendsto
    (fun n => AnnealedModelLaw.law (dim n) p {ω | ε<hardBridgeProbabilityError (dim n) p β d T ω}) atTop (𝓝 0)
  expected_sup : Tendsto (fun n => ∫ω,hardBridgeExpectedError (dim n) p β d T ω
    ∂AnnealedModelLaw.law (dim n) p) atTop (𝓝 0)
  mean_correlation : TendstoUniformlyOn (fun n => Function.uncurry (modelCorrelation (dim n) p β))
    (fun z : ℝ≥0×ℝ≥0 => d.C z.1 z.2) atTop (triangle T)
  mean_primitive : TendstoUniformlyOn (fun n => Function.uncurry (modelGamma (dim n) p β))
    (fun z : ℝ≥0×ℝ≥0 => ∫u in (0:ℝ)..(z.2:ℝ),d.R z.1 u) atTop (triangle T)
  response_diagonal : ∀t : ℝ,0≤t→d.R t t=1

 theorem proposition_3_3_actual {p : ℕ} (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    HardSphereBridge p β dim d T := by
  have hm := actual_ck_means_uniform_limit dim hdim hp β hβ d hd T
  refine ⟨fun ε hε => actual_source33_probability_literal dim hdim hp β hβ d hd T hε,
    actual_source33_expected_sup_literal dim hdim hp β hβ d hd T,
    hm.1.mono (ActualCKMeanConvergenceOfEquicontinuity.triangle_subset_square T),?_,hd.response_diagonal⟩
  apply (hm.2.1.mono (ActualCKMeanConvergenceOfEquicontinuity.triangle_subset_square T)).congr_right
  intro z hz
  simp only [ResponsePrimitiveInterchange.responsePrimitive,min_eq_right (NNReal.coe_le_coe.mpr hz.1)]

 /-- The physical CK solution and all actual-model fixed-horizon bridges exist. -/
 theorem exists_actual_hard_sphere_bridge {p : ℕ} (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β) :
    ∃d : CKSpecification.CKData,CKSpecification.CKEquations p β d ∧
      CKSpecification.PhysicalBounds d ∧ CKSpecification.PositiveSemidefiniteCorrelation d ∧
      ∀dim : ℕ→ℕ,Tendsto dim atTop atTop→∀T : ℝ≥0,HardSphereBridge p β dim d T := by
  obtain ⟨d,hd,hB,hPSD,-⟩ := exists_actual_ck_uniform_limit hp β hβ
  exact ⟨d,hd,hB,hPSD,fun dim hdim T => proposition_3_3_actual dim hdim hp β hβ d hd T⟩

end SphericalAging.ActualHardSphereBridge
