module

public import SphericalAging.AdditiveSphereParameterPrimitive
public import SphericalAging.PrimitiveNormGronwall
public import SphericalAging.DenseLipschitzModification

public section

/-! Dimension-independent, samplewise Euclidean coefficient Lipschitz
approximating outputs of the actual additive-noise flow. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.AdditiveSphereParameterLipschitz
open HardSphereDynamics LocalSDE LandscapeMetricProjection
open AdditiveSphereApproximationCoefficients AdditiveSphereApproximationSDE
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def terminalRate (p : ℕ) (β A T : ℝ≥0) : ℝ≥0 :=
  ⟨(parameterRate p β:ℝ)*Real.exp ((stateRate p β A:ℝ)*(T:ℝ)),by positivity⟩

theorem process_parameter_bound (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J K : CoefficientSpace N p) (x : State N) (T : ℝ≥0) :
    ∀ᵐ omega ∂P,∀ t,t≤T→
      ‖process hN hp D β A J x T t omega-process hN hp D β A K x T t omega‖≤
        (terminalRate p β A T:ℝ)*‖J-K‖ := by
  filter_upwards [process_continuous hN hp D β A J x T,process_continuous hN hp D β A K x T,
    AdditiveSphereParameterPrimitive.process_difference_eq_integral hN hp D β A J K x T]
    with omega hJ hK he
  let g : ℝ→State N := fun s => drift β A J (process hN hp D β A J x T s.toNNReal omega)-
    drift β A K (process hN hp D β A K x T s.toNNReal omega)
  have hg : Continuous g :=
    ((drift_state_lipschitz hN hp β A J).continuous.comp (hJ.comp continuous_real_toNNReal)).sub
      ((drift_state_lipschitz hN hp β A K).continuous.comp (hK.comp continuous_real_toNNReal))
  have hRate : (1:ℝ)≤stateRate p β A := by
    change 1≤1+(β:ℝ)*(p:ℝ)*(A:ℝ)*2^(p-2)*(3*(p:ℝ)+5)
    have hh : 0≤(β:ℝ)*(p:ℝ)*(A:ℝ)*2^(p-2)*(3*(p:ℝ)+5) := by positivity
    linarith
  have hbound : ∀s∈Ico (0:ℝ) (T:ℝ),‖g s‖≤(stateRate p β A:ℝ)*‖∫r in (0:ℝ)..s,g r‖+
      (parameterRate p β:ℝ)*‖J-K‖ := by
    intro s hs
    have hst : s.toNNReal≤T := by
      simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hs.2.le
    have hes := he s.toNNReal hst
    rw [Real.coe_toNNReal s hs.1] at hes
    have hh := AdditiveSphereParameterPrimitive.drift_pair_bound hN hp β A J K
      (process hN hp D β A J x T s.toNNReal omega) (process hN hp D β A K x T s.toNNReal omega)
    change ‖g s‖≤(stateRate p β A:ℝ)*‖process hN hp D β A J x T s.toNNReal omega-
      process hN hp D β A K x T s.toNNReal omega‖+(parameterRate p β:ℝ)*‖J-K‖ at hh
    rw [hes] at hh
    exact hh
  intro t ht
  have hh := PrimitiveNormGronwall.primitive_norm_le hg hRate
    (mul_nonneg (parameterRate p β).coe_nonneg (norm_nonneg _)) hbound
    (show (t:ℝ)∈Icc (0:ℝ) (T:ℝ) from ⟨t.coe_nonneg,ht⟩)
  rw [he t ht]
  exact hh.trans_eq (by change ((parameterRate p β:ℝ)*‖J-K‖)*Real.exp _=
    ((parameterRate p β:ℝ)*Real.exp _)*‖J-K‖;ring)

theorem exists_jointly_measurable_lipschitz_terminal (hN : 0<N) (hp : 2≤p)
    (D : BrownianDriver N P F) (β A : ℝ≥0) (x : State N) (T t : ℝ≥0) (ht : t≤T) :
    ∃ G : Ω×CoefficientSpace N p→State N,
      Measurable G ∧ (∀ omega,LipschitzWith (terminalRate p β A T) (fun J => G (omega,J))) ∧
      ∀ J,(fun omega => G (omega,J))=ᵐ[P] process hN hp D β A J x T t := by
  apply DenseLipschitzModification.exists_jointly_measurable_lipschitz_version
    (terminalRate p β A T) (fun J => process hN hp D β A J x T t) P
  · intro J
    exact ((process_stronglyAdapted hN hp D β A J x T t).mono (F.le t)).measurable
  · intro J K
    exact (process_parameter_bound hN hp D β A J K x T).mono (fun omega h => by
      simpa only [dist_eq_norm] using h t ht)

end SphericalAging.AdditiveSphereParameterLipschitz
