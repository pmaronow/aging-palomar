module

public import SphericalAging.GaussianBallEnergyStein
public import SphericalAging.HamiltonianEnergySteinActual

public section

/-! Genuine Gaussian energy integration by parts for the mean of a finite
family of constructed terminal Hamiltonian diffusions. Brownian drivers
may share a past and need not be independent. Their literal terminal
classes and tensor derivatives supply every Stein hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SphericalAging.FiniteForkTerminalEnergyStein
open MeasureTheory ProbabilityTheory StochasticCalculus Filter Set FiniteModel
  HardSphereDynamics HamiltonianDisorderTerminalDerivative HamiltonianEnergySteinActual
  HamiltonianDisorderResponseGrowth GaussianBallEnergyStein GaussianObservableDerivative
  GaussianIntegrationByParts HamiltonianPredictableForcing
open scoped NNReal ENNReal BigOperators InnerProductSpace Topology
variable {N p K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

@[expose] def terminalMean (F : Fin K→Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (D : ∀b,BrownianDriver N P (F b)) (β : ℝ) (R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (x : State N) (T t : ℝ≥0) : StateL2 N P :=
  (K:ℝ)⁻¹ • ∑b,stateClass (NullAugmentation.driver (D b)) β R hR J x T t

@[expose] def meanResponse (F : Fin K→Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (D : ∀b,BrownianDriver N P (F b)) (β : ℝ) (R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (x : State N) (T t : ℝ≥0) : Disorder N p→L[ℝ] StateL2 N P :=
  (K:ℝ)⁻¹ • ∑b,stateResponse (NullAugmentation.driver (D b)) β R hR J x T t

theorem terminalMean_hasFDerivAt (F : Fin K→Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (D : ∀b,BrownianDriver N P (F b)) (β : ℝ) (R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (x : State N) (T t : ℝ≥0) :
    HasFDerivAt (fun J => terminalMean F D β R hR J x T t)
      (meanResponse F D β R hR J x T t) J := by
  exact (HasFDerivAt.fun_sum (fun b (_ : b∈Finset.univ) =>
    stateClass_hasFDerivAt_disorder (D b) β R hR J x T t)).const_smul ((K:ℝ)⁻¹)

theorem terminalMean_ball (hN : 0<N) (hK : 0<K)
    (F : Fin K→Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (D : ∀b,BrownianDriver N P (F b)) (β : ℝ) (R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (x : State N) (hx : OnSphere x)
    (T t : ℝ≥0) (ht : t≤T) :
    ∀ᵐω ∂P,‖terminalMean F D β R hR J x T t ω‖≤Real.sqrt (N:ℝ) := by
  let X b := stateClass (NullAugmentation.driver (D b)) β R hR J x T t
  have hball b : ∀ᵐω ∂P,‖X b ω‖=Real.sqrt (N:ℝ) :=
    (stateClass_onSphere (Nat.ne_of_gt hN) (D b) β R hR hNR J x hx T t ht).mono fun ω hω =>
      (Real.sqrt_sq (norm_nonneg _)).symm.trans
        (congrArg Real.sqrt ((onSphere_iff_norm_sq _).mp hω))
  have hKpos : (0:ℝ)<K := Nat.cast_pos.mpr hK
  filter_upwards [Lp.coeFn_smul (K:ℝ)⁻¹ (∑b,X b),
    Lp.coeFn_finsetSum Finset.univ X,ae_all_iff.mpr hball] with ω h1 h2 h3
  change ‖((K:ℝ)⁻¹ • ∑b,X b) ω‖≤_
  rw [h1]
  simp only [Pi.smul_apply,h2,Finset.sum_apply,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hKpos.le)]
  calc
    (K:ℝ)⁻¹*‖∑b,X b ω‖≤(K:ℝ)⁻¹*∑b,‖X b ω‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hKpos.le)
    _ = _ := by simp [h3];field_simp

theorem meanResponse_coordinate_growth (hK : 0<K)
    (F : Fin K→Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (D : ∀b,BrownianDriver N P (F b)) (β : ℝ) (R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (x : State N) (T t : ℝ≥0) (ht : t≤T) (I : TensorIndex N p) :
    ‖meanResponse F D β R hR J x T t (Pi.single I 1)‖≤
      (disorderConstant (N:=N) (p:=p) β R hR:ℝ)*
        Real.exp (exponentBase (N:=N) (p:=p) β R hR t/2+
          (exponentSlope (N:=N) (p:=p) β R hR t/2:ℝ≥0)*‖J‖) := by
  have hKpos : (0:ℝ)<K := Nat.cast_pos.mpr hK
  simp only [meanResponse,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hKpos.le)]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hKpos.le)).trans ?_
  have hs := Finset.sum_le_sum (fun b (_ : b∈Finset.univ) =>
    stateResponse_coordinate_growth (D b) β R hR J x T t ht I)
  have hh := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hKpos.le)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    ←mul_assoc,inv_mul_cancel₀ hKpos.ne',one_mul] using hh

theorem actual_terminalMean_energy_stein (hN : 0<N) (hp : 0<p) (hK : 0<K)
    (F : Fin K→Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (D : ∀b,BrownianDriver N P (F b)) (β : ℝ) (R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (x : State N) (hx : OnSphere x)
    (T t : ℝ≥0) (ht : t≤T) :
    (∫J,∫ω,Hamiltonian N p J (terminalMean F D β R hR J x T t ω) ∂P ∂disorderLaw N p)=
      ∑I : TensorIndex N p,∫J,∫ω,⟪gradient (hamiltonianCoefficient I)
        (terminalMean F D β R hR J x T t ω),
        meanResponse F D β R hR J x T t (Pi.single I 1) ω⟫_ℝ ∂P ∂disorderLaw N p := by
  exact hamiltonian_energy_stein_ball hN hp
    (fun J => terminalMean F D β R hR J x T t)
    (fun J => meanResponse F D β R hR J x T t)
    (fun J => terminalMean_hasFDerivAt F D β R hR J x T t)
    (fun J => terminalMean_ball hN hK F D β R hR hNR J x hx T t ht)
    (fun _ => disorderConstant (N:=N) (p:=p) β R hR)
    (fun _ => exponentSlope (N:=N) (p:=p) β R hR t/2)
    (fun _ => exponentBase (N:=N) (p:=p) β R hR t/2)
    (fun I J => meanResponse_coordinate_growth hK F D β R hR J x T t ht I)

end SphericalAging.FiniteForkTerminalEnergyStein
