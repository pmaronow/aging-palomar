module

public import SphericalAging.GaussianOrthogonalForkCovariance
public import SphericalAging.GaussianDualSupConcentration
public import SphericalAging.GaussianPiLpLaw
public import SphericalAging.OrthogonalGaussianDisclosure

public section

/-! Actual Gaussian supremum concentration for the orthogonal fork
increments in Huang--Sellke Lemma 3.2. The supremum's Lipschitz scale is
derived from the computed actual covariance, rather than assumed. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianOrthogonalForkSupremum
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open GaussianOrthogonalForkCovariance OrthogonalGaussianDisclosure GaussianSmoothConcentration
open scoped NNReal
variable {N p K : ℕ}

@[expose] abbrev ForkTensor (N p K : ℕ) := PiLp 2 (fun _ : Option (Fin K) => TensorSpace N p)

@[expose] def tensorInputs (J : ForkDisorder N p K) : ForkTensor N p K :=
  WithLp.toLp 2 (fun i => WithLp.toLp 2 (J i))

theorem tensorInputs_hasLaw :
    HasLaw (tensorInputs (N:=N) (p:=p) (K:=K)) (stdGaussian (ForkTensor N p K)) (forkLaw N p K) := by
  have hm : Measurable (tensorInputs (N:=N) (p:=p) (K:=K)) :=
    (PiLp.continuous_toLp 2 (fun _ : Option (Fin K) => TensorSpace N p)).measurable.comp
      (Measurable.of_eval (fun i =>
        (PiLp.continuous_toLp 2 (fun _ : TensorIndex N p => ℝ)).measurable.comp (measurable_pi_apply i)))
  refine ⟨hm.aemeasurable,?_⟩
  change (Measure.pi (fun _ : Option (Fin K) => disorderLaw N p)).map
    ((WithLp.toLp 2)∘(fun J i => WithLp.toLp 2 (J i)))=_
  rw [←Measure.map_map (by fun_prop) (by fun_prop),Measure.pi_map_pi
    (fun _ => (ordered_tensor_hasLaw N p).aemeasurable)]
  simp_rw [(ordered_tensor_hasLaw N p).map_eq]
  exact GaussianPiLpLaw.map_pi_stdGaussian

@[expose] def decode : ForkTensor N p K≃L[ℝ]ForkDisorder N p K :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin K) => TensorSpace N p)).trans
    (ContinuousLinearEquiv.piCongrRight (fun _ =>
      PiLp.continuousLinearEquiv 2 ℝ (fun _ : TensorIndex N p => ℝ)))

theorem decode_tensorInputs (J : ForkDisorder N p K) : decode (tensorInputs J)=J := by
  ext i I
  rfl

@[expose] def forkDual (a b : ℝ) (x : Vector N) (y : Fin K→Vector N) : ForkTensor N p K→L[ℝ] ℝ :=
  (averagedIncrementCLM a b x y).comp decode.toContinuousLinearMap

theorem forkDual_tensorInputs (a b : ℝ) (x : Vector N) (y : Fin K→Vector N)
    (J : ForkDisorder N p K) : forkDual a b x y (tensorInputs J)=averagedIncrement a b x y J := by
  rw [forkDual,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,decode_tensorInputs,
    averagedIncrementCLM_apply]

theorem forkDual_norm_sq (a b : ℝ) (x : Vector N) (y : Fin K→Vector N) :
    ‖forkDual (p:=p) a b x y‖^2=variance (averagedIncrement a b x y) (forkLaw N p K) := by
  have hh := tensorInputs_hasLaw.covariance_fun_comp
    (forkDual (p:=p) a b x y).continuous.measurable.aemeasurable
    (forkDual (p:=p) a b x y).continuous.measurable.aemeasurable
  simp_rw [forkDual_tensorInputs] at hh
  rw [covariance_self (averagedIncrement_hasGaussianLaw a b x y).aemeasurable,
    covariance_self (forkDual a b x y).continuous.measurable.aemeasurable,
    variance_dual_stdGaussian] at hh
  exact hh.symm

theorem orthogonal_forkDual_norm_le (hN : 0<N) (hp : 1≤p) (hK : 0<K)
    (a b : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (x : Vector N) (y : Fin K→Vector N) (r q : ℝ)
    (hr : 0≤r) (hq : 0≤q) (hq1 : q≤1) (hf : OrthogonalFork x y r q) :
    ‖forkDual (p:=p) a b x y‖≤Real.sqrt (1/((K:ℝ)*N)) := by
  apply Real.le_sqrt_of_sq_le
  rw [forkDual_norm_sq]
  exact orthogonal_fork_variance_le hN hp hK a b ha hab hb x y r q hr hq hq1 hf

@[expose] abbrev ForkDomain (N K : ℕ) (r q : ℝ) :=
  {z : Vector N×(Fin K→Vector N) // OrthogonalFork z.1 z.2 r q}

@[expose] def supremum (a b r q : ℝ) (J : ForkDisorder N p K) : ℝ :=
  sSup (Set.range (fun z : ForkDomain N K r q => averagedIncrement a b z.1.1 z.1.2 J))

@[expose] def forkConstant (N K : ℕ) : ℝ≥0 := ⟨(Real.pi/2)^2/((K:ℝ)*N),by positivity⟩

theorem fork_constant_eq (N K : ℕ) :
    rotationConstant ⟨Real.sqrt (1/((K:ℝ)*N)),Real.sqrt_nonneg _⟩=forkConstant N K := by
  apply NNReal.coe_injective
  change (Real.pi/2)^2*Real.sqrt (1/((K:ℝ)*N))^2=(Real.pi/2)^2/((K:ℝ)*N)
  rw [Real.sq_sqrt (by positivity)]
  ring

theorem supremum_centered_hasSubgaussianMGF (hN : 0<N) (hp : 1≤p) (hK : 0<K)
    (a b r q : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hr : 0≤r) (hq : 0≤q) (hq1 : q≤1) [Nonempty (ForkDomain N K r q)] :
    HasSubgaussianMGF (fun J => supremum (N:=N) (p:=p) (K:=K) a b r q J-
      ∫J',supremum a b r q J' ∂forkLaw N p K) (forkConstant N K) (forkLaw N p K) := by
  let A : ForkDomain N K r q→(ForkTensor N p K→L[ℝ] ℝ) :=
    fun z => forkDual a b z.1.1 z.1.2
  have hA : ∀z,‖A z‖≤(⟨Real.sqrt (1/((K:ℝ)*N)),Real.sqrt_nonneg _⟩:ℝ≥0) :=
    fun z => orthogonal_forkDual_norm_le hN hp hK a b ha hab hb z.1.1 z.1.2 r q hr hq hq1 z.2
  have hG := GaussianDualSupConcentration.supremum_centered_hasSubgaussianMGF A hA
  rw [fork_constant_eq] at hG
  have hLip := GaussianDualSupConcentration.supremum_lipschitz A hA
  have hEq (J : ForkDisorder N p K) :
      GaussianDualSupConcentration.supremum A (tensorInputs J)=supremum a b r q J := by
    unfold GaussianDualSupConcentration.supremum supremum
    change sSup (Set.range (fun z : ForkDomain N K r q => forkDual a b z.1.1 z.1.2 (tensorInputs J)))=_
    simp_rw [forkDual_tensorInputs]
  have hMean := tensorInputs_hasLaw.integral_comp
    hLip.continuous.stronglyMeasurable.aestronglyMeasurable
  simp only [Function.comp_def] at hMean
  simp_rw [hEq] at hMean
  rw [←tensorInputs_hasLaw.map_eq] at hG
  have hh := HasSubgaussianMGF.of_map tensorInputs_hasLaw.aemeasurable hG
  rw [tensorInputs_hasLaw.map_eq] at hh
  simp only [Function.comp_def,hEq,←hMean] at hh
  exact hh

theorem supremum_centered_absolute_tail (hN : 0<N) (hp : 1≤p) (hK : 0<K)
    (a b r q : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hr : 0≤r) (hq : 0≤q) (hq1 : q≤1) [Nonempty (ForkDomain N K r q)]
    (ε : ℝ) (hε : 0≤ε) :
    (forkLaw N p K).real {J | ε≤|supremum a b r q J-∫J',supremum a b r q J' ∂forkLaw N p K|}≤
      2*Real.exp (-ε^2/(2*(forkConstant N K:ℝ))) := by
  let X := fun J => supremum (N:=N) (p:=p) (K:=K) a b r q J-
    ∫J',supremum a b r q J' ∂forkLaw N p K
  have hG := supremum_centered_hasSubgaussianMGF hN hp hK a b r q ha hab hb hr hq hq1
  have hs : {J | ε≤|X J|}={J | ε≤X J}∪{J | ε≤-X J} := by
    ext J
    change ε≤|X J| ↔ ε≤X J ∨ ε≤-X J
    exact le_abs
  change (forkLaw N p K).real {J | ε≤|X J|}≤_
  rw [hs]
  exact (measureReal_union_le _ _).trans
    (by simpa only [two_mul,Pi.neg_apply] using add_le_add (hG.measure_ge_le hε) (hG.neg.measure_ge_le hε))

end SphericalAging.GaussianOrthogonalForkSupremum
