module

public import SphericalAging.HamiltonianOneReplicaEdgeCoefficients
public import SphericalAging.GaussianLinearSupBound

public section

/-! Genuine compact comparison for the full polynomial edge remainder.
The exact ordered-tensor increment covariance is bounded before comparison. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.HamiltonianOneReplicaEdgeComparison
open Set MeasureTheory ProbabilityTheory FiniteModel GaussianComparison GaussianLinearSupBound
open GaussianIntegrationByParts HamiltonianDerivativeCovariance HamiltonianTangentJetCovariance
open HamiltonianOneReplicaEdgeCoefficients
open scoped BigOperators InnerProductSpace
variable {N p : ℕ}
local instance : NormedAddCommGroup (Vector N→L[ℝ]ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (Vector N→L[ℝ]ℝ) := ContinuousLinearMap.toNormedSpace

 theorem remainderCoeff_continuous (a b : ℝ) (x : Vector N) :
    Continuous (remainderCoeff (p:=p) a b x) := by
  apply continuous_pi
  intro k
  cases k with
  | inl I =>
    exact continuous_const.mul
      (((coefficient_contDiff I).continuous.comp (continuous_const.add continuous_id)).sub
        continuous_const |>.sub (fderiv ℝ (hamiltonianCoefficient I) x).continuous)
  | inr I =>
    exact continuous_const.mul
      ((coefficient_contDiff I).continuous.comp (continuous_const.add continuous_id))

 theorem actual_remainder_supremum_mean_bound {I : Type*} [TopologicalSpace I] [CompactSpace I]
    [Nonempty I] (hN : 0<N) (hp : 2≤p) {a b r d : ℝ}
    (ha : 0≤a) (hab : a≤b) (hr : 0≤r) (hd : 0≤d) (x : Vector N)
    (hx : ‖x‖^2=(N:ℝ)*r) (u : I→Vector N) (hu : Continuous u)
    (htangent : ∀i,inner ℝ (u i) x=0) (hnorm : ∀i,‖u i‖^2=(N:ℝ)*d) :
    (∫z,gaussianSup (fun _ => 0) (fun i => remainderCoeff (p:=p) a b x (u i)) z
      ∂gaussianCoordinates (TensorIndex N p⊕TensorIndex N p))/(N:ℝ)≤
      Real.sqrt (d*edgeRate p a b r (r+d)) := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hR := edgeRate_nonnegative (p:=p) ha hab hr (by linarith : r≤r+d)
  have hb (i : I) : ‖u i‖≤Real.sqrt N*Real.sqrt d := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hn.le,Real.sq_sqrt hd,hnorm i]
  have hci : ∀i j : I, (∑k : TensorIndex N p⊕TensorIndex N p,
      (remainderCoeff a b x (u i) k-remainderCoeff a b x (u j) k)^2)≤
      (Real.sqrt (edgeRate p a b r (r+d)))^2*‖u i-u j‖^2 := by
    intro i j
    rw [Real.sq_sqrt hR]
    exact actual_remainder_increment_bound hN hp ha hab hr hd x (u i) (u j)
      hx (htangent i) (htangent j) (hnorm i) (hnorm j)
  have hc := compact_increment_mean_le (I:=I) (κ:=TensorIndex N p⊕TensorIndex N p) (N:=N)
    hN ((remainderCoeff_continuous (p:=p) a b x).comp hu) hu
    (Real.sqrt_nonneg _) (by positivity : 0≤Real.sqrt N*Real.sqrt d) hb hci
  apply (div_le_iff₀ hn).mpr
  apply hc.trans_eq
  rw [Real.sqrt_mul hd]
  have hs : Real.sqrt N*Real.sqrt N=(N:ℝ) := Real.mul_self_sqrt hn.le
  calc
    _ = (Real.sqrt N*Real.sqrt N)*(Real.sqrt d*Real.sqrt (edgeRate p a b r (r+d))) := by ring
    _ = _ := by rw [hs];ring

@[expose]  def singleRemainder (a b : ℝ) (x u : Vector N) (J : Disorder N p×Disorder N p) : ℝ :=
  Real.sqrt a*(Hamiltonian N p J.1 (x+u)-Hamiltonian N p J.1 x-
    fderiv ℝ (Hamiltonian N p J.1) x u)+Real.sqrt (b-a)*Hamiltonian N p J.2 (x+u)

 theorem remainder_affine_eq_actual (a b : ℝ) (x u : Vector N)
    (J : (TensorIndex N p⊕TensorIndex N p)→ℝ) :
    gaussianAffine (fun _ : Vector N => 0) (remainderCoeff (p:=p) a b x) J u=
      singleRemainder a b x u ((fun I => J (Sum.inl I)),(fun I => J (Sum.inr I))) := by
  have hg := Hamiltonian_derivative_tensorLinear (fun I => J (Sum.inl I)) 1 x (fun _ => u)
  simp only [iteratedFDeriv_one_apply,tensorLinear,coefficientDerivative] at hg
  rw [gaussianAffine,Fintype.sum_sum_type]
  simp only [remainderCoeff,zero_add,singleRemainder]
  rw [hg,hamiltonian_eq_sum_coefficients,hamiltonian_eq_sum_coefficients,hamiltonian_eq_sum_coefficients]
  rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  simp only [Finset.mul_sum,firstCoeff]
  congr 1 <;> (apply Finset.sum_congr rfl; intro I _; ring)

@[expose]  def singleSup {I : Type*} (a b : ℝ) (x : Vector N) (u : I→Vector N)
    (J : Disorder N p×Disorder N p) : ℝ := sSup (range (fun i => singleRemainder a b x (u i) J))

 theorem singleSup_eq_gaussianSup {I : Type*} (a b : ℝ) (x : Vector N) (u : I→Vector N)
    (J : Disorder N p×Disorder N p) :
    singleSup a b x u J=gaussianSup (fun _ => 0) (fun i => remainderCoeff (p:=p) a b x (u i))
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : TensorIndex N p⊕TensorIndex N p => ℝ)).symm J) := by
  unfold singleSup gaussianSup
  congr 1
  apply congrArg range
  funext i
  have he := (MeasurableEquiv.sumPiEquivProdPi (fun _ : TensorIndex N p⊕TensorIndex N p => ℝ)).apply_symm_apply J
  change ((fun I => (MeasurableEquiv.sumPiEquivProdPi (fun _ : TensorIndex N p⊕TensorIndex N p => ℝ)).symm J (Sum.inl I)),
    (fun I => (MeasurableEquiv.sumPiEquivProdPi (fun _ : TensorIndex N p⊕TensorIndex N p => ℝ)).symm J (Sum.inr I)))=J at he
  have hh := (remainder_affine_eq_actual a b x (u i)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : TensorIndex N p⊕TensorIndex N p => ℝ)).symm J)).symm
  rw [he] at hh
  exact hh

 theorem singleSup_integrable {I : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]
    (a b : ℝ) (x : Vector N) (u : I→Vector N) (hu : Continuous u) :
    Integrable (singleSup (p:=p) a b x u) ((disorderLaw N p).prod (disorderLaw N p)) := by
  have hmp := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : TensorIndex N p⊕TensorIndex N p => gaussianReal 0 1)
  have he : singleSup (p:=p) a b x u=fun J => gaussianSup (fun _ : I => 0)
      (fun i => remainderCoeff (p:=p) a b x (u i))
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : TensorIndex N p⊕TensorIndex N p => ℝ)).symm J) :=
    funext (singleSup_eq_gaussianSup a b x u)
  rw [he]
  simpa only [disorderLaw,gaussianCoordinates,Function.comp_def] using hmp.integrable_comp_of_integrable
    (integrable_gaussianSup (m:=fun _ : I => (0:ℝ)) continuous_const
      ((remainderCoeff_continuous (p:=p) a b x).comp hu))

 theorem singleSup_expectation_bound {I : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]
    (hN : 0<N) (hp : 2≤p) {a b r d : ℝ} (ha : 0≤a) (hab : a≤b) (hr : 0≤r) (hd : 0≤d)
    (x : Vector N) (hx : ‖x‖^2=(N:ℝ)*r) (u : I→Vector N) (hu : Continuous u)
    (htangent : ∀i,inner ℝ (u i) x=0) (hnorm : ∀i,‖u i‖^2=(N:ℝ)*d) :
    (∫J,singleSup (p:=p) a b x u J ∂(disorderLaw N p).prod (disorderLaw N p))/(N:ℝ)≤
      Real.sqrt (d*edgeRate p a b r (r+d)) := by
  simp_rw [singleSup_eq_gaussianSup]
  have he := (measurePreserving_sumPiEquivProdPi_symm
    (fun _ : TensorIndex N p⊕TensorIndex N p => gaussianReal 0 1)).integral_comp'
    (gaussianSup (fun _ : I => (0:ℝ)) (fun i => remainderCoeff (p:=p) a b x (u i)))
  change (∫J : Disorder N p×Disorder N p,
    gaussianSup (fun _ : I => 0) (fun i => remainderCoeff (p:=p) a b x (u i))
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : TensorIndex N p⊕TensorIndex N p => ℝ)).symm J)
    ∂(disorderLaw N p).prod (disorderLaw N p))=_ at he
  rw [he]
  exact actual_remainder_supremum_mean_bound hN hp ha hab hr hd x hx u hu htangent hnorm

end SphericalAging.HamiltonianOneReplicaEdgeComparison
