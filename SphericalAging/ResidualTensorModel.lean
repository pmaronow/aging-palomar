module

public import SphericalAging.ResidualTensorCoordinates
public import SphericalAging.ForkNormalizedEnergy

public section

/-! Literal residual pure-spin model in dimension finrank(W-perp).
The vector and tensor coordinates, Gaussian law and actual Hamiltonian
change of variables are derived from the original ordered tensor. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ResidualTensorModel
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open ResidualTensorCoordinates TensorHamiltonianRotation LandscapeDerivatives ForkNormalizedEnergy
open scoped InnerProductSpace

@[expose]  def vectorBasis {N : ℕ} (W : Submodule ℝ (Vector N)) :
    OrthonormalBasis (Fin (Module.finrank ℝ Wᗮ)) ℝ Wᗮ := stdOrthonormalBasis ℝ Wᗮ

@[expose]  def tensorCoordinates {N p : ℕ} (W : Submodule ℝ (Vector N)) :
    residualTensorSpace (p:=p) W≃ₗᵢ[ℝ]TensorSpace (Module.finrank ℝ Wᗮ) p :=
  coordinates W (vectorBasis W)

 theorem residual_finrank {N p : ℕ} (W : Submodule ℝ (Vector N)) :
    Module.finrank ℝ (residualTensorSpace (p:=p) W)=(Module.finrank ℝ Wᗮ)^p := by
  have hh := (tensorCoordinates (p:=p) W).toLinearEquiv.finrank_eq
  simpa only [TensorSpace,TensorIndex,finrank_euclideanSpace,Fintype.card_fun,Fintype.card_fin] using hh

 theorem tensorCoordinates_gaussian {N p : ℕ} (W : Submodule ℝ (Vector N)) :
    MeasurePreserving (tensorCoordinates (p:=p) W) (stdGaussian (residualTensorSpace (p:=p) W))
      (stdGaussian (TensorSpace (Module.finrank ℝ Wᗮ) p)) :=
  coordinates_gaussian W (vectorBasis W)

 theorem original_Hamiltonian_coordinates {N n p : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) (J : TensorSpace N p) (y : Wᗮ) :
    Hamiltonian N p J.ofLp (y : Vector N)=normalization N p*
      ⟪coordinates W b ((residualTensorSpace W).orthogonalProjectionOnto J),
        pureTensor (fun _ : Fin p => b.repr y)⟫_ℝ := by
  let Y : residualTensorSpace (p:=p) W :=
    ⟨pureTensor (fun _ : Fin p => (y : Vector N)),Submodule.subset_span ⟨(fun _ => y),rfl⟩⟩
  have hh := (coordinates (p:=p) W b).inner_map_map ((residualTensorSpace W).orthogonalProjectionOnto J) Y
  rw [coordinates_pureTensor] at hh
  have hp := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right Y J
  rw [Hamiltonian_eq_tensor_inner,WithLp.toLp_ofLp,hh]
  exact congrArg (fun x : ℝ => normalization N p*x) hp.symm

 theorem normalization_ratio {N n p : ℕ} (hN : 0<N) (hn : 0<n) (hp : 1≤p) :
    normalization N p/(N:ℝ)=Real.sqrt ((n:ℝ)/(N:ℝ))*
      (Real.sqrt (n:ℝ)/Real.sqrt (N:ℝ))^p*normalization n p/(n:ℝ) := by
  have hA : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hB : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hNe : normalization N p=1/Real.sqrt (N:ℝ)^(p-1) :=
    (eq_div_iff (pow_ne_zero _ hA.ne')).mpr (normalization_sqrt_power hN)
  have hne : normalization n p=1/Real.sqrt (n:ℝ)^(p-1) :=
    (eq_div_iff (pow_ne_zero _ hB.ne')).mpr (normalization_sqrt_power hn)
  have hAp : Real.sqrt (N:ℝ)^p=Real.sqrt (N:ℝ)^(p-1)*Real.sqrt (N:ℝ) := by
    rw [←pow_succ];congr 1;omega
  have hBp : Real.sqrt (n:ℝ)^p=Real.sqrt (n:ℝ)^(p-1)*Real.sqrt (n:ℝ) := by
    rw [←pow_succ];congr 1;omega
  rw [Real.sqrt_div (Nat.cast_nonneg n),hNe,hne,div_pow,hAp,hBp,
    ←Real.sq_sqrt (Nat.cast_nonneg N),←Real.sq_sqrt (Nat.cast_nonneg n)]
  simp only [Real.sqrt_sq (Real.sqrt_nonneg _)]
  field_simp
  <;> ring

 theorem original_normalized_Hamiltonian {N n p : ℕ} (hN : 0<N) (hn : 0<n) (hp : 1≤p)
    (W : Submodule ℝ (Vector N)) (b : OrthonormalBasis (Fin n) ℝ Wᗮ)
    (J : TensorSpace N p) (y : Wᗮ) :
    Hamiltonian N p J.ofLp (y : Vector N)/(N:ℝ)=Real.sqrt ((n:ℝ)/(N:ℝ))*
      (Hamiltonian n p (coordinates W b ((residualTensorSpace W).orthogonalProjectionOnto J)).ofLp
        ((Real.sqrt (n:ℝ)/Real.sqrt (N:ℝ)) • b.repr y)/(n:ℝ)) := by
  rw [original_Hamiltonian_coordinates W b J y,Hamiltonian_spatial_smul,Hamiltonian_eq_tensor_inner,WithLp.toLp_ofLp]
  have hh := normalization_ratio hN hn hp
  calc
    _ = (normalization N p/(N:ℝ))*
        ⟪coordinates W b ((residualTensorSpace W).orthogonalProjectionOnto J),
          pureTensor (fun _ : Fin p => b.repr y)⟫_ℝ := by ring
    _ = _ := by rw [hh];ring

end SphericalAging.ResidualTensorModel
