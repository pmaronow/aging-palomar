module

public import SphericalAging.ResidualTensorAlgorithm

public section

/-! Exact original residual energy and overlap of the constructed algorithm.
No dimension-change identity is supplied as an assumption. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ResidualTensorEnergy
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure GaussianLandscape
open ResidualTensorCoordinates ResidualTensorModel ResidualTensorAlgorithm
open TensorOrthogonalAction TensorHamiltonianRotation ExternalFieldUniformCost ExternalFieldElementaryPenalty ExternalFieldSharpScalar
open scoped InnerProductSpace NNReal

@[expose]  def physicalProjection {N : ℕ} (W : Submodule ℝ (Vector N))
    (F : Vector N≃ₗᵢ[ℝ]Vector N) (x : Vector N) : Vector N :=
  F ((Wᗮ).orthogonalProjectionOnto (F.symm x))

 theorem Hamiltonian_residual_coordinates {N n p : ℕ} (hN : 0<N) (hn : 0<n) (hp : 1≤p)
    (W : Submodule ℝ (Vector N)) (b : OrthonormalBasis (Fin n) ℝ Wᗮ)
    (F : Vector N≃ₗᵢ[ℝ]Vector N) (D : TensorSpace N p) (A : TensorSpace N p→Vector N)
    (J : TensorSpace n p) :
    Hamiltonian N p (embedding W b F J).ofLp
      (physicalProjection W F (A (originalInput W b F D J)))/(N:ℝ)=
    Real.sqrt ((n:ℝ)/(N:ℝ))*Hamiltonian n p J.ofLp (output W b F D A J)/(n:ℝ) := by
  let R := (coordinates (p:=p) W b).symm J
  have hr : (residualTensorSpace W).orthogonalProjectionOnto (R : TensorSpace N p)=R :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self R
  have hh := original_normalized_Hamiltonian hN hn hp W b (R : TensorSpace N p)
    ((Wᗮ).orthogonalProjectionOnto (F.symm (A (originalInput W b F D J))))
  rw [hr,(coordinates (p:=p) W b).apply_symm_apply] at hh
  have hrot := Hamiltonian_rotated F (R : TensorSpace N p).ofLp
    ((Wᗮ).orthogonalProjectionOnto (F.symm (A (originalInput W b F D J))))
  change Hamiltonian N p (embedding W b F J).ofLp
    (physicalProjection W F (A (originalInput W b F D J)))=
    Hamiltonian N p (R : TensorSpace N p).ofLp
      ((Wᗮ).orthogonalProjectionOnto (F.symm (A (originalInput W b F D J)))) at hrot
  rw [hrot]
  change Hamiltonian N p (R : TensorSpace N p).ofLp
      ((Wᗮ).orthogonalProjectionOnto (F.symm (A (originalInput W b F D J))))/(N:ℝ)=
    Real.sqrt ((n:ℝ)/(N:ℝ))*Hamiltonian n p J.ofLp
      ((Real.sqrt (n:ℝ)/Real.sqrt (N:ℝ)) • b.repr
        ((Wᗮ).orthogonalProjectionOnto (F.symm (A (originalInput W b F D J)))))/(n:ℝ)
  simpa only [mul_div_assoc] using hh

 theorem cost_identity {N n p : ℕ} {L : ℝ≥0} (hN : 0<N) (hn : 0<n) (hnN : n≤N) (hp : 1≤p)
    (W : Submodule ℝ (Vector N)) (b : OrthonormalBasis (Fin n) ℝ Wᗮ)
    (F : Vector N≃ₗᵢ[ℝ]Vector N) (D : TensorSpace N p) (A : TensorSpace N p→Vector N)
    (hA : LipschitzWith L A) (hball : ∀J,‖A J‖≤Real.sqrt N) (u : Wᗮ) (hu : ‖u‖=1)
    (J : TensorSpace n p) :
    Hamiltonian N p (embedding W b F J).ofLp
      (physicalProjection W F (A (originalInput W b F D J)))/(N:ℝ)+
      Real.sqrt ((n:ℝ)/(N:ℝ))*betaD p*
        |⟪F u,A (originalInput W b F D J)⟫_ℝ/Real.sqrt (N:ℝ)|^p=
    Real.sqrt ((n:ℝ)/(N:ℝ))*(
      Hamiltonian n p J.ofLp ((ballAlgorithm hN hnN W b F D A hA hball u hu).output J.ofLp)/(n:ℝ)+
      betaD p*|⟪(ballAlgorithm hN hnN W b F D A hA hball u hu).direction,
        (ballAlgorithm hN hnN W b F D A hA hball u hu).output J.ofLp⟫_ℝ/(n:ℝ)|^p) := by
  simp only [ballAlgorithm,WithLp.toLp_ofLp]
  rw [Hamiltonian_residual_coordinates hN hn hp W b F D A J,overlap_identity hN hn W b F D A u J]
  ring

end SphericalAging.ResidualTensorEnergy
