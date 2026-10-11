module

public import SphericalAging.ResidualTensorMeanCost

public section

/-! The field cost is evaluated in the genuine canonical residual Gaussian,
using the constructed pure-tensor isometry. It includes zero queries. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ResidualGaussianMeanCost
open Set Filter MeasureTheory ProbabilityTheory FiniteModel GaussianLandscape AdaptiveGradientDisclosure
open ResidualTensorCoordinates ResidualTensorAlgorithm ResidualTensorEnergy ResidualTensorMeanCost
open TensorOrthogonalAction OrthogonalGaussianDisclosure ExternalFieldUniformCost
open ExternalFieldElementaryPenalty ExternalFieldSharpScalar SphereGibbsEntropy
open scoped Topology InnerProductSpace NNReal

 theorem disorder_coordinates_preserving (n p : ℕ) :
    MeasurePreserving (WithLp.ofLp : TensorSpace n p→Disorder n p)
      (stdGaussian (TensorSpace n p)) (disorderLaw n p) := by
  refine ⟨(PiLp.continuous_ofLp 2 (fun _ : TensorIndex n p => ℝ)).measurable,?_⟩
  rw [←(ordered_tensor_hasLaw n p).map_eq,Measure.map_map (by fun_prop) (by fun_prop)]
  rw [show (WithLp.ofLp : TensorSpace n p→Disorder n p)∘WithLp.toLp 2=id by funext J;rfl]
  exact Measure.map_id

 theorem value_measurable {N n p : ℕ} {L : ℝ≥0} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) (F : Vector N≃ₗᵢ[ℝ]Vector N)
    (D : TensorSpace N p) (A : TensorSpace N p→Vector N) (hA : LipschitzWith L A) (u : Wᗮ) :
    Measurable (value W b F D A u) := by
  have hJ : Measurable (WithLp.toLp 2 : Disorder n p→TensorSpace n p) :=
    (PiLp.continuous_toLp 2 (fun _ : TensorIndex n p => ℝ)).measurable
  have hE : Measurable (fun J : Disorder n p => embedding W b F (WithLp.toLp 2 J)) :=
    (embedding W b F).continuous.measurable.comp hJ
  have hI : Measurable (fun J : Disorder n p => originalInput W b F D (WithLp.toLp 2 J)) := measurable_const.add hE
  have hO := hA.continuous.measurable.comp hI
  have hProj : Continuous (physicalProjection W F) :=
    F.continuous.comp ((Wᗮ).subtypeL.continuous.comp ((Wᗮ).orthogonalProjectionOnto.continuous.comp F.symm.continuous))
  have hd : Measurable (fun J : Disorder n p => (embedding W b F (WithLp.toLp 2 J)).ofLp) :=
    (PiLp.continuous_ofLp 2 (fun _ : TensorIndex N p => ℝ)).measurable.comp hE
  have hi : Measurable (fun J : Disorder n p =>
      ⟪F u,A (originalInput W b F D (WithLp.toLp 2 J))⟫_ℝ/Real.sqrt (N:ℝ)) :=
    (((continuous_const.inner continuous_id).measurable).comp hO).div_const _
  exact (((Hamiltonian_joint_continuous N p).measurable.comp
      (hd.prodMk (hProj.measurable.comp hO))).div_const _).add
    (((continuous_abs.measurable.comp hi).pow_const p).const_mul (betaD p))

@[expose]  def residualValue {N p : ℕ} (W : Submodule ℝ (Vector N)) (F : Vector N≃ₗᵢ[ℝ]Vector N)
    (D : TensorSpace N p) (A : TensorSpace N p→Vector N) (u : Wᗮ)
    (R : residualTensorSpace (p:=p) W) : ℝ :=
  Hamiltonian N p (action F R.val).ofLp (physicalProjection W F (A (D+action F R.val)))/(N:ℝ)+
    betaD p*|⟪F u,A (D+action F R.val)⟫_ℝ/Real.sqrt (N:ℝ)|^p

 theorem residualValue_eq_coordinates {N n p : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) (F : Vector N≃ₗᵢ[ℝ]Vector N)
    (D : TensorSpace N p) (A : TensorSpace N p→Vector N) (u : Wᗮ)
    (R : residualTensorSpace (p:=p) W) :
    residualValue W F D A u R=value W b F D A u ((coordinates W b R).ofLp) := by
  have he : embedding W b F (coordinates W b R)=action F R.val := by
    change action F ((coordinates W b).symm (coordinates W b R) : TensorSpace N p)=_
    rw [LinearIsometryEquiv.symm_apply_apply]
  simp only [residualValue,value,originalInput,WithLp.toLp_ofLp,he]

 theorem residual_integral_eq {N n p : ℕ} {L : ℝ≥0} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) (F : Vector N≃ₗᵢ[ℝ]Vector N)
    (D : TensorSpace N p) (A : TensorSpace N p→Vector N) (hA : LipschitzWith L A) (u : Wᗮ) :
    (∫R,residualValue W F D A u R ∂stdGaussian (residualTensorSpace W))=
      ∫J,value W b F D A u J ∂disorderLaw n p := by
  have hLaw := (disorder_coordinates_preserving n p).comp (coordinates_gaussian (p:=p) W b)
  have hi := hLaw.hasLaw.integral_comp (value_measurable W b F D A hA u).aestronglyMeasurable
  convert hi using 1
  congr 1
  funext R
  exact residualValue_eq_coordinates W b F D A u R

 theorem mean_bound {N n p k : ℕ} {L : ℝ≥0} (hN : 0<N) (hn : 0<n) (hnN : n≤N)
    (hNk : N≤n+k) (hp : 3≤p) {ε : ℝ} (hε : 0≤ε)
    (hb : ∀B : BallFieldAlgorithm n p L,meanCost B≤thresholdEnergy p+ε)
    (W : Submodule ℝ (Vector N)) (b : OrthonormalBasis (Fin n) ℝ Wᗮ)
    (F : Vector N≃ₗᵢ[ℝ]Vector N) (D : TensorSpace N p) (A : TensorSpace N p→Vector N)
    (hA : LipschitzWith L A) (hball : ∀J,‖A J‖≤Real.sqrt N) (u : Wᗮ) (hu : ‖u‖=1) :
    (∫R,residualValue W F D A u R ∂stdGaussian (residualTensorSpace W))≤
      thresholdEnergy p+ε+betaD p*(k:ℝ)/(N:ℝ) := by
  rw [residual_integral_eq W b F D A hA u]
  exact ResidualTensorMeanCost.mean_bound hN hn hnN hNk hp hε hb W b F D A hA hball u hu

end SphericalAging.ResidualGaussianMeanCost
