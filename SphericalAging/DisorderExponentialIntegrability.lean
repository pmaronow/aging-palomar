module

public import SphericalAging.GaussianLandscapeMoments
public import SphericalAging.HamiltonianParameter

public section

/-! Actual Gaussian-disorder exponential integrability for finite-N
variational equations. Ordered tensor coordinates are controlled by the
actual multilinear landscape norm. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace BigOperators NNReal ENNReal
namespace SphericalAging.DisorderExponentialIntegrability
open FiniteModel GaussianLandscape HardSphereDynamics
set_option maxHeartbeats 1800000

/-- Every original ordered coupling is the actual tensor evaluated on
its ordered standard basis tuple. -/
theorem tensorForm_apply_basis {N p : ℕ} (J : Disorder N p) (I : TensorIndex N p) :
    tensorForm N p J (fun k => basisVector (I k))=J I := by
  classical
  rw [tensorForm_apply,Finset.sum_eq_single I]
  · simp [basisVector,Pi.single_apply]
  · intro L _ hLI
    have hne : ∃ k,L k ≠ I k := by
      by_contra h
      push_neg at h
      exact hLI (funext h)
    obtain ⟨k,hk⟩ := hne
    have hz : (∏ j : Fin p,basisVector (I j) (L j))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      simp [basisVector,Pi.single_apply,Ne.symm hk]
    simp only [hz,mul_zero]
  · simp

/-- The finite sup norm of the actual disorder is controlled by its
actual multilinear operator norm. -/
theorem disorder_norm_le_tensorForm {N p : ℕ} (J : Disorder N p) :
    ‖J‖ ≤ ‖tensorForm N p J‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro I
  rw [← tensorForm_apply_basis J I]
  have hh := (tensorForm N p J).le_opNorm (fun k => basisVector (I k))
  simpa only [basisVector,EuclideanSpace.norm_single,norm_one,Finset.prod_const_one,mul_one] using hh

theorem disorder_norm_le_landscape {N p : ℕ} (hN : 0 < N) (J : Disorder N p) :
    ‖J‖ ≤ Real.sqrt (N : ℝ)*landscapeNorm N p J := by
  have hr : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have he : Real.sqrt (N : ℝ)*landscapeNorm N p J=‖tensorForm N p J‖ := by
    unfold landscapeNorm
    field_simp
  rw [he]
  exact disorder_norm_le_tensorForm J

/-- Every finite linear exponential of the genuine ordered Gaussian
coupling sup norm is integrable. -/
theorem disorder_norm_exp_integrable {N p : ℕ} (hN : 0 < N) (hp : 0 < p) (b : ℝ≥0) :
    Integrable (fun J : Disorder N p => Real.exp ((b : ℝ)*‖J‖)) (disorderLaw N p) := by
  have hi := (GaussianLandscapeMoments.uniform_exponential_moment hN hp
    ((b : ℝ)*Real.sqrt (N : ℝ))).1
  apply hi.mono' (Real.continuous_exp.comp (continuous_norm.const_mul (b : ℝ))).aestronglyMeasurable
  exact .of_forall (fun J => by
    change ‖Real.exp ((b : ℝ)*‖J‖)‖ ≤ _
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (disorder_norm_le_landscape hN J) b.coe_nonneg])

/-- Multiplication by any fixed nonnegative constant and constant
addition in the exponent preserve actual Gaussian integrability. -/
theorem disorder_affine_exp_integrable {N p : ℕ} (hN : 0 < N) (hp : 0 < p)
    (a : ℝ) (b : ℝ≥0) :
    Integrable (fun J : Disorder N p => Real.exp (a+(b : ℝ)*‖J‖)) (disorderLaw N p) := by
  simpa only [Real.exp_add] using (disorder_norm_exp_integrable hN hp b).const_mul (Real.exp a)

open HamiltonianParameter

/-- The actual cutoff drift has a global state Lipschitz constant growing
linearly with the genuine disorder norm. -/
theorem cutoffDrift_affine_state_lipschitz {N p : ℕ} (β : ℝ) (R : ℝ) (hR : 0 < R) :
    ∃ K0 K1 : ℝ≥0, ∀ J : Disorder N p,
      LipschitzWith (K0 + ‖J‖₊*K1) (cutoffCoefficient R hR (hamiltonianDrift β J)) := by
  obtain ⟨K0, hK0⟩ := cutoffCoefficient_lipschitz R hR (hamiltonianDrift β (0 : Disorder N p))
    ((contDiff_hamiltonianDrift β (0 : Disorder N p)).of_le (by simp))
  have hKi : ∀ I : TensorIndex N p, ∃ K : ℝ≥0, LipschitzWith K (couplingDrift β R hR I) :=
    couplingDrift_lipschitz β R hR
  choose Ki hKi using hKi
  refine ⟨K0, ∑ I, Ki I, fun J => LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_sum,coe_nnnorm]
  have heq : cutoffCoefficient R hR (hamiltonianDrift β J) x -
      cutoffCoefficient R hR (hamiltonianDrift β J) y =
      (cutoffCoefficient R hR (hamiltonianDrift β (0 : Disorder N p)) x -
        cutoffCoefficient R hR (hamiltonianDrift β (0 : Disorder N p)) y) +
      ∑ I, J I • (couplingDrift β R hR I x - couplingDrift β R hR I y) := by
    rw [cutoffDrift_vector_affine β J R hR x, cutoffDrift_vector_affine β J R hR y]
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel
  rw [heq]
  calc
    _ ≤ ‖cutoffCoefficient R hR (hamiltonianDrift β (0 : Disorder N p)) x -
        cutoffCoefficient R hR (hamiltonianDrift β (0 : Disorder N p)) y‖ +
        ∑ I, ‖J I • (couplingDrift β R hR I x - couplingDrift β R hR I y)‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ (K0 : ℝ)*‖x-y‖ + ∑ I, ‖J‖ * ((Ki I : ℝ)*‖x-y‖) := by
      apply add_le_add
      · simpa only [dist_eq_norm] using hK0.dist_le_mul x y
      · apply Finset.sum_le_sum
        intro I _
        rw [norm_smul]
        apply mul_le_mul (norm_le_pi_norm J I)
          (by simpa only [dist_eq_norm] using (hKi I).dist_le_mul x y) (norm_nonneg _)
          (norm_nonneg J)
    _ = _ := by rw [← Finset.mul_sum, ← Finset.sum_mul]; ring

end SphericalAging.DisorderExponentialIntegrability
