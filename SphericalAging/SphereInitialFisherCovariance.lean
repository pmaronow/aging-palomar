module

public import SphericalAging.SphereInitialFisher
public import SphericalAging.HamiltonianDerivativeCovariance
public import SphericalAging.HamiltonianParameter
public import SphericalAging.GaussianLandscapeMoments

public section

/-! Exact actual Gaussian expectation of the tangential Hamiltonian
gradient at a sphere point, the covariance behind the initial Fisher
information. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace ENNReal
namespace SphericalAging.SphereInitialFisherCovariance
open HardSphereDynamics FiniteModel HamiltonianDerivativeCovariance
open SphereInitialLaw SphereInitialFisher HamiltonianParameter
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

lemma directional_gradient_memLp {N p : ℕ} (x a : State N) :
    MemLp (fun J : Disorder N p => inner ℝ (gradient (Hamiltonian N p J) x) a) 2 (disorderLaw N p) := by
  simpa only [iteratedFDeriv_one_apply,inner_gradient_left] using
    Hamiltonian_derivative_memLp (p := p) 1 x (fun _ => a)

lemma projected_gradient_norm_sq_eq {N p : ℕ} (J : Disorder N p) (x : State N) :
    ‖projection x (gradient (Hamiltonian N p J) x)‖^2=
      ∑ i : Fin N,(inner ℝ (gradient (Hamiltonian N p J) x) (projection x (basisVector i)))^2 := by
  rw [← real_inner_self_eq_norm_sq,← coordinate_square_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← basis_inner,projection_self_adjoint]

theorem projected_gradient_sq_integrable {N p : ℕ} (x : State N) :
    Integrable (fun J : Disorder N p => ‖projection x (gradient (Hamiltonian N p J) x)‖^2) (disorderLaw N p) := by
  simpa only [projected_gradient_norm_sq_eq] using integrable_finsetSum Finset.univ
    (fun i _ => (directional_gradient_memLp (p := p) x (projection x (basisVector i))).integrable_sq)

/-- Exact tangential gradient covariance at every actual sphere point. -/
theorem projected_gradient_square_expectation {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    (x : State N) (hx : OnSphere x) :
    (∫ J : Disorder N p,‖projection x (gradient (Hamiltonian N p J) x)‖^2 ∂disorderLaw N p)=
      (p : ℝ)*((N : ℝ)-1) := by
  have hn : (N : ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hN)
  have hrad (i : Fin N) : inner ℝ x (projection x (basisVector i))=0 :=
    projection_tangent (Nat.ne_of_gt hN) x (basisVector i) hx
  have hxx : inner ℝ x x=(N : ℝ) := hx
  have hc (i : Fin N) : (∫ J : Disorder N p,
      (inner ℝ (gradient (Hamiltonian N p J) x) (projection x (basisVector i)))^2 ∂disorderLaw N p)=
      (p : ℝ)*inner ℝ (projection x (basisVector i)) (projection x (basisVector i)) := by
    have hh := Hamiltonian_gradient_covariance_overlap hN hp x x (projection x (basisVector i)) (projection x (basisVector i))
    simpa only [← sq,hxx,div_self hn,one_pow,hrad,real_inner_comm (projection x (basisVector i)) x,
      mul_zero,add_zero,mul_one] using hh
  simp_rw [projected_gradient_norm_sq_eq]
  rw [integral_finsetSum Finset.univ
    (fun i _ => (directional_gradient_memLp (p := p) x (projection x (basisVector i))).integrable_sq)]
  simp only [hc,← Finset.mul_sum]
  rw [← projectionTraceSquare,projectionTraceSquare_onSphere (Nat.ne_of_gt hN) x hx]

lemma Hamiltonian_gradient_joint_continuous (N p : ℕ) :
    Continuous (fun q : Disorder N p × State N => gradient (Hamiltonian N p q.1) q.2) := by
  have hc : Continuous (fun q : Disorder N p × State N =>
      ∑ I : TensorIndex N p,(q.1 I) • hamiltonianGradient (disorderBasis I) q.2) := by
    apply continuous_finsetSum
    intro I _
    exact ((continuous_apply I).comp continuous_fst).smul
      ((hamiltonianGradient_contDiff (disorderBasis I)).continuous.comp continuous_snd)
  convert hc using 1
  funext q
  simpa only [hamiltonianGradient,Finset.sum_apply,Pi.smul_apply] using congrFun (gradient_sum_basis q.1) q.2

lemma projected_gradient_joint_continuous (N p : ℕ) :
    Continuous (fun q : Disorder N p × State N => projection q.2 (gradient (Hamiltonian N p q.1) q.2)) := by
  unfold projection
  exact (Hamiltonian_gradient_joint_continuous N p).sub
    (((continuous_snd.inner (Hamiltonian_gradient_joint_continuous N p)).div_const (N : ℝ)).smul continuous_snd)

theorem projected_gradient_joint_square_integrable {N p : ℕ} (hN : 0<N) (hp : 0<p) :
    Integrable (fun q : Disorder N p × State N => ‖projection q.2 (gradient (Hamiltonian N p q.1) q.2)‖^2)
      ((disorderLaw N p).prod (sphereLaw N)) := by
  have hQ : Integrable (fun J : Disorder N p => (GaussianLandscape.landscapeNorm N p J)^2) (disorderLaw N p) := by
    simpa only [Real.rpow_two] using
      (GaussianLandscapeMoments.uniform_real_power_moment (by omega : 1≤N) hp (by norm_num : (0 : ℝ)≤2)).1
  have hi := (hQ.const_mul ((p : ℝ)^2*(N : ℝ))).comp_fst (sphereLaw N)
  apply hi.mono' ((projected_gradient_joint_continuous N p).norm.pow 2).aestronglyMeasurable
  have hs := (Measure.quasiMeasurePreserving_snd (μ := disorderLaw N p) (ν := sphereLaw N)).ae (sphereLaw_support hN)
  filter_upwards [hs] with q hq
  change ‖‖projection q.2 (gradient (Hamiltonian N p q.1) q.2)‖^2‖≤_
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact (Hamiltonian_tangent_gradient_sq_bound hN q.1 q.2 ((onSphere_iff_norm_sq _).mpr hq)).trans_eq (by ring)

/-- The true initial annealed Fisher value follows from Gaussian
covariance and product Fubini under the actual sphere law. -/
theorem initial_fisher_normalized_annealed_identity {N p : ℕ} (hN : 0<N) (hp : 2≤p) (β : ℝ) :
    (∫ J : Disorder N p,SphereRotationGeometry.fisherInformation β J (fun _ => 1)/(N : ℝ) ∂disorderLaw N p)=
      β^2*(p : ℝ)*((N : ℝ)-1)/(N : ℝ) := by
  have hi := projected_gradient_joint_square_integrable hN (by omega : 0<p)
  simp_rw [fisherInformation_uniform_eq]
  rw [integral_div,integral_const_mul]
  have hs : (∫ J : Disorder N p,∫ x : State N,‖projection x (gradient (Hamiltonian N p J) x)‖^2
      ∂sphereLaw N ∂disorderLaw N p)=(p : ℝ)*((N : ℝ)-1) := by
    rw [integral_integral_swap hi]
    calc
      _ = ∫ _x : State N,(p : ℝ)*((N : ℝ)-1) ∂sphereLaw N := by
        apply integral_congr_ae
        filter_upwards [sphereLaw_support hN] with x hx
        exact projected_gradient_square_expectation hN hp x ((onSphere_iff_norm_sq _).mpr hx)
      _ = _ := by simp
  rw [hs]
  ring

end SphericalAging.SphereInitialFisherCovariance
