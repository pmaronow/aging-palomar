module

public import SphericalAging.SphereInitialFisherCovariance
public import SphericalAging.GaussianOrthogonalForkCovariance
public import SphericalAging.ResponseMatrixEnergyContraction

public section

/-! The genuine shared Gaussian linear term in a pure-p orthogonal fork.
The projection is onto the orthogonal complement of the actual base vector,
so no assumption that the base lies on the physical unit sphere is needed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace
namespace SphericalAging.PurePSharedLinearMoment
open FiniteModel HardSphereDynamics HamiltonianDerivativeCovariance
open SphereInitialFisherCovariance GaussianOrthogonalForkCovariance
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

@[expose] def tangentSpace {N : ℕ} (x : Vector N) : Submodule ℝ (Vector N) := (ℝ ∙ x)ᗮ
@[expose] def tangentGradient {N p : ℕ} (x : Vector N) (J : Disorder N p) : Vector N :=
  (tangentSpace x).starProjection (gradient (Hamiltonian N p J) x)

theorem tangent_inner {N : ℕ} (x v : Vector N) :
    inner ℝ x ((tangentSpace x).starProjection v)=0 := by
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right).mp
    (Submodule.starProjection_apply_mem (tangentSpace x) v)

theorem tangentGradient_norm_sq {N p : ℕ} (x : Vector N) (J : Disorder N p) :
    ‖tangentGradient x J‖^2=
      ∑i : Fin N,(inner ℝ (gradient (Hamiltonian N p J) x)
        ((tangentSpace x).starProjection (basisVector i)))^2 := by
  rw [←real_inner_self_eq_norm_sq,←coordinate_square_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [←basis_inner]
  exact congrArg (fun z : ℝ => z^2)
    ((tangentSpace x).inner_starProjection_left_eq_right _ _)

theorem tangentGradient_sq_integrable {N p : ℕ} (x : Vector N) :
    Integrable (fun J : Disorder N p => ‖tangentGradient x J‖^2) (disorderLaw N p) := by
  simpa only [tangentGradient_norm_sq] using integrable_finsetSum Finset.univ
    (fun i _ => (directional_gradient_memLp (p:=p) x
      ((tangentSpace x).starProjection (basisVector i))).integrable_sq)

theorem tangentGradient_continuous {N p : ℕ} (x : Vector N) :
    Continuous (tangentGradient (p:=p) x) :=
  (tangentSpace x).starProjection.continuous.comp
    ((Hamiltonian_gradient_joint_continuous N p).comp (continuous_id.prodMk continuous_const))

theorem tangentGradient_memLp {N p : ℕ} (x : Vector N) :
    MemLp (tangentGradient (p:=p) x) 2 (disorderLaw N p) :=
  (memLp_two_iff_integrable_sq_norm (tangentGradient_continuous x).aestronglyMeasurable).mpr
    (tangentGradient_sq_integrable x)

/-- Actual iid tensor covariance and the true tangent projection eliminate
the radial covariance, leaving at most N tangent coordinates. -/
theorem tangentGradient_secondMoment_le {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    {r : ℝ} (hr : 0≤r) (x : Vector N) (hx : ‖x‖^2=(N:ℝ)*r) :
    (∫J : Disorder N p,‖tangentGradient x J‖^2 ∂disorderLaw N p)≤
      (N:ℝ)*(p:ℝ)*r^(p-1) := by
  have hn : (N:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hN)
  have hxx : inner ℝ x x/(N:ℝ)=r := by
    rw [real_inner_self_eq_norm_sq,hx,mul_div_cancel_left₀ _ hn]
  have hc (i : Fin N) : (∫J : Disorder N p,
      (inner ℝ (gradient (Hamiltonian N p J) x)
        ((tangentSpace x).starProjection (basisVector i)))^2 ∂disorderLaw N p)=
      (p:ℝ)*r^(p-1)*‖(tangentSpace x).starProjection (basisVector i)‖^2 := by
    have hh := Hamiltonian_gradient_covariance_overlap hN hp x x
      ((tangentSpace x).starProjection (basisVector i))
      ((tangentSpace x).starProjection (basisVector i))
    have ht : inner ℝ ((tangentSpace x).starProjection (basisVector i)) x=0 := by
      rw [real_inner_comm];exact tangent_inner x _
    rw [hxx,ht,mul_zero,zero_mul,add_zero,real_inner_self_eq_norm_sq] at hh
    simpa only [←sq] using hh
  simp_rw [tangentGradient_norm_sq]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    (directional_gradient_memLp (p:=p) x ((tangentSpace x).starProjection (basisVector i))).integrable_sq)]
  simp only [hc]
  calc
    _≤∑i : Fin N,(p:ℝ)*r^(p-1) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := (tangentSpace x).norm_starProjection_apply_le (basisVector i)
      have hb : ‖basisVector (N:=N) i‖=1 := by simp [basisVector,EuclideanSpace.norm_single]
      rw [hb] at hi
      exact mul_le_of_le_one_right (mul_nonneg (Nat.cast_nonneg p) (pow_nonneg hr _))
        (by nlinarith [norm_nonneg ((tangentSpace x).starProjection (basisVector i))])
    _=_ := by simp [mul_comm,mul_left_comm,mul_assoc]

/-- A genuine orthogonal sum has its exact squared length, with no loss in K. -/
theorem orthogonal_sum_norm_sq {N K : ℕ} {d : ℝ} (u : Fin K→Vector N)
    (hu : ∀i,‖u i‖^2=(N:ℝ)*d)
    (ho : ∀i j,i≠j→inner ℝ (u i) (u j)=0) :
    ‖∑i,u i‖^2=(K:ℝ)*(N:ℝ)*d := by
  classical
  rw [←real_inner_self_eq_norm_sq,sum_inner]
  have hh (i : Fin K) : inner ℝ (u i) (∑j,u j)=(N:ℝ)*d := by
    rw [inner_sum,Finset.sum_eq_single i]
    · rw [real_inner_self_eq_norm_sq,hu]
    · intro j _ hji
      exact ho i j hji.symm
    · simp
  simp only [hh,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

@[expose] def linearAverage {N p K : ℕ} (x : Vector N) (u : Fin K→Vector N)
    (J : Disorder N p) : ℝ :=
  (∑i,inner ℝ (gradient (Hamiltonian N p J) x) (u i))/((K:ℝ)*N)

/-- The same envelope bounds every orthogonal fork, including a fork chosen
after observing the disorder. -/
@[expose] def linearEnvelope {N p : ℕ} (K : ℕ) (x : Vector N) (d : ℝ)
    (J : Disorder N p) : ℝ :=
  Real.sqrt (d/((K:ℝ)*N))*‖tangentGradient x J‖

theorem linearAverage_abs_le_envelope {N p K : ℕ} (hN : 0<N) (hK : 0<K)
    {d : ℝ} (hd : 0≤d) (x : Vector N) (u : Fin K→Vector N)
    (hu : ∀i,‖u i‖^2=(N:ℝ)*d) (ht : ∀i,inner ℝ (u i) x=0)
    (ho : ∀i j,i≠j→inner ℝ (u i) (u j)=0) (J : Disorder N p) :
    |linearAverage x u J|≤linearEnvelope K x d J := by
  have hn : (0:ℝ)<(K:ℝ)*N := mul_pos (Nat.cast_pos.mpr hK) (Nat.cast_pos.mpr hN)
  have ht' (i : Fin K) : (tangentSpace x).starProjection (u i)=u i :=
    Submodule.starProjection_eq_self_iff.mpr
      (Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (ht i))
  have he : (∑i,inner ℝ (gradient (Hamiltonian N p J) x) (u i))=
      inner ℝ (tangentGradient x J) (∑i,u i) := by
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [tangentGradient,(tangentSpace x).inner_starProjection_left_eq_right,ht']
  have hh := abs_real_inner_le_norm (tangentGradient x J) (∑i,u i)
  have hs := orthogonal_sum_norm_sq u hu ho
  have hc : 0≤d/((K:ℝ)*N) := div_nonneg hd hn.le
  have hsqrt := Real.sq_sqrt hc
  have hbound : |linearAverage x u J|≤
      ‖tangentGradient x J‖*‖∑i,u i‖/((K:ℝ)*N) := by
    rw [linearAverage,he,abs_div,abs_of_pos hn]
    exact div_le_div_of_nonneg_right hh hn.le
  have hsq : (‖tangentGradient x J‖*‖∑i,u i‖/((K:ℝ)*N))^2=
      (linearEnvelope K x d J)^2 := by
    rw [linearEnvelope,mul_pow,div_pow,mul_pow,hs,hsqrt]
    field_simp [hn.ne']
  have ha : 0≤‖tangentGradient x J‖*‖∑i,u i‖/((K:ℝ)*N) := by positivity
  have hb : 0≤linearEnvelope K x d J := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith

theorem linearEnvelope_integrable {N p : ℕ} (K : ℕ) (x : Vector N) (d : ℝ) :
    Integrable (linearEnvelope (p:=p) K x d) (disorderLaw N p) :=
  ((tangentGradient_memLp (p:=p) x).integrable (by norm_num)).norm.const_mul _

/-- The discarded shared linear term is exactly of order sqrt(d/K),
proved from the actual product Gaussian covariance. -/
theorem linearEnvelope_expectation_le {N p K : ℕ} (hN : 0<N) (hp : 2≤p) (hK : 0<K)
    {r d : ℝ} (hr : 0≤r) (hd : 0≤d) (x : Vector N) (hx : ‖x‖^2=(N:ℝ)*r) :
    (∫J : Disorder N p,linearEnvelope K x d J ∂disorderLaw N p)≤
      Real.sqrt ((p:ℝ)*r^(p-1)*d/K) := by
  have hn : (N:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hN)
  have hk : (K:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hK)
  have hc : 0≤d/((K:ℝ)*N) := div_nonneg hd (by positivity)
  have hnorm := ResponseMatrixEnergyContraction.integral_abs_le_sqrt_secondMoment
    (tangentGradient_memLp (p:=p) x).norm
  simp only [abs_of_nonneg (norm_nonneg _)] at hnorm
  have hm := tangentGradient_secondMoment_le hN hp hr x hx
  unfold linearEnvelope
  rw [integral_const_mul]
  calc
    _≤Real.sqrt (d/((K:ℝ)*N))*Real.sqrt (∫J : Disorder N p,‖tangentGradient x J‖^2 ∂disorderLaw N p) :=
      mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)
    _≤Real.sqrt (d/((K:ℝ)*N))*Real.sqrt ((N:ℝ)*(p:ℝ)*r^(p-1)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hm) (Real.sqrt_nonneg _)
    _=_ := by
      rw [←Real.sqrt_mul hc]
      congr 1
      field_simp [hn,hk]

theorem orthogonalFork_increment_norm {N K : ℕ} {x : Vector N} {y : Fin K→Vector N}
    {r q : ℝ} (hf : GaussianOrthogonalForkCovariance.OrthogonalFork x y r q) (i : Fin K) :
    ‖y i-x‖^2=(N:ℝ)*(q-r) := by
  rw [norm_sub_sq_real,hf.leaf_norm,hf.leaf_base,hf.base_norm]
  ring

theorem fork_linearAverage_abs_le {N p K : ℕ} (hN : 0<N) (hK : 0<K)
    {r q : ℝ} (hrq : r≤q) (x : Vector N) (y : Fin K→Vector N)
    (hf : GaussianOrthogonalForkCovariance.OrthogonalFork x y r q)
    (J : ForkDisorder N p K) :
    |linearAverage x (fun i => y i-x) (J none)|≤linearEnvelope K x (q-r) (J none) :=
  linearAverage_abs_le_envelope hN hK (sub_nonneg.mpr hrq) x (fun i => y i-x)
    (fun i => orthogonalFork_increment_norm hf i) hf.increment_base hf.increment_orthogonal (J none)

@[expose] def forkLinearEnvelope {N p K : ℕ} (x : Vector N) (d : ℝ)
    (J : ForkDisorder N p K) : ℝ := linearEnvelope K x d (J none)

theorem forkLinearEnvelope_integrable {N p K : ℕ} (x : Vector N) (d : ℝ) :
    Integrable (forkLinearEnvelope (p:=p) (K:=K) x d) (forkLaw N p K) :=
  (measurePreserving_eval (fun _ : Option (Fin K) => disorderLaw N p) none).integrable_comp_of_integrable
    (linearEnvelope_integrable (p:=p) K x d)

theorem forkLinearEnvelope_expectation_le {N p K : ℕ} (hN : 0<N) (hp : 2≤p) (hK : 0<K)
    {r d : ℝ} (hr : 0≤r) (hd : 0≤d) (x : Vector N) (hx : ‖x‖^2=(N:ℝ)*r) :
    (∫J : ForkDisorder N p K,forkLinearEnvelope x d J ∂forkLaw N p K)≤
      Real.sqrt ((p:ℝ)*r^(p-1)*d/K) := by
  have he := (measurePreserving_eval (fun _ : Option (Fin K) => disorderLaw N p) none).hasLaw.integral_comp
    (linearEnvelope_integrable (p:=p) K x d).aestronglyMeasurable
  exact (le_of_eq he).trans (linearEnvelope_expectation_le hN hp hK hr hd x hx)

/-- Any measurable discarded linear term dominated by the actual uniform
envelope is genuinely integrable and has the same sharp expectation bound. -/
theorem dominated_fork_linear_expectation {N p K : ℕ} (hN : 0<N) (hp : 2≤p) (hK : 0<K)
    {r d : ℝ} (hr : 0≤r) (hd : 0≤d) (x : Vector N) (hx : ‖x‖^2=(N:ℝ)*r)
    (Z : ForkDisorder N p K→ℝ) (hZ : AEStronglyMeasurable Z (forkLaw N p K))
    (hbound : ∀ᵐJ∂forkLaw N p K,|Z J|≤forkLinearEnvelope x d J) :
    Integrable Z (forkLaw N p K) ∧
      (∫J : ForkDisorder N p K,|Z J| ∂forkLaw N p K)≤Real.sqrt ((p:ℝ)*r^(p-1)*d/K) := by
  have hi : Integrable Z (forkLaw N p K) := (forkLinearEnvelope_integrable x d).mono' hZ
    (by simpa only [Real.norm_eq_abs] using hbound)
  exact ⟨hi,(integral_mono_ae hi.abs (forkLinearEnvelope_integrable x d) hbound).trans
    (forkLinearEnvelope_expectation_le hN hp hK hr hd x hx)⟩

end SphericalAging.PurePSharedLinearMoment
