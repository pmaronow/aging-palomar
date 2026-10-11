module

public import SphericalAging.CloseOrthogonalTransport
public import SphericalAging.GaussianOrthogonalForkCovariance
public import SphericalAging.ForkEnergyComparison

public section

/-! Actual basepoint transport for the orthogonal fork domains and their
Hamiltonian increments. The transport is explicitly constructed from two
reflections, and its displacement bound uses the same original disorder. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.OrthogonalForkBasepointTransport
open Set MeasureTheory FiniteModel GaussianLandscape ForkEnergyComparison
  GaussianOrthogonalForkCovariance CloseOrthogonalTransport
open scoped InnerProductSpace BigOperators
variable {N p K : ℕ}

theorem fork_map (O : Vector N≃ₗᵢ[ℝ]Vector N) {x : Vector N} {y : Fin K→Vector N}
    {r q : ℝ} (hf : OrthogonalFork x y r q) :
    OrthogonalFork (O x) (fun i => O (y i)) r q := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [O.norm_map] using hf.base_norm
  · intro i;simpa only [O.norm_map] using hf.leaf_norm i
  · intro i
    rw [←map_sub,O.inner_map_map]
    exact hf.increment_base i
  · intro i j hij
    rw [←map_sub,←map_sub,O.inner_map_map]
    exact hf.increment_orthogonal i j hij

theorem fork_transport {x x' : Vector N} (hxx' : ‖x‖=‖x'‖)
    {y : Fin K→Vector N} {r q : ℝ} (hf : OrthogonalFork x y r q) :
    OrthogonalFork x' (fun i => transport x x' (y i)) r q := by
  have hh := fork_map (transport x x') hf
  rwa [transport_base hxx'] at hh

@[expose] def forkEquiv (x x' : Vector N) (hxx' : ‖x‖=‖x'‖) (r q : ℝ) :
    {y : Fin K→Vector N // OrthogonalFork x y r q}≃
      {y : Fin K→Vector N // OrthogonalFork x' y r q} where
  toFun y := ⟨fun i => transport x x' (y.val i),fork_transport hxx' y.property⟩
  invFun y := ⟨fun i => (transport x x').symm (y.val i),by
    have hh := fork_map (transport x x').symm y.property
    have he : (transport x x').symm x'=x := by
      calc
        _=(transport x x').symm (transport x x' x) :=
          congrArg (transport x x').symm (transport_base hxx').symm
        _=x := (transport x x').symm_apply_apply x
    rwa [he] at hh⟩
  left_inv y := by apply Subtype.ext;funext i;exact (transport x x').symm_apply_apply _
  right_inv y := by apply Subtype.ext;funext i;exact (transport x x').apply_symm_apply _

theorem Hamiltonian_transport_difference (hN : 0<N) (J : Disorder N p)
    (x x' z : Vector N) (hx : x≠0) (hz : ‖z‖≤Real.sqrt N) :
    |Hamiltonian N p J z-Hamiltonian N p J (transport x x' z)|≤
      4*(p:ℝ)*landscapeNorm N p J*(N:ℝ)*‖x-x'‖/‖x‖ := by
  have hL := Hamiltonian_ball_lipschitz hN (C:=1) (x:=z) (y:=transport x x' z)
    (by norm_num : (0:ℝ)≤1) J
    (by simpa using hz) (by simpa only [one_mul,(transport x x').norm_map] using hz)
  simp only [one_pow,mul_one] at hL
  have hD := transport_displacement_le x x' z hx
  rw [norm_sub_rev] at hD
  have hn : 0≤4*‖x-x'‖/‖x‖ := by positivity
  calc
    _≤(p:ℝ)*landscapeNorm N p J*Real.sqrt N*‖z-transport x x' z‖ := hL
    _≤(p:ℝ)*landscapeNorm N p J*Real.sqrt N*(4*‖x-x'‖/‖x‖*‖z‖) := by
      apply mul_le_mul_of_nonneg_left hD
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (landscapeNorm_nonnegative _ _ _))
        (Real.sqrt_nonneg _)
    _≤(p:ℝ)*landscapeNorm N p J*Real.sqrt N*(4*‖x-x'‖/‖x‖*Real.sqrt N) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz hn)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (landscapeNorm_nonnegative _ _ _))
          (Real.sqrt_nonneg _))
    _=(4*(p:ℝ)*landscapeNorm N p J*‖x-x'‖/‖x‖)*(Real.sqrt N*Real.sqrt N) := by ring
    _=_ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg N)];ring

end SphericalAging.OrthogonalForkBasepointTransport
