module

public import SphericalAging.ForkEnergyComparison
public import SphericalAging.SphereTensorObservable
public import SphericalAging.PhysicalVariationalBounds

public section

/-! Dimension-independent entire-vector bounds for the true hard drift
on the ball of radius 2 sqrt N. These supply state-clipped additive-noise
approximations; no Lipschitz or approximation conclusion is assumed. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ClippedHamiltonianDriftBounds
open Set FiniteModel GaussianLandscape LandscapeDerivatives HardSphereDynamics
open PhysicalVariationalBounds AdaptiveGradientDisclosure SphereTensorObservable
open scoped InnerProductSpace BigOperators NNReal

 theorem hessian_ball_bound {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    {C : ℝ} (hC : 0≤C) (J : Disorder N p) {x : Vector N}
    (hx : ‖x‖≤C*Real.sqrt N) :
    ‖fderiv ℝ (hamiltonianGradient J) x‖≤
      (p:ℝ)*((p:ℝ)-1)*C^(p-2)*landscapeNorm N p J := by
  have hn : 0≤normalization N p := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hp1 : (1:ℝ)≤p := by exact_mod_cast (show 1≤p by omega)
  have hr := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hs : normalization N p*Real.sqrt (N:ℝ)^(p-2)=(Real.sqrt (N:ℝ))⁻¹ := by
    rw [←one_div]
    apply (eq_div_iff hr.ne').mpr
    have hpow : p-1=(p-2)+1 := by omega
    have hh := normalization_sqrt_power (p:=p) hN
    rw [hpow,pow_succ] at hh
    simpa only [mul_assoc] using hh
  change ‖fderiv ℝ (gradient (Hamiltonian N p J)) x‖≤_
  rw [gradient_derivative_norm]
  have hh := Hamiltonian_iteratedFDeriv_norm_le J x 2
  rw [Nat.cast_descFactorial_two] at hh
  calc
    _ ≤ normalization N p*((p:ℝ)*((p:ℝ)-1))*‖tensorForm N p J‖*‖x‖^(p-2) := hh
    _ ≤ normalization N p*((p:ℝ)*((p:ℝ)-1))*‖tensorForm N p J‖*(C*Real.sqrt N)^(p-2) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _) (by positivity)
    _ = (p:ℝ)*((p:ℝ)-1)*C^(p-2)*‖tensorForm N p J‖*
        (normalization N p*Real.sqrt N^(p-2)) := by rw [mul_pow];ring
    _ = _ := by rw [hs];unfold landscapeNorm;ring

 theorem projection_norm_le_three {N : ℕ} (hN : 0<N) (x v : State N)
    (hx : ‖x‖≤2*Real.sqrt N) : ‖projection x v‖≤3*‖v‖ := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hx2 : ‖x‖^2≤4*(N:ℝ) := by
    have hh := pow_le_pow_left₀ (norm_nonneg x) hx 2
    simpa only [mul_pow,Real.sq_sqrt hn.le,show (2:ℝ)^2=4 by norm_num] using hh
  have hc : (⟪x,v⟫_ℝ)^2≤4*(N:ℝ)*‖v‖^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg x) (norm_nonneg v))).mpr
      (abs_real_inner_le_norm x v)
    rw [sq_abs,mul_pow] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hx2 (sq_nonneg _))
  have he : ‖projection x v‖^2=‖v‖^2+
      (‖x‖^2/(N:ℝ)^2-2/(N:ℝ))*(⟪x,v⟫_ℝ)^2 := by
    rw [projection,norm_sub_sq_real,real_inner_smul_right,norm_smul,
      mul_pow,Real.norm_eq_abs,sq_abs,real_inner_comm v x]
    field_simp
    ring
  have hcoef : ‖x‖^2/(N:ℝ)^2-2/(N:ℝ)≤2/(N:ℝ) := by
    apply (le_div_iff₀ hn).mpr
    field_simp
    nlinarith
  have hsq : ‖projection x v‖^2≤9*‖v‖^2 := by
    rw [he]
    calc
      _ ≤ ‖v‖^2+(2/(N:ℝ))*(⟪x,v⟫_ℝ)^2 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
      _ ≤ ‖v‖^2+(2/(N:ℝ))*(4*(N:ℝ)*‖v‖^2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (div_nonneg (show (0:ℝ)≤2 by norm_num) hn.le))
      _ = _ := by field_simp;ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤3*‖v‖)).mp (by nlinarith [hsq])

 theorem gradient_euclidean_bound {N p : ℕ} (hN : 0<N)
    {C : ℝ} (hC : 0≤C) (J : Disorder N p) {x : Vector N}
    (hx : ‖x‖≤C*Real.sqrt N) :
    ‖hamiltonianGradient J x‖≤(p:ℝ)*C^(p-1)*‖WithLp.toLp 2 J‖ := by
  have hn : 0≤normalization N p := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hb : ‖fderiv ℝ (Hamiltonian N p J) x‖≤
      normalization N p*‖WithLp.toLp 2 J‖*(p:ℝ)*‖x‖^(p-1) := by
    apply (fderiv ℝ (Hamiltonian N p J) x).opNorm_le_bound (by positivity)
    intro y
    rw [Hamiltonian_fderiv_eq_tensor_inner,Real.norm_eq_abs,abs_mul,abs_of_nonneg hn]
    calc
      _ ≤ normalization N p*(‖WithLp.toLp 2 J‖*‖gradientTensor x y‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) hn
      _ ≤ normalization N p*(‖WithLp.toLp 2 J‖*((p:ℝ)*‖x‖^(p-1)*‖y‖)) := by
        apply mul_le_mul_of_nonneg_left _ hn
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [←derivativeTensor_apply]
        exact derivativeTensor_apply_norm_le x y
      _ = _ := by ring
  rw [hamiltonianGradient,gradient,LinearIsometryEquiv.norm_map]
  calc
    _ ≤ normalization N p*‖WithLp.toLp 2 J‖*(p:ℝ)*‖x‖^(p-1) := hb
    _ ≤ normalization N p*‖WithLp.toLp 2 J‖*(p:ℝ)*(C*Real.sqrt N)^(p-1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _) (by positivity)
    _ = (p:ℝ)*C^(p-1)*‖WithLp.toLp 2 J‖*(normalization N p*Real.sqrt N^(p-1)) := by
      rw [mul_pow];ring
    _ = _ := by rw [normalization_sqrt_power hN];ring

 theorem drift_disorder_ball_bound {N p : ℕ} (hN : 0<N)
    {β : ℝ} (hβ : 0≤β) (J K : Disorder N p) (x : State N)
    (hx : ‖x‖≤2*Real.sqrt N) :
    ‖hamiltonianDrift β J x-hamiltonianDrift β K x‖≤
      3*β*(p:ℝ)*2^(p-1)*‖WithLp.toLp 2 (J-K)‖ := by
  have hg : hamiltonianGradient (J-K) x=hamiltonianGradient J x-hamiltonianGradient K x := by
    have hh := HamiltonianParameter.gradient_add J (-K)
    rw [show J+(-K)=J-K by rfl,show -K=(-1:ℝ) • K by simp,
      HamiltonianParameter.gradient_smul (-1) K] at hh
    simpa only [neg_one_smul,Pi.add_apply,Pi.neg_apply,sub_eq_add_neg] using congrFun hh x
  have he : hamiltonianDrift β J x-hamiltonianDrift β K x=
      β • projection x (hamiltonianGradient (J-K) x) := by
    unfold hamiltonianDrift drift
    rw [hg]
    rw [show projection x (hamiltonianGradient J x-hamiltonianGradient K x)=
      projection x (hamiltonianGradient J x)-projection x (hamiltonianGradient K x) by
        simp only [projection,inner_sub_right,sub_div,sub_smul];module]
    module
  rw [he,norm_smul,Real.norm_of_nonneg hβ]
  exact (mul_le_mul_of_nonneg_left ((projection_norm_le_three hN x _ hx).trans
    (mul_le_mul_of_nonneg_left (gradient_euclidean_bound hN (by norm_num : (0:ℝ)≤2) (J-K) hx)
      (by norm_num))) hβ).trans_eq (by ring)

 theorem projectionDerivative_ball_bound {N : ℕ} (hN : 0<N) (x v g : State N)
    (hx : ‖x‖≤2*Real.sqrt N) :
    ‖projectionDerivative x v g‖≤4*‖g‖/Real.sqrt N*‖v‖ := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hr := Real.sqrt_pos.mpr hn
  calc
    _ ≤ ‖(inner ℝ v g/(N:ℝ)) • x‖+‖(inner ℝ x g/(N:ℝ)) • v‖ := by
      simpa only [projectionDerivative,neg_smul,norm_neg] using
        norm_sub_le (-((inner ℝ v g/(N:ℝ)) • x)) ((inner ℝ x g/(N:ℝ)) • v)
    _ = ‖inner ℝ v g‖/(N:ℝ)*‖x‖+‖inner ℝ x g‖/(N:ℝ)*‖v‖ := by
      simp only [norm_smul,norm_div,Real.norm_of_nonneg hn.le]
    _ ≤ (‖v‖*‖g‖)/(N:ℝ)*‖x‖+(‖x‖*‖g‖)/(N:ℝ)*‖v‖ := by
      exact add_le_add (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (norm_inner_le_norm v g) hn.le) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (norm_inner_le_norm x g) hn.le) (norm_nonneg _))
    _ ≤ (‖v‖*‖g‖)/(N:ℝ)*(2*Real.sqrt N)+
        ((2*Real.sqrt N)*‖g‖)/(N:ℝ)*‖v‖ := by gcongr
    _ = _ := by field_simp;rw [Real.sq_sqrt hn.le];ring

 theorem drift_derivative_ball_bound {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p) (x v : State N)
    (hx : ‖x‖≤2*Real.sqrt N) :
    ‖fderiv ℝ (hamiltonianDrift β J) x v‖≤
      (1+β*(p:ℝ)*landscapeNorm N p J*2^(p-2)*(3*(p:ℝ)+5))*‖v‖ := by
  have hr := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hp1 : (1:ℝ)≤p := by exact_mod_cast (show 1≤p by omega)
  have hH := hessian_ball_bound hN hp (by norm_num : (0:ℝ)≤2) J hx
  have hg := ForkEnergyComparison.gradient_ball_bound hN (by norm_num : (0:ℝ)≤2) J hx
  have hP : ‖projection x (fderiv ℝ (hamiltonianGradient J) x v)‖≤
      3*((p:ℝ)*((p:ℝ)-1)*2^(p-2)*landscapeNorm N p J)*‖v‖ := by
    exact (projection_norm_le_three hN x _ hx).trans
      ((mul_le_mul_of_nonneg_left (((fderiv ℝ (hamiltonianGradient J) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hH (norm_nonneg _))) (by norm_num)).trans_eq (by ring))
  have hd : ‖projectionDerivative x v (hamiltonianGradient J x)‖≤
      4*((p:ℝ)*2^(p-1)*landscapeNorm N p J)*‖v‖ := by
    refine (projectionDerivative_ball_bound hN x v _ hx).trans ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
    apply (div_le_iff₀ hr).mpr
    exact (mul_le_mul_of_nonneg_left hg (by norm_num)).trans_eq (by ring)
  rw [fderiv_hamiltonianDrift_apply]
  calc
    _ ≤ ‖β • (projection x (fderiv ℝ (hamiltonianGradient J) x v)+
        projectionDerivative x v (hamiltonianGradient J x))‖+‖kappa N • v‖ := norm_sub_le _ _
    _ ≤ β*(‖projection x (fderiv ℝ (hamiltonianGradient J) x v)‖+
        ‖projectionDerivative x v (hamiltonianGradient J x)‖)+‖v‖ := by
      rw [norm_smul,norm_smul,Real.norm_of_nonneg hβ]
      exact add_le_add (mul_le_mul_of_nonneg_left (norm_add_le _ _) hβ)
        ((mul_le_mul_of_nonneg_right (kappa_norm_le_one hN) (norm_nonneg v)).trans_eq (one_mul _))
    _ ≤ β*(3*((p:ℝ)*((p:ℝ)-1)*2^(p-2)*landscapeNorm N p J)*‖v‖+
        4*((p:ℝ)*2^(p-1)*landscapeNorm N p J)*‖v‖)+‖v‖ := by gcongr
    _ = _ := by
      have he : p-1=(p-2)+1 := by omega
      rw [he,pow_succ]
      ring

 theorem drift_ball_lipschitz {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p) {x y : State N}
    (hx : ‖x‖≤2*Real.sqrt N) (hy : ‖y‖≤2*Real.sqrt N) :
    ‖hamiltonianDrift β J x-hamiltonianDrift β J y‖≤
      (1+β*(p:ℝ)*landscapeNorm N p J*2^(p-2)*(3*(p:ℝ)+5))*‖x-y‖ := by
  apply (convex_closedBall (0:State N) (2*Real.sqrt N)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (contDiff_hamiltonianDrift β J).differentiable (by simp) z) ?_
    (show y∈Metric.closedBall (0:State N) (2*Real.sqrt N) by simpa using hy)
    (show x∈Metric.closedBall (0:State N) (2*Real.sqrt N) by simpa using hx)
  intro z hz
  apply (fderiv ℝ (hamiltonianDrift β J) z).opNorm_le_bound
    (by have := landscapeNorm_nonnegative N p J;positivity)
  intro v
  exact drift_derivative_ball_bound hN hp hβ J z v (by simpa using hz)

 theorem drift_ball_norm_bound {N p : ℕ} (hN : 0<N)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p) {x : State N}
    (hx : ‖x‖≤2*Real.sqrt N) :
    ‖hamiltonianDrift β J x‖≤
      (2+3*β*(p:ℝ)*2^(p-1)*landscapeNorm N p J)*Real.sqrt N := by
  have hg := ForkEnergyComparison.gradient_ball_bound hN (by norm_num : (0:ℝ)≤2) J hx
  unfold hamiltonianDrift drift
  calc
    _ ≤ ‖β • projection x (hamiltonianGradient J x)‖+‖kappa N • x‖ := norm_sub_le _ _
    _ ≤ β*(3*‖hamiltonianGradient J x‖)+‖x‖ := by
      rw [norm_smul,norm_smul,Real.norm_of_nonneg hβ]
      exact add_le_add (mul_le_mul_of_nonneg_left (projection_norm_le_three hN x _ hx) hβ)
        ((mul_le_mul_of_nonneg_right (kappa_norm_le_one hN) (norm_nonneg x)).trans_eq (one_mul _))
    _ ≤ β*(3*((p:ℝ)*2^(p-1)*landscapeNorm N p J*Real.sqrt N))+2*Real.sqrt N := by
      apply add_le_add _ hx
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg (by norm_num)) hβ
    _ = _ := by ring

 theorem drift_state_clipped_bound {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p) (Ψ : State N→State N)
    (hΨ : LipschitzWith 1 Ψ) (hball : ∀x,‖Ψ x‖≤2*Real.sqrt N) (x y : State N) :
    ‖hamiltonianDrift β J (Ψ x)-hamiltonianDrift β J (Ψ y)‖≤
      (1+β*(p:ℝ)*landscapeNorm N p J*2^(p-2)*(3*(p:ℝ)+5))*‖x-y‖ := by
  have hK : 0≤1+β*(p:ℝ)*landscapeNorm N p J*2^(p-2)*(3*(p:ℝ)+5) := by
    have := landscapeNorm_nonnegative N p J
    positivity
  exact (drift_ball_lipschitz hN hp hβ J (hball x) (hball y)).trans
    (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using hΨ.dist_le_mul x y) hK)

end SphericalAging.ClippedHamiltonianDriftBounds
