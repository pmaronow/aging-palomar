module

public import SphericalAging.HamiltonianTangentJetIncrement

public section

/-! Direct comparison coefficients for a genuine finite orthogonal-fork edge.
Only the shared first variation is removed; the full remaining polynomial
covariance is retained, with actual weights zero ≤ a ≤ b. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.HamiltonianOneReplicaEdgeCoefficients
open Set FiniteModel GaussianIntegrationByParts HamiltonianDerivativeCovariance
open HamiltonianTangentJetCovariance HamiltonianTangentJetIncrement
open scoped BigOperators InnerProductSpace
variable {N p : ℕ}

 theorem power_secant_upper {q z : ℝ} (hq : 0≤q) (hz : |z|≤q) (p : ℕ) :
    q^p-z^p≤(p:ℝ)*q^(p-1)*(q-z) := by
  have hzq : z≤q := (le_abs_self z).trans hz
  have hh := abs_pow_sub_pow_le (a:=q) (b:=z) (n:=p)
  rw [abs_of_nonneg hq,max_eq_left hz,abs_of_nonneg (sub_nonneg.mpr hzq)] at hh
  exact (le_abs_self _).trans (hh.trans_eq (by ring))

 theorem coefficient_gram_overlap (hN : 0<N) (hp : 1≤p) (y z : Vector N) :
    (∑I : TensorIndex N p,hamiltonianCoefficient I y*hamiltonianCoefficient I z)=
      (N:ℝ)*(inner ℝ y z/(N:ℝ))^p := by
  rw [coefficient_gram,normalization_sq N p hN,dimension_covariance_scale N p hN hp]

 theorem coefficient_full_difference (hN : 0<N) (hp : 1≤p) (y z : Vector N)
    {q : ℝ} (hy : ‖y‖^2=(N:ℝ)*q) (hz : ‖z‖^2=(N:ℝ)*q) :
    (∑I : TensorIndex N p,(hamiltonianCoefficient I y-hamiltonianCoefficient I z)^2)=
      2*(N:ℝ)*(q^p-(inner ℝ y z/(N:ℝ))^p) := by
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [square_difference_sum,coefficient_gram_overlap hN hp y y,
    coefficient_gram_overlap hN hp z z,coefficient_gram_overlap hN hp y z,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,hy,hz,mul_div_cancel_left₀ q hn]
  ring

 theorem coefficient_gradient_full (hN : 0<N) (x y u : Vector N) {r : ℝ}
    (hxy : inner ℝ x y/(N:ℝ)=r) :
    (∑I : TensorIndex N p,firstCoeff I x u*hamiltonianCoefficient I y)=
      (p:ℝ)*r^(p-1)*inner ℝ u y := by
  simp only [firstCoeff]
  rw [coefficient_gradient_gram_left]
  calc
    _ = (p:ℝ)*(normalization N p^2*(inner ℝ x y)^(p-1))*inner ℝ u y := by ring
    _ = _ := by rw [normalization_first_power hN,hxy]

 theorem coefficient_gradient_difference (hN : 0<N) (x u v : Vector N) {r : ℝ}
    (hxu : inner ℝ x (x+u)/(N:ℝ)=r) (hxv : inner ℝ x (x+v)/(N:ℝ)=r) :
    (∑I : TensorIndex N p,(hamiltonianCoefficient I (x+u)-hamiltonianCoefficient I (x+v))*firstCoeff I x (u-v))=
      (p:ℝ)*r^(p-1)*‖u-v‖^2 := by
  have he : (∑I : TensorIndex N p,(hamiltonianCoefficient I (x+u)-hamiltonianCoefficient I (x+v))*firstCoeff I x (u-v))=
      (∑I : TensorIndex N p,firstCoeff I x (u-v)*hamiltonianCoefficient I (x+u))-
      ∑I : TensorIndex N p,firstCoeff I x (u-v)*hamiltonianCoefficient I (x+v) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro I _
    ring
  rw [he,coefficient_gradient_full hN x (x+u) (u-v) hxu,
    coefficient_gradient_full hN x (x+v) (u-v) hxv,←mul_sub,←inner_sub_right]
  simp only [add_sub_add_left_eq_sub,real_inner_self_eq_norm_sq]

@[expose]  def remainderCoeff (a b : ℝ) (x u : Vector N) : (TensorIndex N p⊕TensorIndex N p)→ℝ
  | Sum.inl I => Real.sqrt a*(hamiltonianCoefficient I (x+u)-hamiltonianCoefficient I x-firstCoeff I x u)
  | Sum.inr I => Real.sqrt (b-a)*hamiltonianCoefficient I (x+u)

@[expose]  def edgeRate (p : ℕ) (a b r q : ℝ) : ℝ :=
  b*(p:ℝ)*q^(p-1)-a*(p:ℝ)*r^(p-1)

 theorem edgeRate_nonnegative {a b r q : ℝ} (ha : 0≤a) (hab : a≤b) (hr : 0≤r) (hrq : r≤q) :
    0≤edgeRate p a b r q := by
  have hb : 0≤b := ha.trans hab
  unfold edgeRate
  apply sub_nonneg.mpr
  gcongr

 theorem actual_remainder_increment_gram (hN : 0<N) (hp : 2≤p) {a b r d : ℝ}
    (ha : 0≤a) (hab : a≤b) (x u v : Vector N) (hx : ‖x‖^2=(N:ℝ)*r)
    (hu : inner ℝ u x=0) (hv : inner ℝ v x=0)
    (hnu : ‖u‖^2=(N:ℝ)*d) (hnv : ‖v‖^2=(N:ℝ)*d) :
    (∑I : TensorIndex N p⊕TensorIndex N p,
      (remainderCoeff a b x u I-remainderCoeff a b x v I)^2)=
      2*(N:ℝ)*(b*((r+d)^p-(r+inner ℝ u v/(N:ℝ))^p)-
        a*(p:ℝ)*r^(p-1)*(d-inner ℝ u v/(N:ℝ))) := by
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  have hxu0 : inner ℝ x u=0 := (real_inner_comm x u).symm.trans hu
  have hxv0 : inner ℝ x v=0 := (real_inner_comm x v).symm.trans hv
  have hxu : inner ℝ x (x+u)/(N:ℝ)=r := by rw [inner_add_right,real_inner_self_eq_norm_sq,hx,hxu0,add_zero,mul_div_cancel_left₀ r hn]
  have hxv : inner ℝ x (x+v)/(N:ℝ)=r := by rw [inner_add_right,real_inner_self_eq_norm_sq,hx,hxv0,add_zero,mul_div_cancel_left₀ r hn]
  have hyu : ‖x+u‖^2=(N:ℝ)*(r+d) := by rw [norm_add_sq_real,hx,hnu,hxu0];ring
  have hyv : ‖x+v‖^2=(N:ℝ)*(r+d) := by rw [norm_add_sq_real,hx,hnv,hxv0];ring
  have huv : inner ℝ (x+u) (x+v)/(N:ℝ)=r+inner ℝ u v/(N:ℝ) := by
    rw [inner_add_left,inner_add_right,inner_add_right,real_inner_self_eq_norm_sq,hx,
      hxv0,hu,add_zero,zero_add,add_div,mul_div_cancel_left₀ r hn]
  have hdu : inner ℝ (u-v) x=0 := by rw [inner_sub_left,hu,hv];ring
  have hgrad : (∑I : TensorIndex N p,(firstCoeff I x (u-v))^2)=
      (p:ℝ)*r^(p-1)*‖u-v‖^2 := by
    simpa only [pow_two,real_inner_self_eq_norm_sq] using first_tangent_gram hN hp x (u-v) (u-v) hx hdu
  have hdiff : ‖u-v‖^2=2*(N:ℝ)*(d-inner ℝ u v/(N:ℝ)) := by
    rw [norm_sub_sq_real,hnu,hnv]
    field_simp
    <;> ring
  have hsum : (∑I : TensorIndex N p,
      ((hamiltonianCoefficient I (x+u)-hamiltonianCoefficient I (x+v))-firstCoeff I x (u-v))^2)=
      2*(N:ℝ)*((r+d)^p-(r+inner ℝ u v/(N:ℝ))^p)-(p:ℝ)*r^(p-1)*‖u-v‖^2 := by
    have hfull := coefficient_full_difference (p:=p) hN (by omega) (x+u) (x+v) hyu hyv
    rw [huv] at hfull
    simp only [pow_two] at hfull
    rw [square_difference_sum,hfull,coefficient_gradient_difference hN x u v hxu hxv]
    have hgr := hgrad
    simp only [pow_two] at hgr
    rw [hgr]
    ring
  rw [Fintype.sum_sum_type]
  simp only [remainderCoeff]
  have hleft (I : TensorIndex N p) :
      (Real.sqrt a*(hamiltonianCoefficient I (x+u)-hamiltonianCoefficient I x-firstCoeff I x u)-
      Real.sqrt a*(hamiltonianCoefficient I (x+v)-hamiltonianCoefficient I x-firstCoeff I x v))=
      Real.sqrt a*((hamiltonianCoefficient I (x+u)-hamiltonianCoefficient I (x+v))-firstCoeff I x (u-v)) := by
    simp only [firstCoeff,map_sub]
    ring
  simp_rw [hleft,←mul_sub,mul_pow,←Finset.mul_sum]
  rw [Real.sq_sqrt ha,Real.sq_sqrt (sub_nonneg.mpr hab),hsum,
    coefficient_full_difference (p:=p) hN (by omega) (x+u) (x+v) hyu hyv,huv,hdiff]
  ring

 theorem actual_remainder_increment_bound (hN : 0<N) (hp : 2≤p) {a b r d : ℝ}
    (ha : 0≤a) (hab : a≤b) (hr : 0≤r) (hd : 0≤d) (x u v : Vector N)
    (hx : ‖x‖^2=(N:ℝ)*r) (hu : inner ℝ u x=0) (hv : inner ℝ v x=0)
    (hnu : ‖u‖^2=(N:ℝ)*d) (hnv : ‖v‖^2=(N:ℝ)*d) :
    (∑I : TensorIndex N p⊕TensorIndex N p,(remainderCoeff a b x u I-remainderCoeff a b x v I)^2)≤
      edgeRate p a b r (r+d)*‖u-v‖^2 := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hnormeq : ‖v‖=‖u‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hnv.trans hnu.symm)
  have hit : |inner ℝ u v|≤(N:ℝ)*d := by
    apply (abs_real_inner_le_norm u v).trans_eq
    rw [hnormeq,←pow_two,hnu]
  have hquot : |inner ℝ u v/(N:ℝ)|≤d := by
    rw [abs_div,abs_of_pos hn]
    exact (div_le_iff₀ hn).mpr (hit.trans_eq (by ring))
  have hz : |r+inner ℝ u v/(N:ℝ)|≤r+d :=
    (abs_add_le _ _).trans (by rw [abs_of_nonneg hr];gcongr)
  have hpower := power_secant_upper (add_nonneg hr hd) hz p
  have hdiff : ‖u-v‖^2=2*(N:ℝ)*(d-inner ℝ u v/(N:ℝ)) := by
    rw [norm_sub_sq_real,hnu,hnv]
    field_simp
    <;> ring
  rw [actual_remainder_increment_gram hN hp ha hab x u v hx hu hv hnu hnv,hdiff]
  have hb := ha.trans hab
  have hh := mul_le_mul_of_nonneg_left hpower hb
  have hs := mul_le_mul_of_nonneg_left (sub_le_sub_right hh
    (a*(p:ℝ)*r^(p-1)*(d-inner ℝ u v/(N:ℝ)))) (mul_nonneg (by norm_num : (0:ℝ)≤2) hn.le)
  exact hs.trans_eq (by unfold edgeRate;ring)

end SphericalAging.HamiltonianOneReplicaEdgeCoefficients
