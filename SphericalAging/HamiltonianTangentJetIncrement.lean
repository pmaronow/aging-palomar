module

public import SphericalAging.HamiltonianTangentJetCovariance

public section

/-! The exact tangent jet coefficient increment bound needed for the
sharp Gaussian linear comparison in the expected-edge estimate. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.HamiltonianTangentJetIncrement
open Set FiniteModel HamiltonianDerivativeCovariance HamiltonianTangentJetCovariance
open scoped BigOperators InnerProductSpace
variable {N p : ℕ}

 theorem first_tangent_gram (hN : 0<N) (hp : 2≤p) (x u v : Vector N)
    {r : ℝ} (hx : ‖x‖^2=(N:ℝ)*r) (hu : inner ℝ u x=0) :
    (∑I : TensorIndex N p,firstCoeff I x u*firstCoeff I x v)=
      (p:ℝ)*r^(p-1)*inner ℝ u v := by
  have he : inner ℝ x x/(N:ℝ)=r := by
    rw [real_inner_self_eq_norm_sq,hx]
    exact mul_div_cancel_left₀ r (Nat.cast_ne_zero.mpr hN.ne')
  simpa only [firstCoeff,he,hu,mul_zero,zero_mul,add_zero] using
    coefficient_gradient_cross_gram_overlap hN hp x x u v

 theorem second_tangent_gram_overlap (hN : 0<N) (hp : 2≤p) (x u v : Vector N)
    {r : ℝ} (hx : ‖x‖^2=(N:ℝ)*r) (hu : inner ℝ u x=0) :
    (∑I : TensorIndex N p,secondCoeff I x u*secondCoeff I x v)=
      (2*(p:ℝ)*((p:ℝ)-1)*r^(p-2)/(N:ℝ))*(inner ℝ u v)^2 := by
  have he : inner ℝ x x/(N:ℝ)=r := by
    rw [real_inner_self_eq_norm_sq,hx]
    exact mul_div_cancel_left₀ r (Nat.cast_ne_zero.mpr hN.ne')
  rw [second_tangent_gram hp x u v hu]
  calc
    _ = (2*(p:ℝ)*((p:ℝ)-1))*(normalization N p^2*(inner ℝ x x)^(p-2))*(inner ℝ u v)^2 := by ring
    _ = _ := by rw [normalization_second_power hN hp,he];ring

 theorem square_difference_sum {ι : Type*} [Fintype ι] (a b : ι→ℝ) :
    (∑i,(a i-b i)^2)=(∑i,a i*a i)+(∑i,b i*b i)-2*(∑i,a i*b i) := by
  calc
    _ = ∑i,(a i*a i+b i*b i-2*(a i*b i)) := Finset.sum_congr rfl (fun i _ => by ring)
    _ = _ := by rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum]

 theorem first_tangent_increment_gram (hN : 0<N) (hp : 2≤p) (x u v : Vector N)
    {r : ℝ} (hx : ‖x‖^2=(N:ℝ)*r) (hu : inner ℝ u x=0) (hv : inner ℝ v x=0) :
    (∑I : TensorIndex N p,(firstCoeff I x u-firstCoeff I x v)^2)=
      (p:ℝ)*r^(p-1)*‖u-v‖^2 := by
  rw [square_difference_sum,first_tangent_gram hN hp x u u hx hu,
    first_tangent_gram hN hp x v v hx hv,first_tangent_gram hN hp x u v hx hu,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,norm_sub_sq_real]
  ring

 theorem second_tangent_increment_gram (hN : 0<N) (hp : 2≤p) (x u v : Vector N)
    {r : ℝ} (hx : ‖x‖^2=(N:ℝ)*r) (hu : inner ℝ u x=0) (hv : inner ℝ v x=0) :
    (∑I : TensorIndex N p,(secondCoeff I x u-secondCoeff I x v)^2)=
      (2*(p:ℝ)*((p:ℝ)-1)*r^(p-2)/(N:ℝ))*(‖u‖^4+‖v‖^4-2*(inner ℝ u v)^2) := by
  rw [square_difference_sum,second_tangent_gram_overlap hN hp x u u hx hu,
    second_tangent_gram_overlap hN hp x v v hx hv,second_tangent_gram_overlap hN hp x u v hx hu,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  ring

@[expose]  def jetCoeff (a b : ℝ) (x u : Vector N) : (TensorIndex N p⊕TensorIndex N p)→ℝ
  | Sum.inl I => Real.sqrt (b-a)*firstCoeff I x u
  | Sum.inr I => (Real.sqrt a/2)*secondCoeff I x u

@[expose]  def jetRate (p : ℕ) (a b r d : ℝ) : ℝ :=
  (b-a)*(p:ℝ)*r^(p-1)+a*(p:ℝ)*((p:ℝ)-1)*r^(p-2)*d

 theorem jetRate_nonnegative (hp : 2≤p) {a b r d : ℝ}
    (ha : 0≤a) (hab : a≤b) (hr : 0≤r) (hd : 0≤d) : 0≤jetRate p a b r d := by
  have hp1 : (1:ℝ)≤p := by exact_mod_cast (show 1≤p by omega)
  unfold jetRate
  positivity

 theorem jet_increment_bound (hN : 0<N) (hp : 2≤p) {a b r d : ℝ}
    (ha : 0≤a) (hab : a≤b) (hr : 0≤r) (hd : 0≤d) (x u v : Vector N)
    (hx : ‖x‖^2=(N:ℝ)*r) (hu : inner ℝ u x=0) (hv : inner ℝ v x=0)
    (hnu : ‖u‖^2=(N:ℝ)*d) (hnv : ‖v‖^2=(N:ℝ)*d) :
    (∑I : TensorIndex N p⊕TensorIndex N p,(jetCoeff (p:=p) a b x u I-jetCoeff (p:=p) a b x v I)^2)≤jetRate p a b r d*‖u-v‖^2 := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hp1 : (1:ℝ)≤p := by exact_mod_cast (show 1≤p by omega)
  have hdiff := norm_sub_sq_real u v
  rw [hnu,hnv] at hdiff
  have hcore : ((N:ℝ)*d)^2-(inner ℝ u v)^2≤((N:ℝ)*d)*‖u-v‖^2 := by
    nlinarith [sq_nonneg ((N:ℝ)*d-inner ℝ u v)]
  have hs : (Real.sqrt a/2)^2=a/4 := by rw [div_pow,Real.sq_sqrt ha];norm_num
  rw [Fintype.sum_sum_type]
  simp only [jetCoeff]
  simp_rw [←mul_sub,mul_pow,←Finset.mul_sum]
  rw [Real.sq_sqrt (sub_nonneg.mpr hab),hs,
    first_tangent_increment_gram hN hp x u v hx hu hv,
    second_tangent_increment_gram hN hp x u v hx hu hv]
  have hpowu : ‖u‖^4=((N:ℝ)*d)^2 := by nlinarith [sq_nonneg ‖u‖]
  have hpowv : ‖v‖^4=((N:ℝ)*d)^2 := by nlinarith [sq_nonneg ‖v‖]
  rw [hpowu,hpowv]
  calc
    _ = (b-a)*((p:ℝ)*r^(p-1)*‖u-v‖^2)+
        (a*(p:ℝ)*((p:ℝ)-1)*r^(p-2)/(N:ℝ))*(((N:ℝ)*d)^2-(inner ℝ u v)^2) := by ring
    _ ≤ (b-a)*((p:ℝ)*r^(p-1)*‖u-v‖^2)+
        (a*(p:ℝ)*((p:ℝ)-1)*r^(p-2)/(N:ℝ))*(((N:ℝ)*d)*‖u-v‖^2) := by
      gcongr
    _ = _ := by unfold jetRate;field_simp

end SphericalAging.HamiltonianTangentJetIncrement
