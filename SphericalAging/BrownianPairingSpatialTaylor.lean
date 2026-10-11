module

public import SphericalAging.ActualGammaPredictorCompactTaylor

public section

/-! Exact spatial Taylor algebra for a Brownian/state pairing predictor.
The Brownian variable is unbounded; its linear appearance yields explicit
weighted fourth-state-increment and mixed second-increment remainders. -/
noncomputable section
open Set
open scoped InnerProductSpace
namespace SphericalAging.BrownianPairingSpatialTaylor
open HardSphereDynamics ActualGammaPredictorCompactTaylor
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

@[expose] def pairing (f : State N→State N) (g : State N→ℝ) (d : ℝ) (x b : State N) : ℝ :=
  ⟪b,f x⟫_ℝ/d+g x
@[expose] def linearIncrement (f : State N→State N) (g : State N→ℝ) (d : ℝ)
    (x b v w : State N) : ℝ :=
  ⟪b,fderiv ℝ f x v⟫_ℝ/d+fderiv ℝ g x v+⟪w,f x⟫_ℝ/d
@[expose] def remainder (f : State N→State N) (g : State N→ℝ) (d : ℝ)
    (x y b w : State N) : ℝ :=
  pairing f g d y (b+w)-pairing f g d x b-linearIncrement f g d x b (y-x) w

theorem remainder_eq (f : State N→State N) (g : State N→ℝ) (d : ℝ)
    (x y b w : State N) :
    remainder f g d x y b w=
      ⟪b,f y-f x-fderiv ℝ f x (y-x)⟫_ℝ/d+
        (g y-g x-fderiv ℝ g x (y-x))+⟪w,f y-f x⟫_ℝ/d := by
  unfold remainder pairing linearIncrement
  simp only [inner_add_left,inner_sub_right]
  ring

theorem remainder_square_bound (f : State N→State N) (g : State N→ℝ) (d C : ℝ)
    (hd : 0<d) (hC : 0≤C) (hBound : SpatialBound f g C)
    (x y b w : State N) (hx : x∈Metric.closedBall (0 : State N) (Real.sqrt N))
    (hy : y∈Metric.closedBall (0 : State N) (Real.sqrt N)) :
    (remainder f g d x y b w)^2≤3*(C/d+C)^2*
      ((1+‖b‖^2)*‖y-x‖^4+‖w‖^2*‖y-x‖^2) := by
  obtain ⟨_,_,hb⟩ := hBound x hx
  obtain ⟨hml,_,hmt,hgt⟩ := hb y hy
  let K := C/d+C
  have hK : 0≤K := add_nonneg (div_nonneg hC hd.le) hC
  have hCK : C≤K := le_add_of_nonneg_left (div_nonneg hC hd.le)
  have hCdK : C/d≤K := le_add_of_nonneg_right hC
  let a := K*‖b‖*‖y-x‖^2
  let c := K*‖y-x‖^2
  let e := K*‖w‖*‖y-x‖
  have ha : ‖⟪b,f y-f x-fderiv ℝ f x (y-x)⟫_ℝ/d‖≤a := by
    rw [norm_div,Real.norm_of_nonneg hd.le]
    calc
      _≤(‖b‖*(C*‖y-x‖^2))/d := div_le_div_of_nonneg_right
        ((norm_inner_le_norm (𝕜:=ℝ) _ _).trans (mul_le_mul_of_nonneg_left hmt (norm_nonneg _))) hd.le
      _=(C/d)*‖b‖*‖y-x‖^2 := by ring
      _≤a := by dsimp only [a];gcongr
  have hc : ‖g y-g x-fderiv ℝ g x (y-x)‖≤c :=
    hgt.trans (mul_le_mul_of_nonneg_right hCK (sq_nonneg _))
  have he : ‖⟪w,f y-f x⟫_ℝ/d‖≤e := by
    rw [norm_div,Real.norm_of_nonneg hd.le]
    calc
      _≤(‖w‖*(C*‖y-x‖))/d := div_le_div_of_nonneg_right
        ((norm_inner_le_norm (𝕜:=ℝ) _ _).trans (mul_le_mul_of_nonneg_left hml (norm_nonneg _))) hd.le
      _=(C/d)*‖w‖*‖y-x‖ := by ring
      _≤e := by dsimp only [e];gcongr
  have hR : ‖remainder f g d x y b w‖≤a+c+e := by
    rw [remainder_eq]
    exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ha hc)) he)
  have hp : (remainder f g d x y b w)^2≤(a+c+e)^2 := by
    rw [←sq_abs,←Real.norm_eq_abs]
    nlinarith [norm_nonneg (remainder f g d x y b w),show 0≤a+c+e from by dsimp [a,c,e];positivity]
  calc
    _≤(a+c+e)^2 := hp
    _≤3*a^2+3*c^2+3*e^2 := by nlinarith [sq_nonneg (a-c),sq_nonneg (a-e),sq_nonneg (c-e)]
    _=_ := by dsimp only [a,c,e,K];ring

theorem linear_error_square_bound (f : State N→State N) (g : State N→ℝ) (d C : ℝ)
    (hd : 0<d) (hC : 0≤C) (hBound : SpatialBound f g C)
    (x b v z w : State N) (hx : x∈Metric.closedBall (0 : State N) (Real.sqrt N)) :
    (linearIncrement f g d x b v w-linearIncrement f g d x b z w)^2≤
      2*(C/d+C)^2*(1+‖b‖^2)*‖v-z‖^2 := by
  obtain ⟨hm,hg,_⟩ := hBound x hx
  have he : linearIncrement f g d x b v w-linearIncrement f g d x b z w=
      ⟪b,fderiv ℝ f x (v-z)⟫_ℝ/d+fderiv ℝ g x (v-z) := by
    unfold linearIncrement
    simp only [map_sub,inner_sub_right]
    ring
  let K := C/d+C
  have hK : 0≤K := add_nonneg (div_nonneg hC hd.le) hC
  have hCK : C≤K := le_add_of_nonneg_left (div_nonneg hC hd.le)
  have hCdK : C/d≤K := le_add_of_nonneg_right hC
  have ha : ‖⟪b,fderiv ℝ f x (v-z)⟫_ℝ/d‖≤K*‖b‖*‖v-z‖ := by
    rw [norm_div,Real.norm_of_nonneg hd.le]
    calc
      _≤(‖b‖*(C*‖v-z‖))/d := div_le_div_of_nonneg_right
        ((norm_inner_le_norm (𝕜:=ℝ) _ _).trans (mul_le_mul_of_nonneg_left
          ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hm (norm_nonneg _))) (norm_nonneg _))) hd.le
      _=(C/d)*‖b‖*‖v-z‖ := by ring
      _≤_ := by gcongr
  have hc : ‖fderiv ℝ g x (v-z)‖≤K*‖v-z‖ :=
    ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hg (norm_nonneg _))).trans
      (mul_le_mul_of_nonneg_right hCK (norm_nonneg _))
  rw [he]
  have hn := (norm_add_le _ _).trans (add_le_add ha hc)
  have hp : (⟪b,fderiv ℝ f x (v-z)⟫_ℝ/d+fderiv ℝ g x (v-z))^2≤
      (K*‖b‖*‖v-z‖+K*‖v-z‖)^2 := by
    rw [←sq_abs,←Real.norm_eq_abs]
    nlinarith [norm_nonneg (⟪b,fderiv ℝ f x (v-z)⟫_ℝ/d+fderiv ℝ g x (v-z)),
      show 0≤K*‖b‖*‖v-z‖+K*‖v-z‖ from by positivity]
  calc
    _≤(K*‖b‖*‖v-z‖+K*‖v-z‖)^2 := hp
    _≤2*(K*‖b‖*‖v-z‖)^2+2*(K*‖v-z‖)^2 := by
      nlinarith [sq_nonneg (K*‖b‖*‖v-z‖-K*‖v-z‖)]
    _=_ := by dsimp only [K];ring

end SphericalAging.BrownianPairingSpatialTaylor
