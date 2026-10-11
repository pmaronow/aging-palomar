module

public import SphericalAging.VectorQuarticSourceBound

public section

/-! Actual quartic production for coordinatewise bounded linear coefficients
and genuine quadratic forcing. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal InnerProductSpace
namespace SphericalAging.AffineQuarticProduction
open HardSphereDynamics VectorSourceFourthMoment VectorQuarticSourceBound
set_option maxHeartbeats 1600000
variable {N : ℕ}

@[expose] def rate (N : ℕ) (Kb Ks : ℝ≥0) : ℝ≥0 := 4*N*Kb+12*N^2*Ks^2+6

@[expose] def sourceFactor (N : ℕ) (Lb Ls : ℝ≥0) : ℝ≥0 := (N*Lb)^4+3*(2*N*Ls)^4

theorem row_norm_le (a : Fin N→ℝ) (B : ℝ) (h : ∀i,‖a i‖≤B) :
    ‖WithLp.toLp 2 a‖≤N*B := by
  have he : WithLp.toLp 2 a=∑i : Fin N,a i • basisVector i := by
    ext i
    simp [basisVector,Pi.single_apply]
  rw [he]
  calc
    _≤∑i : Fin N,‖a i • basisVector i‖ := norm_sum_le _ _
    _≤∑_i : Fin N,B := Finset.sum_le_sum (fun i _ => by simpa [basisVector,norm_smul] using h i)
    _=_ := by simp

theorem quadratic_fourthProduction_le (x : State N) (a : Fin N→ℝ) (b : Fin N→Fin N→ℝ)
    (Kb Ks Lb Ls : ℝ≥0) (u v : ℝ) (hu : 0≤u) (hv : 0≤v)
    (ha : ∀i,‖a i‖≤(Kb:ℝ)*‖x‖+(Lb:ℝ)*u*v)
    (hb : ∀i j,‖b i j‖≤(Ks:ℝ)*‖x‖+(Ls:ℝ)*u*v) :
    fourthProduction x a b≤(rate N Kb Ks:ℝ)*‖x‖^4+(sourceFactor N Lb Ls:ℝ)*(u*v)^4 := by
  have ha' : ‖WithLp.toLp 2 a‖≤(N:ℝ)*Kb*‖x‖+((N:ℝ)*Lb)*(u*v) := by
    convert row_norm_le a _ ha using 1 <;> ring
  have hb' : (∑i : Fin N,∑j : Fin N,(b i j)^2)≤
      (2*(N:ℝ)^2*(Ks:ℝ)^2)*‖x‖^2+(2*(N:ℝ)*Ls*(u*v))^2 := by
    have hij (i j : Fin N) : (b i j)^2≤2*((Ks:ℝ)*‖x‖)^2+2*((Ls:ℝ)*u*v)^2 := by
      have hp := pow_le_pow_left₀ (norm_nonneg _) (hb i j) 2
      rw [Real.norm_eq_abs,sq_abs] at hp
      nlinarith only [hp,sq_nonneg ((Ks:ℝ)*‖x‖-(Ls:ℝ)*u*v)]
    calc
      _≤∑_i : Fin N,∑_j : Fin N,(2*((Ks:ℝ)*‖x‖)^2+2*((Ls:ℝ)*u*v)^2) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hij i j))
      _≤_ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];
                nlinarith only [sq_nonneg ((N:ℝ)*(Ls:ℝ)*(u*v))]
  have hh := fourthProduction_le x a b ((N:ℝ)*Kb) (2*(N:ℝ)^2*(Ks:ℝ)^2)
    ((N:ℝ)*Lb*(u*v)) (2*(N:ℝ)*Ls*(u*v)) (by positivity) (by positivity)
    (by positivity) (by positivity) ha' hb'
  convert hh using 1 <;> simp only [rate,sourceFactor,NNReal.coe_add,NNReal.coe_mul,
    NNReal.coe_pow,NNReal.coe_ofNat,NNReal.coe_natCast] <;> ring

end SphericalAging.AffineQuarticProduction
