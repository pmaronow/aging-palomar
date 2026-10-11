module

public import SphericalAging.ActualStateIncrementMoments
public import BrownianMotion.Gaussian.Moment

public section

/-! Actual finite-vector Brownian moments. Coordinate Gaussian laws and
finite-dimensional Cauchy--Schwarz give the exact second moment and a
dimension-sharp fourth-moment ceiling. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.BrownianVectorMoments
open HardSphereDynamics LocalSDE VectorBrownian
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

@[expose] def brownianVector (t : ℝ≥0) (ω : Space N) : State N :=
  WithLp.toLp 2 (fun i => coordinate i t ω)

theorem gaussian_secondMoment (v : ℝ≥0) :
    (∫ x : ℝ,x^2 ∂gaussianReal 0 v)=(v : ℝ) := by
  have hh := centralMoment_two_mul_gaussianReal 0 (NNReal.sqrt v) 1
  rw [NNReal.sq_sqrt,centralMoment_of_integral_id_eq_zero _ (by simp)] at hh
  norm_num at hh
  simpa only [← NNReal.coe_pow,NNReal.sq_sqrt,mul_one] using hh

theorem gaussian_fourthMoment (v : ℝ≥0) :
    (∫ x : ℝ,x^4 ∂gaussianReal 0 v)=3*(v : ℝ)^2 := by
  have hh := centralMoment_two_mul_gaussianReal 0 (NNReal.sqrt v) 2
  rw [NNReal.sq_sqrt,centralMoment_of_integral_id_eq_zero _ (by simp)] at hh
  norm_num at hh
  have he : (NNReal.sqrt v : ℝ)^4=(v : ℝ)^2 := by
    rw [show (4 : ℕ)=2*2 from rfl,pow_mul,← NNReal.coe_pow,NNReal.sq_sqrt]
  rw [Real.coe_sqrt] at he
  rw [he] at hh
  simpa only [mul_comm] using hh

theorem coordinate_memLp (i : Fin N) (t : ℝ≥0) {q : ℝ≥0∞} (hq : q≠⊤) :
    MemLp (coordinate i t) q (law N) :=
  (coordinate_isPreBrownian i).isGaussianProcess.hasGaussianLaw_eval t |>.memLp hq

theorem brownianVector_memLp (t : ℝ≥0) {q : ℝ≥0∞} (hq : q≠⊤) :
    MemLp (brownianVector (N := N) t) q (law N) := by
  have hm := memLp_finsetSum Finset.univ (fun i _ => (coordinate_memLp i t hq).continuousLinearMap_comp
    (ContinuousLinearMap.toSpanSingleton ℝ (basisVector (N := N) i)))
  convert hm using 1
  funext ω
  simp only [ContinuousLinearMap.toSpanSingleton_apply]
  exact (state_sum_basis (brownianVector t ω)).symm

theorem coordinate_secondMoment (i : Fin N) (t : ℝ≥0) :
    (∫ ω,(coordinate i t ω)^2 ∂law N)=(t : ℝ) := by
  have hh := ((coordinate_isPreBrownian i).hasLaw_eval t).integral_comp
    (f := fun x : ℝ => x^2) (by fun_prop)
  exact hh.trans (gaussian_secondMoment t)

theorem coordinate_fourthMoment (i : Fin N) (t : ℝ≥0) :
    (∫ ω,(coordinate i t ω)^4 ∂law N)=3*(t : ℝ)^2 := by
  have hh := ((coordinate_isPreBrownian i).hasLaw_eval t).integral_comp
    (f := fun x : ℝ => x^4) (by fun_prop)
  exact hh.trans (gaussian_fourthMoment t)

theorem brownianVector_secondMoment (t : ℝ≥0) :
    (∫ ω,‖brownianVector (N := N) t ω‖^2 ∂law N)=(N : ℝ)*t := by
  simp_rw [← real_inner_self_eq_norm_sq,← coordinate_square_sum]
  change (∫ ω,∑ i : Fin N,(coordinate i t ω)^2 ∂law N)=(N : ℝ)*t
  rw [integral_finsetSum _ (fun i _ => (coordinate_memLp i t (q := 2) (by norm_num)).integrable_sq)]
  simp only [coordinate_secondMoment,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem vector_norm_four_le (v : State N) : ‖v‖^4≤(N : ℝ)*(∑ i : Fin N,(v i)^4) := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin N => (1 : ℝ)) (fun i => (v i)^2)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
    ← pow_mul,Nat.reduceMul,coordinate_square_sum,real_inner_self_eq_norm_sq] at hh
  simpa only [← pow_mul,Nat.reduceMul] using hh

theorem brownianVector_fourthMoment_le (t : ℝ≥0) :
    (∫ ω,‖brownianVector (N := N) t ω‖^4 ∂law N)≤3*(N : ℝ)^2*(t : ℝ)^2 := by
  have hci (i : Fin N) : Integrable (fun ω => (coordinate i t ω)^4) (law N) := by
    have hh := (coordinate_memLp i t (q := 4) (by norm_num)).integrable_norm_pow'
    simpa only [Real.norm_eq_abs,show (4 : ℕ)=2*2 from rfl,pow_mul,sq_abs] using hh
  calc
    _≤∫ ω,(N : ℝ)*(∑ i : Fin N,(coordinate i t ω)^4) ∂law N := by
      apply integral_mono (brownianVector_memLp t (q := 4) (by norm_num)).integrable_norm_pow'
        ((integrable_finsetSum Finset.univ (fun i _ => hci i)).const_mul _)
      intro ω
      exact vector_norm_four_le _
    _=(N : ℝ)*(∑ i : Fin N,∫ ω,(coordinate i t ω)^4 ∂law N) := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => hci i)]
    _=3*(N : ℝ)^2*(t : ℝ)^2 := by simp only [coordinate_fourthMoment,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

theorem brownianVector_increment_secondMoment (s t : ℝ≥0) :
    (∫ ω,‖brownianVector (N := N) (s+t) ω-brownianVector s ω‖^2 ∂law N)=(N : ℝ)*t := by
  have hc (i : Fin N) : (∫ ω,(coordinate i (s+t) ω-coordinate i s ω)^2 ∂law N)=(t : ℝ) := by
    have hl := (coordinate_isPreBrownian i).hasLaw_sub (s+t) s
    have hh := (hl.integral_comp (f := fun x : ℝ => x^2) (by fun_prop)).trans (gaussian_secondMoment _)
    simpa [Function.comp_def,coe_nndist,Real.dist_eq,NNReal.coe_add,abs_of_nonneg t.coe_nonneg] using hh
  have hi (i : Fin N) : Integrable (fun ω => (coordinate i (s+t) ω-coordinate i s ω)^2) (law N) :=
    ((coordinate_memLp i (s+t) (q := 2) (by norm_num)).sub
      (coordinate_memLp i s (q := 2) (by norm_num))).integrable_sq
  simp_rw [← real_inner_self_eq_norm_sq,← coordinate_square_sum]
  change (∫ ω,∑ i : Fin N,(coordinate i (s+t) ω-coordinate i s ω)^2 ∂law N)=(N : ℝ)*t
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp only [hc,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

end SphericalAging.BrownianVectorMoments
