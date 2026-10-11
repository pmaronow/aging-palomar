module

public import SphericalAging.ActualOverlapFutureInnovation
public import SphericalAging.ActualCompactOverlapInnovation
public import SphericalAging.ActualBackgroundOverlapLaw

public section

/-! Actual Brownian variance of two-time overlap. A compact earlier test agrees with the actual sphere observable. The future observed
direction and earlier backward test are both genuine process observables.
The variance bound follows from their proved innovation estimates. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualCompactBrownianOverlapVariance
open HardSphereDynamics ActualSphereTransition ActualSphereBackwardIto
open ActualOverlapBackwardTestDerivative ActualSphereMarkovRestart
open ActualOverlapFutureInnovation ActualCompactOverlapInnovation
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem brownian_overlap_variance_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (x : State N) (hx : OnSphere x) (s u : ℝ≥0)
    (hreg : SpatialC2Transition β R hR J
      (compactOverlapTest β R hR J u)) :
    variance (fun ω =>
      ⟪jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) s ω,
        jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) (s+u) ω⟫_ℝ/(N : ℝ))
      (VectorBrownian.law N)≤
      (4*u/(N : ℝ))*Real.exp (2*((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*u)+
      (4*s/(N : ℝ))*(1+Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*u))^2*
        Real.exp (2*((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*s) := by
  let P := VectorBrownian.law N
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let X := jointProcess D β R hR (J,x)
  let O : VectorBrownian.Space N → ℝ := fun ω => ⟪X s ω,X (s+u) ω⟫_ℝ/(N : ℝ)
  let g := overlapTest D β R hR J u
  let c : ℝ := transition D β R hR J s (compactOverlapTest β R hR J u) x
  have hn : 0<N := by omega
  have hX (T : ℝ≥0) := jointProcess_physical (Nat.ne_of_gt hn) (VectorBrownian.driver N)
    β R hR hNR J x hx T
  have hsphere := jointProcess_onSphere (Nat.ne_of_gt hn) (VectorBrownian.driver N) β R hR hNR J x hx
  have hXt (a : ℝ≥0) : StronglyMeasurable (X a) :=
    (jointProcess_measurable D β R hR).comp_measurable
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hO : StronglyMeasurable O := (continuous_id.div_const (N : ℝ)).comp_stronglyMeasurable
    ((hXt s).inner (hXt (s+u)))
  have hmO : MemLp O 2 P := MemLp.of_bound hO.aestronglyMeasurable 1
    (hsphere.mono (fun ω h => by
      simpa only [O,X,FiniteCorrelationIto.overlap,Real.norm_eq_abs] using
        FiniteCorrelationIto.overlap_abs_le_one hn (h s) (h (s+u))))
  have hg : Continuous g := (overlapTest_differentiable (VectorBrownian.driver N) β R hR J u).continuous
  have hmg : MemLp (fun ω => g (X s ω)) 2 P :=
    MemLp.of_bound (hg.comp_stronglyMeasurable (hXt s)).aestronglyMeasurable 1
      (hsphere.mono (fun ω h => by
        simpa only [Real.norm_eq_abs] using overlapTest_abs_le_one hn (VectorBrownian.driver N)
          β R hR hNR J u (X s ω) (h s)))
  have hmC : MemLp (fun ω => O ω-c) 2 P := hmO.sub (memLp_const c)
  have hvar : variance O P≤∫ ω,(O ω-c)^2 ∂P := by
    have hh := variance_eq_sub hmC
    simp only [Pi.pow_apply] at hh
    rw [variance_sub_const hO.aestronglyMeasurable c] at hh
    exact hh.trans_le (sub_le_self _ (sq_nonneg _))
  have hiA : Integrable (fun ω => (O ω-g (X s ω))^2) P := (hmO.sub hmg).integrable_sq
  have hiB : Integrable (fun ω => (g (X s ω)-c)^2) P := (hmg.sub (memLp_const c)).integrable_sq
  have hsplit : (∫ ω,(O ω-c)^2 ∂P)≤
      2*(∫ ω,(O ω-g (X s ω))^2 ∂P)+2*(∫ ω,(g (X s ω)-c)^2 ∂P) := by
    calc
      _≤∫ ω,2*(O ω-g (X s ω))^2+2*(g (X s ω)-c)^2 ∂P :=
        integral_mono hmC.integrable_sq ((hiA.const_mul 2).add (hiB.const_mul 2))
          (fun ω => by
            change (O ω-c)^2≤2*(O ω-g (X s ω))^2+2*(g (X s ω)-c)^2
            nlinarith [sq_nonneg (O ω-2*g (X s ω)+c)])
      _=_ := by rw [integral_add (hiA.const_mul 2) (hiB.const_mul 2),integral_const_mul,integral_const_mul]
  have hfut := future_innovation_variance_le hN hp β R hR hNR J X hX hsphere s u
  have hearly := compact_earlier_innovation_variance_le hN hp β R hR hNR J x hx s u hreg
  change (∫ ω,(O ω-g (X s ω))^2 ∂P)≤_ at hfut
  change (∫ ω,(g (X s ω)-c)^2 ∂P)≤_ at hearly
  change variance O P≤_
  refine (hvar.trans hsplit).trans ((add_le_add
    (mul_le_mul_of_nonneg_left hfut (by norm_num : (0 : ℝ)≤2))
    (mul_le_mul_of_nonneg_left hearly (by norm_num : (0 : ℝ)≤2))).trans_eq ?_)
  ring

theorem brownian_overlap_variance_le_horizon (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (x : State N) (hx : OnSphere x) (s u T : ℝ≥0) (hsu : s+u≤T)
    (hreg : SpatialC2Transition β R hR J
      (compactOverlapTest β R hR J u)) :
    variance (fun ω =>
      ⟪jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) s ω,
        jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) (s+u) ω⟫_ℝ/(N : ℝ))
      (VectorBrownian.law N)≤
      (20*T/(N : ℝ))*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*T) := by
  have hb := brownian_overlap_variance_le hN hp β R hR hNR J x hx s u hreg
  let C : ℝ := (β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J
  have hC : 0≤C := mul_nonneg (mul_nonneg β.coe_nonneg (sq_nonneg _))
    (GaussianLandscape.landscapeNorm_nonnegative N p J)
  have hs : (s : ℝ)≤T := by exact_mod_cast (le_add_right (le_refl s)).trans hsu
  have hu : (u : ℝ)≤T := by exact_mod_cast (le_add_left (le_refl u)).trans hsu
  have hsuR : (s : ℝ)+u≤T := by exact_mod_cast hsu
  have hn : 0<(N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hfut : Real.exp (2*C*u)≤Real.exp (2*C*T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu (by positivity))
  have hexp : 1≤Real.exp (C*u) := Real.one_le_exp (mul_nonneg hC u.coe_nonneg)
  have hsquare : (1+Real.exp (C*u))^2≤4*Real.exp (2*C*u) := by
    have hh := pow_le_pow_left₀ (by positivity : 0≤1+Real.exp (C*u))
      (show 1+Real.exp (C*u)≤2*Real.exp (C*u) by linarith) 2
    rw [mul_pow,← Real.exp_nat_mul] at hh
    convert hh using 1 <;> norm_num <;> ring
  have hearly : (1+Real.exp (C*u))^2*Real.exp (2*C*s)≤4*Real.exp (2*C*T) := by
    calc
      _≤(4*Real.exp (2*C*u))*Real.exp (2*C*s) :=
        mul_le_mul_of_nonneg_right hsquare (Real.exp_nonneg _)
      _=4*Real.exp (2*C*((s : ℝ)+u)) := by rw [mul_assoc,← Real.exp_add];congr 2;ring
      _≤_ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hsuR (by positivity))) (by norm_num)
  have huf : (4*u/(N : ℝ))*Real.exp (2*C*u)≤(4*T/(N : ℝ))*Real.exp (2*C*T) :=
    mul_le_mul (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu (by norm_num)) hn.le)
      hfut (Real.exp_nonneg _) (by positivity)
  have hse : (4*s/(N : ℝ))*(1+Real.exp (C*u))^2*Real.exp (2*C*s)≤
      (16*T/(N : ℝ))*Real.exp (2*C*T) := by
    rw [mul_assoc]
    calc
      _≤(4*T/(N : ℝ))*(4*Real.exp (2*C*T)) :=
        mul_le_mul (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) hn.le)
          hearly (by positivity) (by positivity)
      _=_ := by ring
  refine hb.trans ?_
  change (4*u/(N : ℝ))*Real.exp (2*C*u)+
    (4*s/(N : ℝ))*(1+Real.exp (C*u))^2*Real.exp (2*C*s)≤_
  refine (add_le_add huf hse).trans_eq ?_
  dsimp only [C]
  ring

end SphericalAging.ActualCompactBrownianOverlapVariance
