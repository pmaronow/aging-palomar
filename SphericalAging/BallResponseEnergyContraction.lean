module

public import SphericalAging.ResponseMatrixEnergyContraction

public section

/-! Rank-one energy errors for actual finite fork means. Both vectors
may lie in the sphere ball, so the bound applies to the center without
asserting that its norm is exactly sqrt(N). -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.BallResponseEnergyContraction
open MeasureTheory ProbabilityTheory FiniteModel HardSphereDynamics
  FiniteCorrelationIto EnergyCovarianceContraction ResponseMatrixEnergyContraction
open scoped NNReal ENNReal BigOperators InnerProductSpace
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem overlap_abs_le_one_ball (hN : 0<N) {x y : State N}
    (hx : ‖x‖≤Real.sqrt (N:ℝ)) (hy : ‖y‖≤Real.sqrt (N:ℝ)) : |overlap x y|≤1 := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  rw [overlap,abs_div,abs_of_pos hn,div_le_one hn]
  exact (abs_real_inner_le_norm x y).trans
    ((mul_le_mul hx hy (norm_nonneg _) (Real.sqrt_nonneg _)).trans_eq (Real.mul_self_sqrt hn.le))

theorem ball_sample_pairing_sq_le (M : State N→L[ℝ] Lp (State N) 2 P) (ω : Ω)
    {x y : State N} (hx : ‖x‖≤Real.sqrt (N:ℝ)) (hy : ‖y‖≤Real.sqrt (N:ℝ)) :
    ⟪y,sampleMatrix M ω x⟫_ℝ^2≤(N:ℝ)^2*∑i : Fin N,‖M (basisVector i) ω‖^2 := by
  have hxsq : ‖x‖^2≤(N:ℝ) := ((sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hx).trans_eq
    (Real.sq_sqrt (Nat.cast_nonneg N))
  have hysq : ‖y‖^2≤(N:ℝ) := ((sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hy).trans_eq
    (Real.sq_sqrt (Nat.cast_nonneg N))
  have hinner := pow_le_pow_left₀ (abs_nonneg _)
    (abs_real_inner_le_norm y (sampleMatrix M ω x)) 2
  simp only [sq_abs,mul_pow] at hinner
  calc
    _≤‖y‖^2*‖sampleMatrix M ω x‖^2 := hinner
    _≤‖y‖^2*(‖x‖^2*(∑i : Fin N,‖M (basisVector i) ω‖^2)) :=
      mul_le_mul_of_nonneg_left (sampleMatrix_apply_norm_sq_le M ω x) (sq_nonneg _)
    _≤(N:ℝ)*((N:ℝ)*(∑i : Fin N,‖M (basisVector i) ω‖^2)) := by
      gcongr
    _=_ := by ring

theorem ball_energyCorrection_sq_le_columns (hN : 0<N) (hp : 2≤p)
    (M : State N →L[ℝ] Lp (State N) 2 P) (ω : Ω)
    {x y : State N} (hx : ‖x‖≤Real.sqrt (N:ℝ)) (hy : ‖y‖≤Real.sqrt (N:ℝ)) :
    (energyCorrection (p := p) x y (sampleMatrix M ω))^2 ≤
      ((p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ)^2)*
        (∑ i : Fin N,‖(M (basisVector i)) ω‖^2) := by
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  have hp1 : (1 : ℝ)≤p := by exact_mod_cast (show 1≤p from by omega)
  have hpm : 0≤(p : ℝ)-1 := by linarith
  have hK : 0≤(p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2 := by positivity
  have hc : |overlap x y|^(p-2)≤1 := pow_le_one₀ (abs_nonneg _) (overlap_abs_le_one_ball hN hx hy)
  have ha : |energyCorrection (p := p) x y (sampleMatrix M ω)| ≤
      ((p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2)*|inner ℝ y (sampleMatrix M ω x)| := by
    rw [energyCorrection,abs_mul,abs_mul,abs_of_nonneg hK,abs_pow]
    simpa only [mul_one] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc hK) (abs_nonneg _)
  have hs := pow_le_pow_left₀ (abs_nonneg _) ha 2
  simp only [sq_abs,mul_pow] at hs
  calc
    _ ≤ ((p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2)^2*(inner ℝ y (sampleMatrix M ω x))^2 := hs
    _ ≤ ((p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2)^2*
        ((N : ℝ)^2*(∑ i : Fin N,‖(M (basisVector i)) ω‖^2)) :=
      mul_le_mul_of_nonneg_left (ball_sample_pairing_sq_le M ω hx hy) (sq_nonneg _)
    _ = _ := by field_simp <;> ring

theorem ball_energyCorrection_secondMoment (hN : 0<N) (hp : 2≤p)
    (M : State N →L[ℝ] Lp (State N) 2 P) (C : ℝ)
    (hm : ∀ i : Fin N,MemLp (M (basisVector i) : Ω → State N) 4 P)
    (hb : ∀ i : Fin N,(∫ ω,‖(M (basisVector i)) ω‖^4 ∂P)≤C)
    {x y : Ω → State N} (hxm : AEStronglyMeasurable x P) (hym : AEStronglyMeasurable y P)
    (hx : ∀ᵐ ω ∂P,‖x ω‖≤Real.sqrt (N:ℝ)) (hy : ∀ᵐ ω ∂P,‖y ω‖≤Real.sqrt (N:ℝ)) :
    MemLp (fun ω => energyCorrection (p := p) (x ω) (y ω) (sampleMatrix M ω)) 2 P ∧
    (∫ ω,(energyCorrection (p := p) (x ω) (y ω) (sampleMatrix M ω))^2 ∂P)≤
      ((p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ))*(1+C) := by
  let K : ℝ := (p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ)^2
  have hK : 0≤K := by dsimp [K];positivity
  have hbound : ∀ᵐ ω ∂P,(energyCorrection (p := p) (x ω) (y ω) (sampleMatrix M ω))^2≤
      K*(∑ i : Fin N,‖(M (basisVector i)) ω‖^2) := by
    filter_upwards [hx,hy] with ω hxx hyy
    exact ball_energyCorrection_sq_le_columns hN hp M ω hxx hyy
  have hi : Integrable (fun ω => K*(∑ i : Fin N,‖(M (basisVector i)) ω‖^2)) P := (integrable_finsetSum Finset.univ
    (fun i _ => (Lp.memLp (M (basisVector i))).integrable_norm_pow')).const_mul K
  have hmeas := energyCorrection_aestronglyMeasurable (p := p) M hxm hym
  have hisq : Integrable (fun ω => (energyCorrection (p := p) (x ω) (y ω) (sampleMatrix M ω))^2) P :=
    hi.mono' (hmeas.pow 2) (hbound.mono (fun ω hw => by simpa only [Real.norm_eq_abs,abs_pow,sq_abs] using hw))
  refine ⟨(memLp_two_iff_integrable_sq hmeas).mpr hisq,?_⟩
  calc
    _ ≤ ∫ ω,K*(∑ i : Fin N,‖(M (basisVector i)) ω‖^2) ∂P := integral_mono_ae hisq hi hbound
    _ = K*(∑ i : Fin N,∫ ω,‖(M (basisVector i)) ω‖^2 ∂P) := by
      rw [integral_const_mul,integral_finsetSum Finset.univ
        (fun i _ => (Lp.memLp (M (basisVector i))).integrable_norm_pow')]
    _ ≤ K*(∑ _i : Fin N,(1+C)) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i _ => column_secondMoment_le M C hm hb i)) hK
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      dsimp [K]
      field_simp [ne_of_gt (Nat.cast_pos.mpr hN : (0 : ℝ)<N)] <;> ring

end SphericalAging.BallResponseEnergyContraction
