module

public import SphericalAging.FiniteForkMoments
public import SphericalAging.ForkParameterBounds
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public section

/-! Actual finite-fork center concentration from the preceding pair-overlap
concentration. The center defect is derived from its literal Gram matrix;
no center norm-concentration conclusion is an input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.FiniteForkCenterConcentration
open MeasureTheory ProbabilityTheory Filter FiniteModel WienerForkTransfer
open ForkParameterBounds
open scoped BigOperators InnerProductSpace Topology NNReal

@[expose] def gramError {N K : ℕ} (Y : Fin K → Vector N) (c : ℝ) (b d : Fin K) : ℝ :=
  ⟪Y b,Y d⟫_ℝ/(N:ℝ)-(if b=d then 1 else c)

theorem mean_norm_gram {N K : ℕ} (Y : Fin K → Vector N) :
    ‖(K:ℝ)⁻¹ • ∑b,Y b‖^2=(K:ℝ)⁻¹^2*∑b,∑d,⟪Y b,Y d⟫_ℝ := by
  rw [←real_inner_self_eq_norm_sq]
  simp only [real_inner_smul_left,real_inner_smul_right,sum_inner,inner_sum]
  simp_rw [←Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

theorem center_defect_eq_gram {N K : ℕ} (hN : 0<N) (hK : 0<K)
    (Y : Fin K → Vector N) (c : ℝ) :
    ‖(K:ℝ)⁻¹ • ∑b,Y b‖^2/(N:ℝ)-(1/(K:ℝ)+(1-1/(K:ℝ))*c)=
      (K:ℝ)⁻¹^2*∑b,∑d,gramError Y c b d := by
  have hKne : (K:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hK
  rw [mean_norm_gram]
  simp only [gramError,Finset.sum_sub_distrib]
  have hrow (b : Fin K) : (∑d : Fin K,if b=d then (1:ℝ) else c)=1+((K:ℝ)-1)*c := by
    have he : (fun d : Fin K => if b=d then (1:ℝ) else c)=
        (fun d => c+(if b=d then 1-c else 0)) := by
      funext d;split_ifs <;> ring
    simp [he,Finset.sum_add_distrib];ring
  simp_rw [hrow]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp_rw [←Finset.sum_div]
  field_simp
  <;> ring

theorem center_defect_square_le_gram {N K : ℕ} (hN : 0<N) (hK : 0<K)
    (Y : Fin K → Vector N) (c : ℝ) :
    (‖(K:ℝ)⁻¹ • ∑b,Y b‖^2/(N:ℝ)-(1/(K:ℝ)+(1-1/(K:ℝ))*c))^2≤
      (K:ℝ)⁻¹^2*∑b,∑d,(gramError Y c b d)^2 := by
  rw [center_defect_eq_gram hN hK]
  have hKpos : (0:ℝ)<K := by exact_mod_cast hK
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin K×Fin K))
    (fun _ => (1:ℝ)) (fun z => gramError Y c z.1 z.2)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_prod,
    Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_mul] at hh
  simp only [←Finset.univ_product_univ,Finset.sum_product] at hh
  calc
    ((K:ℝ)⁻¹^2*∑b,∑d,gramError Y c b d)^2=
      (K:ℝ)⁻¹^4*(∑b,∑d,gramError Y c b d)^2 := by ring
    _ ≤ (K:ℝ)⁻¹^4*((K:ℝ)*(K:ℝ)*(∑b,∑d,(gramError Y c b d)^2)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by field_simp <;> ring

theorem branch_gramError_square_integrable {N p K : ℕ} (hN : 0<N)
    {β : ℝ} {t T : ℝ≥0} {Y : Fin K→ForkSpace N p K→Vector N}
    (hY : ForkJointLaw β t T Y) (c : ℝ) (b d : Fin K) :
    Integrable (fun z => (gramError (fun i => Y i z) c b d)^2) (forkLaw N p K) := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hmeas := (((branch_memLp hY b).aestronglyMeasurable.inner
    (branch_memLp hY d).aestronglyMeasurable).mul_const (N:ℝ)⁻¹).sub
      (aestronglyMeasurable_const (b := if b=d then (1:ℝ) else c))
  apply Integrable.of_bound (hmeas.pow 2) ((2+|c|)^2)
  filter_upwards [branch_norm_sq hY b,branch_norm_sq hY d] with z hb hd
  have hn (i : Fin K) (hi : ‖Y i z‖^2=(N:ℝ)) : ‖Y i z‖=Real.sqrt N :=
    (Real.sqrt_sq (norm_nonneg _)).symm.trans (congrArg Real.sqrt hi)
  have hi : |⟪Y b z,Y d z⟫_ℝ/(N:ℝ)|≤1 := by
    rw [abs_div,abs_of_pos hNr]
    apply (div_le_one hNr).mpr
    simpa only [hn b hb,hn d hd,Real.mul_self_sqrt hNr.le] using
      abs_real_inner_le_norm (Y b z) (Y d z)
  have hc : |if b=d then (1:ℝ) else c|≤1+|c| := by split_ifs <;> simp <;> linarith [abs_nonneg c]
  have hg : |gramError (fun i => Y i z) c b d|≤2+|c| :=
    (abs_sub _ _).trans (by linarith)
  change ‖(gramError (fun i => Y i z) c b d)^2‖≤(2+|c|)^2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤2+|c|)).mpr hg

theorem actual_center_defect_integrable {N p K : ℕ} (hN : 0<N) (hK : 0<K)
    {β : ℝ} {t T : ℝ≥0} {Y : Fin K→ForkSpace N p K→Vector N}
    (hY : ForkJointLaw β t T Y) (c : ℝ) :
    Integrable (fun z => (‖mean Y z‖^2/(N:ℝ)-(1/(K:ℝ)+(1-1/(K:ℝ))*c))^2)
      (forkLaw N p K) := by
  have hm : MemLp (mean Y) 2 (forkLaw N p K) :=
    (Lp.memLp (meanLp Y hY)).ae_eq (meanLp_coe Y hY)
  let Q := 1/(K:ℝ)+(1-1/(K:ℝ))*c
  have hc : Continuous (fun x : Vector N => (‖x‖^2/(N:ℝ)-Q)^2) := by fun_prop
  apply Integrable.of_bound (hc.comp_aestronglyMeasurable hm.aestronglyMeasurable) ((1+|Q|)^2)
  filter_upwards [mean_norm_bound hK hY] with z hz
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hi : ‖mean Y z‖^2/(N:ℝ)∈Set.Icc (0:ℝ) 1 := by
    refine ⟨by positivity,?_⟩
    exact (div_le_one hNr).mpr (((sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hz).trans_eq
      (Real.sq_sqrt hNr.le))
  have hg : |‖mean Y z‖^2/(N:ℝ)-Q|≤1+|Q| :=
    (abs_sub _ _).trans (by rw [abs_of_nonneg hi.1];exact add_le_add hi.2 le_rfl)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤1+|Q|)).mpr hg

theorem actual_center_defect_le_pair_errors {N p K : ℕ} (hN : 0<N) (hK : 0<K)
    {β : ℝ} {t T : ℝ≥0} {Y : Fin K→ForkSpace N p K→Vector N}
    (hY : ForkJointLaw β t T Y) (c : ℝ) :
    (∫z,(‖mean Y z‖^2/(N:ℝ)-(1/(K:ℝ)+(1-1/(K:ℝ))*c))^2 ∂forkLaw N p K)≤
      (K:ℝ)⁻¹^2*∑b,∑d,∫z,(gramError (fun i => Y i z) c b d)^2 ∂forkLaw N p K := by
  have hi b d := branch_gramError_square_integrable hN hY c b d
  have hs b := integrable_finset_sum Finset.univ (fun d _ => hi b d)
  have hss := integrable_finset_sum Finset.univ (fun b _ => hs b)
  have he := integral_mono (actual_center_defect_integrable hN hK hY c)
    (hss.const_mul ((K:ℝ)⁻¹^2)) (fun z => center_defect_square_le_gram hN hK (fun b => Y b z) c)
  rw [integral_const_mul,integral_finset_sum Finset.univ (fun b _ => hs b)] at he
  simp_rw [integral_finset_sum Finset.univ (fun d _ => hi _ d)] at he
  exact he

theorem actual_diagonal_gramError_zero {N p K : ℕ} (hN : 0<N)
    {β : ℝ} {t T : ℝ≥0} {Y : Fin K→ForkSpace N p K→Vector N}
    (hY : ForkJointLaw β t T Y) (c : ℝ) (b : Fin K) :
    (∫z,(gramError (fun i => Y i z) c b b)^2 ∂forkLaw N p K)=0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [branch_norm_sq hY b] with z hz
  have hNr : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  change (gramError (fun i => Y i z) c b b)^2=0
  simp [gramError,real_inner_self_eq_norm_sq,hz,hNr]

/-- Actual center concentration follows from the true off-diagonal
pair-overlap second moments along any ordered filter. In particular this
applies to the dimension-before-stationary-time curried filter. -/
theorem actual_center_defect_tendsto {ι : Type*} {l : Filter ι} {dim : ι→ℕ}
    (hDim : ∀i,0<dim i) {p K : ℕ} (hK : 0<K) {β c : ℝ} {t T : ι→ℝ≥0}
    {Y : ∀i,Fin K→ForkSpace (dim i) p K→Vector (dim i)}
    (hY : ∀i,ForkJointLaw β (t i) (T i) (Y i))
    (hPair : ∀b d : Fin K,b≠d→Tendsto
      (fun i => ∫z,(⟪Y i b z,Y i d z⟫_ℝ/(dim i:ℝ)-c)^2 ∂forkLaw (dim i) p K)
      l (𝓝 0)) :
    Tendsto (fun i => ∫z,(‖mean (Y i) z‖^2/(dim i:ℝ)-
      (1/(K:ℝ)+(1-1/(K:ℝ))*c))^2 ∂forkLaw (dim i) p K) l (𝓝 0) := by
  have hpairs (b d : Fin K) : Tendsto
      (fun i => ∫z,(gramError (fun j => Y i j z) c b d)^2 ∂forkLaw (dim i) p K)
      l (𝓝 0) := by
    by_cases hbd : b=d
    · subst d
      simp_rw [actual_diagonal_gramError_zero (hDim _) (hY _) c b]
      exact tendsto_const_nhds
    · simpa only [gramError,if_neg hbd] using hPair b d hbd
  have hs : Tendsto (fun i => (K:ℝ)⁻¹^2*∑b,∑d,
      ∫z,(gramError (fun j => Y i j z) c b d)^2 ∂forkLaw (dim i) p K) l (𝓝 0) := by
    have hh := tendsto_finset_sum (Finset.univ : Finset (Fin K))
      (fun b _ => tendsto_finset_sum (Finset.univ : Finset (Fin K)) (fun d _ => hpairs b d))
    simpa only [Finset.sum_const_zero,mul_zero] using hh.const_mul ((K:ℝ)⁻¹^2)
  exact squeeze_zero (fun i => integral_nonneg (fun _ => sq_nonneg _))
    (fun i => actual_center_defect_le_pair_errors (hDim i) hK (hY i) c) hs

end SphericalAging.FiniteForkCenterConcentration
