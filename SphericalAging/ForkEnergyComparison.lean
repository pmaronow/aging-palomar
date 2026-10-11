module

public import SphericalAging.GaussianLandscapeMoments
public import SphericalAging.LandscapeDerivatives
public import SphericalAging.WienerPairingFunctional
public import Mathlib.Analysis.Calculus.MeanValue
public import SphericalAging.SphereGibbsEntropy

public section

/-! Genuine dimension-uniform Hamiltonian comparison on the normalized
fork ball. All energy bounds are derived from actual landscape moments. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace RealInnerProductSpace
namespace SphericalAging.ForkEnergyComparison
open FiniteModel GaussianLandscape GaussianLandscapeMoments LandscapeDerivatives

theorem gradient_ball_bound {N p : ℕ} (hN : 0<N) {C : ℝ} (hC : 0≤C)
    (J : Disorder N p) {x : Vector N} (hx : ‖x‖≤C*Real.sqrt N) :
    ‖gradient (Hamiltonian N p J) x‖≤(p:ℝ)*C^(p-1)*landscapeNorm N p J*Real.sqrt N := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hR := Real.sqrt_pos.mpr hNr
  have hnorm : 0≤normalization N p := Real.rpow_nonneg hNr.le _
  calc
    _ ≤ normalization N p*(p:ℝ)*‖tensorForm N p J‖*‖x‖^(p-1) :=
      Hamiltonian_gradient_norm_le J x
    _ ≤ normalization N p*(p:ℝ)*‖tensorForm N p J‖*(C*Real.sqrt N)^(p-1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _)
        (by positivity)
    _ = (p:ℝ)*C^(p-1)*‖tensorForm N p J‖*(normalization N p*Real.sqrt N^(p-1)) := by
      rw [mul_pow]
      ring
    _ = _ := by rw [normalization_sqrt_power hN];unfold landscapeNorm;field_simp

theorem Hamiltonian_ball_lipschitz {N p : ℕ} (hN : 0<N) {C : ℝ} (hC : 0≤C)
    (J : Disorder N p) {x y : Vector N}
    (hx : ‖x‖≤C*Real.sqrt N) (hy : ‖y‖≤C*Real.sqrt N) :
    |Hamiltonian N p J x-Hamiltonian N p J y|≤
      (p:ℝ)*C^(p-1)*landscapeNorm N p J*Real.sqrt N*‖x-y‖ := by
  have hb : ∀ z ∈ Metric.closedBall (0 : Vector N) (C*Real.sqrt N),
      ‖fderiv ℝ (Hamiltonian N p J) z‖≤
        (p:ℝ)*C^(p-1)*landscapeNorm N p J*Real.sqrt N := by
    intro z hz
    rw [Metric.mem_closedBall,dist_zero_right] at hz
    have he : ‖gradient (Hamiltonian N p J) z‖=‖fderiv ℝ (Hamiltonian N p J) z‖ := by
      rw [gradient,LinearIsometryEquiv.norm_map]
    rw [←he]
    exact gradient_ball_bound hN hC J hz
  have hi := (convex_closedBall (0 : Vector N) (C*Real.sqrt N)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (Hamiltonian_hasFDerivAt J z).differentiableAt) hb
    (show y∈Metric.closedBall (0 : Vector N) (C*Real.sqrt N) by simpa using hy)
    (show x∈Metric.closedBall (0 : Vector N) (C*Real.sqrt N) by simpa using hx)
  simpa only [Real.norm_eq_abs] using hi

theorem landscape_memLp_two {N p : ℕ} (hN : 0<N) (hp : 0<p) :
    MemLp (landscapeNorm N p) 2 (disorderLaw N p) := by
  apply (memLp_two_iff_integrable_sq (landscapeNorm_continuous N p).aestronglyMeasurable).mpr
  simpa only [Real.rpow_two] using
    (uniform_real_power_moment (show 1≤N by omega) hp (k:=2) (by norm_num)).1

theorem landscape_L2_bound {N p : ℕ} (hN : 0<N) (hp : 0<p) :
    ‖(landscape_memLp_two hN hp).toLp (landscapeNorm N p)‖≤Real.sqrt (momentCeiling p 2) := by
  apply Real.le_sqrt_of_sq_le
  rw [ProjectedTreeDrift.toLp_norm_sq]
  simpa only [Real.rpow_two] using
    (uniform_real_power_moment (show 1≤N by omega) hp (k:=2) (by norm_num)).2

theorem Hamiltonian_scaled_ball_bound {N p : ℕ} (hN : 0<N) (hp : 0<p)
    {C : ℝ} (hC : 0≤C) (J : Disorder N p) {x : Vector N} (hx : ‖x‖≤C*Real.sqrt N) :
    |Hamiltonian N p J x|≤C^p*landscapeNorm N p J*(N:ℝ) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hR := Real.sqrt_pos.mpr hNr
  have hnorm : 0≤normalization N p := Real.rpow_nonneg hNr.le _
  have hh := (tensorForm N p J).le_opNorm (fun _ => x)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hh
  have hn : |Hamiltonian N p J x|≤normalization N p*‖tensorForm N p J‖*‖x‖^p := by
    rw [Hamiltonian_eq_diagonal,abs_mul,abs_of_nonneg hnorm]
    exact (mul_le_mul_of_nonneg_left hh hnorm).trans_eq (by ring)
  calc
    _ ≤ normalization N p*‖tensorForm N p J‖*‖x‖^p := hn
    _ ≤ normalization N p*‖tensorForm N p J‖*(C*Real.sqrt N)^p :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _) (by positivity)
    _ = C^p*‖tensorForm N p J‖*Real.sqrt N := by
      have hRp : Real.sqrt (N:ℝ)^p=Real.sqrt (N:ℝ)^(p-1)*Real.sqrt N := by
        rw [←pow_succ]
        congr 1
        omega
      rw [mul_pow,hRp]
      calc
        _ = C^p*‖tensorForm N p J‖*(normalization N p*Real.sqrt N^(p-1))*Real.sqrt N := by ring
        _ = _ := by rw [normalization_sqrt_power hN];ring
    _ = _ := by unfold landscapeNorm;field_simp;rw [Real.sq_sqrt hNr.le]

section Random
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem random_Hamiltonian_integrable {N p : ℕ} (hN : 0<N) (hp : 0<p)
    {C : ℝ} (hC : 0≤C) {J : Ω→Disorder N p} (hJ : HasLaw J (disorderLaw N p) μ)
    {X : Ω→Vector N} (hX : AEStronglyMeasurable X μ)
    (hXB : ∀ᵐ ω ∂μ,‖X ω‖≤C*Real.sqrt N) :
    Integrable (fun ω => Hamiltonian N p (J ω) (X ω)) μ := by
  have hQ := hJ.memLp_comp (landscape_memLp_two hN hp)
  have hi := (hQ.integrable (by norm_num : (1:ENNReal)≤2)).const_mul (C^p*(N:ℝ))
  apply hi.mono' ((SphereGibbsEntropy.Hamiltonian_joint_continuous N p).comp_aestronglyMeasurable
    (hJ.aemeasurable.aestronglyMeasurable.prodMk hX))
  filter_upwards [hXB] with ω hω
  simpa only [Real.norm_eq_abs,Function.comp_apply,mul_assoc,mul_comm,mul_left_comm] using
    Hamiltonian_scaled_ball_bound hN hp hC (J ω) hω

theorem scalar_product_L2_bound {f g : Ω→ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ ω,f ω*g ω ∂μ|≤‖hf.toLp f‖*‖hg.toLp g‖ := by
  have he : (∫ ω,f ω*g ω ∂μ)=⟪hf.toLp f,hg.toLp g⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with ω h1 h2
    simp [h1,h2,mul_comm]
  rw [he]
  exact abs_real_inner_le_norm _ _

@[expose] def distanceRoot (μ : Measure Ω) (N : ℕ) (X Y : Ω→Vector N) : ℝ :=
  lpNorm (fun ω => ‖X ω-Y ω‖) 2 μ/Real.sqrt N

@[expose] def comparisonConstant (p : ℕ) (C : ℝ) : ℝ :=
  (p:ℝ)*C^(p-1)*Real.sqrt (momentCeiling p 2)

theorem random_energy_comparison {N p : ℕ} (hN : 0<N) (hp : 0<p)
    {C : ℝ} (hC : 0≤C) {J : Ω→Disorder N p} (hJ : HasLaw J (disorderLaw N p) μ)
    {X Y : Ω→Vector N} (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ)
    (hXB : ∀ᵐ ω ∂μ,‖X ω‖≤C*Real.sqrt N)
    (hYB : ∀ᵐ ω ∂μ,‖Y ω‖≤C*Real.sqrt N) :
    |(∫ ω,Hamiltonian N p (J ω) (X ω) ∂μ)-
      (∫ ω,Hamiltonian N p (J ω) (Y ω) ∂μ)|/(N:ℝ)≤
        comparisonConstant p C*distanceRoot μ N X Y := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hR := Real.sqrt_pos.mpr hNr
  have hq : MemLp (fun ω => landscapeNorm N p (J ω)) 2 μ :=
    hJ.memLp_comp (landscape_memLp_two hN hp)
  have hx : MemLp X 2 μ := MemLp.of_bound hX (C*Real.sqrt N) hXB
  have hy : MemLp Y 2 μ := MemLp.of_bound hY (C*Real.sqrt N) hYB
  have hg : MemLp (fun ω => ‖X ω-Y ω‖) 2 μ := (hx.sub hy).norm
  have hqnorm : ‖hq.toLp (fun ω => landscapeNorm N p (J ω))‖≤Real.sqrt (momentCeiling p 2) := by
    apply Real.le_sqrt_of_sq_le
    rw [ProjectedTreeDrift.toLp_norm_sq]
    have hi := hJ.integral_comp (((landscapeNorm_continuous N p).pow 2).aestronglyMeasurable)
    dsimp only [Function.comp_apply, Pi.pow_apply] at hi
    rw [hi]
    simpa only [Real.rpow_two] using
      (uniform_real_power_moment (show 1≤N by omega) hp (k:=2) (by norm_num)).2
  have hHX := random_Hamiltonian_integrable hN hp hC hJ hX hXB
  have hHY := random_Hamiltonian_integrable hN hp hC hJ hY hYB
  have hAbs : Integrable (fun ω => |Hamiltonian N p (J ω) (X ω)-Hamiltonian N p (J ω) (Y ω)|) μ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hHX.sub hHY).norm
  let K : ℝ := (p:ℝ)*C^(p-1)
  have hK : 0≤K := by dsimp only [K];positivity
  have hProd := hq.integrable_mul hg
  have hbound : (∫ ω,|Hamiltonian N p (J ω) (X ω)-Hamiltonian N p (J ω) (Y ω)| ∂μ)≤
      K*Real.sqrt N*(∫ ω,landscapeNorm N p (J ω)*‖X ω-Y ω‖ ∂μ) := by
    rw [←integral_const_mul]
    apply integral_mono_ae hAbs (hProd.const_mul (K*Real.sqrt N))
    filter_upwards [hXB,hYB] with ω h1 h2
    exact (Hamiltonian_ball_lipschitz hN hC (J ω) h1 h2).trans_eq
      (by dsimp only [K, Pi.mul_apply];ring)
  have hCS := scalar_product_L2_bound hq hg
  have hnonneg : 0≤∫ ω,landscapeNorm N p (J ω)*‖X ω-Y ω‖ ∂μ :=
    integral_nonneg (fun ω => mul_nonneg (landscapeNorm_nonnegative _ _ _) (norm_nonneg _))
  rw [abs_of_nonneg hnonneg] at hCS
  have hCS' := hCS.trans (mul_le_mul_of_nonneg_right hqnorm (norm_nonneg _))
  calc
    _ = |∫ ω,Hamiltonian N p (J ω) (X ω)-Hamiltonian N p (J ω) (Y ω) ∂μ|/(N:ℝ) := by
      rw [integral_sub hHX hHY]
    _ ≤ (∫ ω,|Hamiltonian N p (J ω) (X ω)-Hamiltonian N p (J ω) (Y ω)| ∂μ)/(N:ℝ) :=
      div_le_div_of_nonneg_right (by simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ:=μ)
          (fun ω => Hamiltonian N p (J ω) (X ω)-Hamiltonian N p (J ω) (Y ω)))) hNr.le
    _ ≤ K*Real.sqrt N*(∫ ω,landscapeNorm N p (J ω)*‖X ω-Y ω‖ ∂μ)/(N:ℝ) :=
      div_le_div_of_nonneg_right hbound hNr.le
    _ ≤ K*Real.sqrt N*(Real.sqrt (momentCeiling p 2)*‖hg.toLp (fun ω => ‖X ω-Y ω‖)‖)/(N:ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hCS' (mul_nonneg hK hR.le)) hNr.le
    _ = _ := by
      rw [Lp.norm_toLp]
      unfold comparisonConstant distanceRoot K lpNorm
      field_simp
      rw [Real.sq_sqrt hNr.le]
      ring

end Random

end SphericalAging.ForkEnergyComparison
