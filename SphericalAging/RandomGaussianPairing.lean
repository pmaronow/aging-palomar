module

public import SphericalAging.ForkEnergyComparison
public import SphericalAging.GaussianSphereDirection
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

public section

/-! Dimension-normalized genuine Gaussian pairings and their L² comparison.
The tested vector may depend on the Gaussian seed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal InnerProductSpace
namespace SphericalAging.RandomGaussianPairing
open FiniteModel ForkEnergyComparison SphereInitialLaw GaussianRadiusVariance
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

@[expose] def pairing {N : ℕ} (X G : Ω→Vector N) : ℝ :=
  (∫ω,⟪X ω,G ω⟫_ℝ ∂μ)/(N:ℝ)

theorem inner_integrable {N : ℕ} {X G : Ω→Vector N}
    (hX : MemLp X 2 μ) (hG : MemLp G 2 μ) :
    Integrable (fun ω => ⟪X ω,G ω⟫_ℝ) μ := by
  apply (L2.integrable_inner (hX.toLp X) (hG.toLp G)).congr
  filter_upwards [hX.coeFn_toLp,hG.coeFn_toLp] with ω h1 h2
  rw [h1,h2]

theorem integral_inner_eq {N : ℕ} {X G : Ω→Vector N}
    (hX : MemLp X 2 μ) (hG : MemLp G 2 μ) :
    (∫ω,⟪X ω,G ω⟫_ℝ ∂μ)=⟪hX.toLp X,hG.toLp G⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hX.coeFn_toLp,hG.coeFn_toLp] with ω h1 h2
  rw [h1,h2]

theorem gaussian_memLp {N : ℕ} {G : Ω→Vector N}
    (hG : HasLaw G (gaussianLaw N) μ) : MemLp G 2 μ := by
  have hi : MemLp (id : Vector N→Vector N) 2 (gaussianLaw N) := by
    change MemLp id 2 (stdGaussian (Vector N))
    exact ProbabilityTheory.IsGaussian.memLp_two_id
  exact hG.memLp_comp hi

theorem gaussian_L2_norm {N : ℕ} {G : Ω→Vector N}
    (hG : HasLaw G (gaussianLaw N) μ) :
    ‖(gaussian_memLp hG).toLp G‖=Real.sqrt N := by
  apply (Real.sqrt_sq (norm_nonneg _)).symm.trans
  congr 1
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  calc
    _ = ∫ω,‖G ω‖^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [(gaussian_memLp hG).coeFn_toLp] with ω hω
      simp only [hω,real_inner_self_eq_norm_sq]
    _ = ∫x : Vector N,‖x‖^2 ∂gaussianLaw N := by
      simpa only [Function.comp_apply] using hG.integral_comp
        (show AEStronglyMeasurable (fun x : Vector N => ‖x‖^2) (gaussianLaw N) by fun_prop)
    _ = _ := by
      simpa only [gaussianLaw,finrank_euclideanSpace,Fintype.card_fin] using
        (integral_norm_sq (E:=Vector N))

theorem pairing_abs_le {N : ℕ} (hN : 0<N) {X G : Ω→Vector N}
    (hX : MemLp X 2 μ) (hG : HasLaw G (gaussianLaw N) μ) :
    |pairing (μ:=μ) X G|≤lpNorm X 2 μ/Real.sqrt N := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hR := Real.sqrt_pos.mpr hNr
  unfold pairing
  rw [abs_div,abs_of_pos hNr,integral_inner_eq hX (gaussian_memLp hG)]
  calc
    _ ≤ ‖hX.toLp X‖*‖(gaussian_memLp hG).toLp G‖/(N:ℝ) :=
      div_le_div_of_nonneg_right (abs_real_inner_le_norm _ _) hNr.le
    _ = _ := by
      rw [gaussian_L2_norm hG,Lp.norm_toLp]
      unfold lpNorm
      apply (div_eq_div_iff hNr.ne' hR.ne').mpr
      calc
        _ = (eLpNorm X 2 μ).toReal*(Real.sqrt N*Real.sqrt N) := by ring
        _ = _ := by rw [Real.mul_self_sqrt hNr.le]

theorem pairing_comparison {N : ℕ} (hN : 0<N) {X Y G : Ω→Vector N}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hG : HasLaw G (gaussianLaw N) μ) :
    |pairing (μ:=μ) X G-pairing (μ:=μ) Y G|≤distanceRoot μ N X Y := by
  have he : pairing (μ:=μ) X G-pairing (μ:=μ) Y G=pairing (μ:=μ) (X-Y) G := by
    unfold pairing
    rw [←sub_div,←integral_sub (inner_integrable hX (gaussian_memLp hG))
      (inner_integrable hY (gaussian_memLp hG))]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by simp only [Pi.sub_apply,inner_sub_left]
  rw [he]
  change |pairing (μ:=μ) (X-Y) G|≤lpNorm (fun ω => ‖(X-Y) ω‖) 2 μ/Real.sqrt N
  rw [lpNorm,eLpNorm_norm _ (hX.sub hY).aestronglyMeasurable]
  exact pairing_abs_le hN (hX.sub hY) hG

theorem distanceRoot_triangle {N : ℕ} {X Y Z : Ω→Vector N}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    distanceRoot μ N X Z≤distanceRoot μ N X Y+distanceRoot μ N Y Z := by
  have he : X-Z=(X-Y)+(Y-Z) := by module
  have hb := lpNorm_add_le (hX.sub hY) (by norm_num : (1:ENNReal)≤2)
    (g:=Y-Z)
  rw [←he] at hb
  have hXZ : lpNorm (fun ω => ‖X ω-Z ω‖) 2 μ=lpNorm (X-Z) 2 μ := by
    exact congrArg ENNReal.toReal (eLpNorm_norm (X-Z) (hX.sub hZ).aestronglyMeasurable)
  have hXY : lpNorm (fun ω => ‖X ω-Y ω‖) 2 μ=lpNorm (X-Y) 2 μ := by
    exact congrArg ENNReal.toReal (eLpNorm_norm (X-Y) (hX.sub hY).aestronglyMeasurable)
  have hYZ : lpNorm (fun ω => ‖Y ω-Z ω‖) 2 μ=lpNorm (Y-Z) 2 μ := by
    exact congrArg ENNReal.toReal (eLpNorm_norm (Y-Z) (hY.sub hZ).aestronglyMeasurable)
  unfold distanceRoot
  rw [hXZ,hXY,hYZ,←add_div]
  exact div_le_div_of_nonneg_right hb (Real.sqrt_nonneg N)

theorem distanceRoot_nonneg {N : ℕ} (X Y : Ω→Vector N) : 0≤distanceRoot μ N X Y :=
  div_nonneg lpNorm_nonneg (Real.sqrt_nonneg _)

theorem distanceRoot_sq {N : ℕ} (hN : 0<N) {X Y : Ω→Vector N}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    distanceRoot μ N X Y^2=(∫ω,‖X ω-Y ω‖^2 ∂μ)/(N:ℝ) := by
  have hf : MemLp (fun ω => ‖X ω-Y ω‖) 2 μ := (hX.sub hY).norm
  unfold distanceRoot
  rw [div_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
  congr 1
  rw [lpNorm,←Lp.norm_toLp _ hf]
  exact ProjectedTreeDrift.toLp_norm_sq hf

theorem distanceRoot_eq_sqrt {N : ℕ} (hN : 0<N) {X Y : Ω→Vector N}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    distanceRoot μ N X Y=Real.sqrt ((∫ω,‖X ω-Y ω‖^2 ∂μ)/(N:ℝ)) := by
  rw [←distanceRoot_sq hN hX hY,Real.sqrt_sq (distanceRoot_nonneg X Y)]

theorem pairing_smul {N : ℕ} (c : ℝ) (X G : Ω→Vector N) :
    pairing (μ:=μ) (c • X) G=c*pairing (μ:=μ) X G := by
  unfold pairing
  simp only [Pi.smul_apply,real_inner_smul_left,integral_const_mul]
  ring

theorem pairing_le_absolute {N : ℕ} (hN : 0<N) {X G : Ω→Vector N}
    (hX : MemLp X 2 μ) (hG : HasLaw G (gaussianLaw N) μ) :
    pairing (μ:=μ) X G≤∫ω,|⟪X ω,G ω⟫_ℝ/(N:ℝ)| ∂μ := by
  have hi := inner_integrable hX (gaussian_memLp hG)
  unfold pairing
  rw [←integral_div]
  exact integral_mono (hi.div_const _)
    (hi.div_const _).abs (fun ω => le_abs_self _)

end SphericalAging.RandomGaussianPairing
