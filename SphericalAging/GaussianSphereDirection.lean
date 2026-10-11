module

public import SphericalAging.GaussianRadiusVariance
public import SphericalAging.SphereAnnealedIntegratedFDT

public section

/-! A literal measurable fixed-radius direction from a standard Gaussian
seed, with actual vanishing radial error. The zero vector uses a genuine
sphere fallback, rather than an undefined radial normalization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SphericalAging.GaussianSphereDirection
open MeasureTheory ProbabilityTheory FiniteModel SphereInitialLaw
  GaussianRadiusVariance SphereAnnealedIntegratedFDT HardSphereDynamics
open scoped InnerProductSpace ENNReal

@[expose] def direction (N : ℕ) (hN : 0<N) (x : Vector N) : Vector N :=
  if x=0 then Real.sqrt N • basisVector ⟨0,hN⟩ else normalize N x

theorem direction_measurable {N : ℕ} (hN : 0<N) : Measurable (direction N hN) := by
  unfold direction
  exact measurable_const.ite (measurableSet_singleton (0 : Vector N)) (normalize_measurable N)

theorem direction_norm {N : ℕ} (hN : 0<N) (x : Vector N) :
    ‖direction N hN x‖=Real.sqrt N := by
  unfold direction
  split_ifs with hx
  · simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      basisVector,EuclideanSpace.norm_single,norm_one,mul_one]
  · exact normalize_norm x hx

theorem radial_difference {N : ℕ} (hN : 0<N) (x : Vector N) :
    ‖x-direction N hN x‖=|‖x‖-Real.sqrt N| := by
  by_cases hx : x=0
  · subst x
    rw [zero_sub,norm_neg,direction_norm]
    simp only [norm_zero,zero_sub,abs_neg,abs_of_nonneg (Real.sqrt_nonneg _)]
  · rw [direction,if_neg hx]
    change ‖x-(Real.sqrt N/‖x‖) • x‖=|‖x‖-Real.sqrt N|
    have he : x-(Real.sqrt N/‖x‖) • x=(1-Real.sqrt N/‖x‖) • x := by module
    rw [he,norm_smul,Real.norm_eq_abs]
    calc
      _ = |(1-Real.sqrt N/‖x‖)*‖x‖| := by
        rw [abs_mul,abs_of_nonneg (norm_nonneg x)]
      _ = _ := by
        congr 1
        rw [sub_mul,one_mul,div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)]

theorem radial_error_le_square_error {N : ℕ} (hN : 0<N) (x : Vector N) :
    ‖x-direction N hN x‖/Real.sqrt N≤|‖x‖^2/(N:ℝ)-1| := by
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hr : 0<Real.sqrt N := Real.sqrt_pos.mpr hn
  let a := ‖x‖/Real.sqrt N
  have ha : 0≤a := div_nonneg (norm_nonneg _) hr.le
  have hb : |a-1|≤|a^2-1| := by
    rw [show a^2-1=(a-1)*(a+1) by ring,abs_mul,
      abs_of_nonneg (show 0≤a+1 by linarith)]
    exact le_mul_of_one_le_right (abs_nonneg _) (by linarith)
  have he : a^2=‖x‖^2/(N:ℝ) := by
    dsimp [a]
    rw [div_pow,Real.sq_sqrt hn.le]
  rw [radial_difference]
  have hab : |‖x‖-Real.sqrt N|/Real.sqrt N=|(‖x‖-Real.sqrt N)/Real.sqrt N| := by
    rw [abs_div,abs_of_pos hr]
  rw [hab]
  have hf : (‖x‖-Real.sqrt N)/Real.sqrt N=a-1 := by dsimp [a];field_simp
  rw [hf,←he]
  exact hb

theorem radial_error_mean_le {N : ℕ} (hN : 0<N) :
    Integrable (fun x : Vector N => ‖x-direction N hN x‖/Real.sqrt N) (gaussianLaw N) ∧
    (∫x : Vector N,‖x-direction N hN x‖/Real.sqrt N ∂gaussianLaw N)≤
      Real.sqrt (Real.pi^2/(2*(N:ℝ))) := by
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  let f (x : Vector N) := ‖x‖^2/(N:ℝ)-1
  have hf : MemLp f 2 (gaussianLaw N) := by
    change MemLp f 2 (stdGaussian (Vector N))
    convert ((memLp_norm_sq (E := Vector N)).mul_const (N:ℝ)⁻¹).sub
      (memLp_const 1 : MemLp (fun _ : Vector N => (1:ℝ)) 2 (stdGaussian (Vector N))) using 1
    funext x
    simp only [f,Pi.sub_apply,div_eq_mul_inv]
  have hi := hf.integrable (by norm_num : (1:ℝ≥0∞)≤2)
  have hsq := hf.integrable_sq
  have hmean : (∫x : Vector N,‖x‖^2 ∂gaussianLaw N)=(N:ℝ) := by
    simpa only [gaussianLaw,finrank_euclideanSpace, Fintype.card_fin] using
      integral_norm_sq (E := Vector N)
  have hv : (∫x : Vector N,f x^2 ∂gaussianLaw N)≤Real.pi^2/(2*(N:ℝ)) := by
    have he : (fun x : Vector N => f x^2)=fun x => (‖x‖^2-(N:ℝ))^2/(N:ℝ)^2 := by
      funext x
      dsimp only [f]
      field_simp <;> ring
    rw [he,integral_div]
    have hvar : (∫x : Vector N,(‖x‖^2-(N:ℝ))^2 ∂gaussianLaw N)=
        variance (fun x : Vector N => ‖x‖^2) (gaussianLaw N) := by
      rw [variance_eq_integral (by fun_prop),hmean]
    rw [hvar]
    have hh : variance (fun x : Vector N => ‖x‖^2) (gaussianLaw N)≤(Real.pi^2/2)*(N:ℝ) := by
      simpa only [gaussianLaw,finrank_euclideanSpace,Fintype.card_fin] using
        radius_variance_le (E := Vector N)
    exact (div_le_div_of_nonneg_right hh (sq_nonneg _)).trans_eq (by field_simp <;> ring)
  have habsq : Integrable (fun x => |f x|^2) (gaussianLaw N) := by simpa only [sq_abs] using hsq
  have hj := probability_integral_square_le (gaussianLaw N) hi.abs habsq
  simp only [sq_abs] at hj
  have hroot : (∫x : Vector N,|f x| ∂gaussianLaw N)≤Real.sqrt (Real.pi^2/(2*(N:ℝ))) := by
    exact (Real.le_sqrt (integral_nonneg fun _ => abs_nonneg _) (by positivity)).mpr (hj.trans hv)
  have hrad : Integrable (fun x : Vector N => ‖x-direction N hN x‖/Real.sqrt N) (gaussianLaw N) := by
    apply hi.abs.mono' ((measurable_id.sub (direction_measurable hN)).norm.div_const _).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))]
      exact radial_error_le_square_error hN x
  refine ⟨hrad,?_⟩
  exact (integral_mono hrad hi.abs (radial_error_le_square_error hN)).trans hroot

end SphericalAging.GaussianSphereDirection
