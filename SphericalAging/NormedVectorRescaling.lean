module

public import SphericalAging.FiniteModel

public section

/-! Honest norm and error bounds for rescaling an actual nonzero vector to
a prescribed squared norm. -/
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.NormedVectorRescaling
open FiniteModel
open scoped InnerProductSpace
variable {N : ℕ}

@[expose] def rescale (q : ℝ) (u : Vector N) : Vector N := Real.sqrt q • (‖u‖⁻¹ • u)

theorem rescale_norm (q : ℝ) (u : Vector N) (hu : u≠0) : ‖rescale q u‖=Real.sqrt q := by
  have hn : 0<‖u‖ := norm_pos_iff.mpr hu
  rw [rescale,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg q),abs_of_nonneg (inv_nonneg.mpr hn.le),
    inv_mul_cancel₀ hn.ne',mul_one]

theorem rescale_distance_self (q : ℝ) (u : Vector N) (hu : u≠0) :
    ‖rescale q u-u‖=|Real.sqrt q-‖u‖| := by
  have hn : 0<‖u‖ := norm_pos_iff.mpr hu
  let e := ‖u‖⁻¹ • u
  have he : ‖e‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hn.le),inv_mul_cancel₀ hn.ne']
  have heu : ‖u‖ • e=u := by
    rw [smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
  change ‖Real.sqrt q • e-u‖=_
  calc
    _=‖(Real.sqrt q-‖u‖) • e‖ := by rw [sub_smul,heu]
    _=|Real.sqrt q-‖u‖| := by rw [norm_smul,Real.norm_eq_abs,he,mul_one]

theorem nonnegative_square_difference (a b ε : ℝ) (ha : 0≤a) (hb : 0≤b)
    (hε : 0≤ε) (hsq : |a^2-b^2|≤ε) : |a-b|≤Real.sqrt ε := by
  have hsmall : |a-b|^2≤ε := by
    rcases le_total a b with hab | hba
    · rw [abs_of_nonpos (sub_nonpos.mpr hab)]
      have hh := (abs_le.mp hsq).1
      nlinarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
      have hh := (abs_le.mp hsq).2
      nlinarith
  have hroot := Real.sq_sqrt hε
  nlinarith [abs_nonneg (a-b),Real.sqrt_nonneg ε]

theorem rescale_distance (q ε : ℝ) (hq : 0≤q) (hε : 0≤ε)
    (u v : Vector N) (hu : u≠0) (hv : |‖v‖^2-q|≤ε) :
    ‖rescale q u-v‖≤2*‖u-v‖+Real.sqrt ε := by
  have hvroot : |Real.sqrt q-‖v‖|≤Real.sqrt ε := by
    apply nonnegative_square_difference _ _ ε (Real.sqrt_nonneg q) (norm_nonneg v) hε
    rw [Real.sq_sqrt hq,abs_sub_comm]
    exact hv
  have hdiff : |Real.sqrt q-‖u‖|≤Real.sqrt ε+‖u-v‖ := by
    calc
      _≤|Real.sqrt q-‖v‖|+|‖v‖-‖u‖| := by
        simpa only [sub_add_sub_cancel] using abs_add_le (Real.sqrt q-‖v‖) (‖v‖-‖u‖)
      _≤Real.sqrt ε+‖u-v‖ := add_le_add hvroot (by
        simpa only [abs_sub_comm] using abs_norm_sub_norm_le u v)
  calc
    _≤‖rescale q u-u‖+‖u-v‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (rescale q u-u) (u-v)
    _≤(Real.sqrt ε+‖u-v‖)+‖u-v‖ := by
      rw [rescale_distance_self q u hu]
      exact add_le_add_left hdiff _
    _=_ := by ring

end SphericalAging.NormedVectorRescaling
