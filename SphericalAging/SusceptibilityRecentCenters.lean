module

public import SphericalAging.SusceptibilityDiagonal

public section

/-! The actual recent prefix vectors approach the common plateau center
uniformly on every fixed lag interval, from the constructed diagonal receipt. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter
open scoped Topology InnerProductSpace
namespace SphericalAging.SusceptibilityRecentCenters
open CKSpecification CausalTree PrefixReflection CausalCenterAverage CenterNormalization
open SusceptibilityDiagonal CubicResponseLocalization

theorem recent_centers_uniform {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q)
    {t L : ℕ → ℝ} (A : Receipt h c q t L) {W ε : ℝ} (hW : 0<W) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∀ τ : ℝ,τ∈Icc 0 W →
      ‖prefixVector h (t n-L n) (t n-τ)-
        Real.sqrt q • normalizedCenter h (t n) (L n)‖≤ε := by
  have hn : Tendsto (fun n => ‖prefixVector h (t n-L n) (t n)‖) atTop (𝓝 (Real.sqrt q)) := by
    simpa only [Real.sqrt_sq (norm_nonneg _)] using A.norm_square_tendsto.sqrt
  have hnorm := (hn.sub_const (Real.sqrt q) |>.abs).eventually
    (gt_mem_nhds (by simpa only [sub_self,abs_zero] using (half_pos hε)))
  let η : ℝ := ε^2/32
  have hη : 0<η := by dsimp [η]; positivity
  have he : Tendsto (fun n => 1/L n) atTop (𝓝 (0:ℝ)) := by
    simpa only [one_div,Function.comp_def] using
      (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp A.age_tendsto
  obtain ⟨B,hB⟩ := eventually_atTop.mp
    ((H.plateau_limit.sub_const q |>.abs).eventually
      (gt_mem_nhds (by simpa only [sub_self,abs_zero] using hη)))
  filter_upwards [hnorm,he.eventually (gt_mem_nhds hη),
    A.age_tendsto.eventually (eventually_ge_atTop (max W (B/2+W)))] with n hn he hL
  intro τ hτ
  have hLW : W≤L n := (le_max_left W (B/2+W)).trans hL
  have hLB : B/2+W≤L n := (le_max_right W (B/2+W)).trans hL
  have ha : L n-τ∈Icc (0:ℝ) (L n) := ⟨by linarith [hτ.2],by linarith [hτ.1]⟩
  have hLL : L n∈Icc (0:ℝ) (L n) := ⟨(A.age_positive n).le,le_rfl⟩
  have hgram {a b : ℝ} (ha : a∈Icc 0 (L n)) (hb : b∈Icc 0 (L n))
      (hs : B≤a+b) : |futureKernel h (t n-L n) a b-q|≤2*η := by
    have hg := A.gram n a b ha hb
    have hc := hB (a+b) hs
    have ht := abs_sub_le (futureKernel h (t n-L n) a b) (c (a+b)) q
    linarith
  have hg1 := hgram ha ha (by linarith [hτ.2])
  have hg2 := hgram hLL hLL (by linarith)
  have hg3 := hgram ha hLL (by linarith [hτ.2])
  let w := prefixVector h (t n-L n) (t n-τ)
  let M := prefixVector h (t n-L n) (t n)
  have h1 : futureKernel h (t n-L n) (L n-τ) (L n-τ)=‖w‖^2 := by
    unfold futureKernel prefixKernel
    rw [show t n-L n+(L n-τ)=t n-τ by ring,real_inner_self_eq_norm_sq]
  have h2 : futureKernel h (t n-L n) (L n) (L n)=‖M‖^2 := by
    unfold futureKernel prefixKernel
    rw [sub_add_cancel,real_inner_self_eq_norm_sq]
  have h3 : futureKernel h (t n-L n) (L n-τ) (L n)=inner ℝ w M := by
    unfold futureKernel prefixKernel
    rw [show t n-L n+(L n-τ)=t n-τ by ring,sub_add_cancel]
  rw [h1] at hg1
  rw [h2] at hg2
  rw [h3] at hg3
  have hs : ‖w-M‖^2≤8*η := by
    rw [norm_sub_sq_real]
    have h1 := (abs_le.mp hg1).2
    have h2 := (abs_le.mp hg2).2
    have h3 := (abs_le.mp hg3).1
    linarith
  have hdist : ‖w-M‖≤ε/2 := by
    dsimp [η] at hs
    nlinarith [norm_nonneg (w-M)]
  have hUM : normalizedCenter h (t n) (L n)=unitize M := by
    unfold normalizedCenter localCenter
    rw [sub_add_cancel]
  have hMpos : 0<‖M‖ := by
    simpa only [localCenter,sub_add_cancel] using A.center_positive n
  have hrecover : ‖M‖ • normalizedCenter h (t n) (L n)=M := by
    rw [hUM,unitize,smul_smul,mul_inv_cancel₀ hMpos.ne',one_smul]
  have hd : ‖M-Real.sqrt q • normalizedCenter h (t n) (L n)‖=
      |‖M‖-Real.sqrt q| := by
    have heq : M-Real.sqrt q • normalizedCenter h (t n) (L n)=
        (‖M‖-Real.sqrt q) • normalizedCenter h (t n) (L n) := by
      rw [sub_smul,hrecover]
    rw [heq,norm_smul,Real.norm_eq_abs,A.center_unit n,mul_one]
  have htri : ‖w-Real.sqrt q • normalizedCenter h (t n) (L n)‖≤
      ‖w-M‖+‖M-Real.sqrt q • normalizedCenter h (t n) (L n)‖ := by
    calc
      _ = ‖(w-M)+(M-Real.sqrt q • normalizedCenter h (t n) (L n))‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  rw [hd] at htri
  change ‖w-Real.sqrt q • normalizedCenter h (t n) (L n)‖≤ε
  change |‖M‖-Real.sqrt q|<ε/2 at hn
  linarith

theorem recent_centers_tendstoUniformlyOn {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q)
    {t L : ℕ → ℝ} (A : Receipt h c q t L) {W : ℝ} (hW : 0<W) :
    TendstoUniformlyOn (fun n τ => prefixVector h (t n-L n) (t n-τ)-
      Real.sqrt q • normalizedCenter h (t n) (L n)) (fun _ => 0) atTop (Icc 0 W) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [recent_centers_uniform H A hW (half_pos hε)] with n hn
  intro τ hτ
  have hh := hn τ hτ
  rw [dist_eq_norm,zero_sub,norm_neg]
  linarith

end SphericalAging.SusceptibilityRecentCenters
