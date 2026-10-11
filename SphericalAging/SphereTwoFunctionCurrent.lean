module

public import SphericalAging.SphereProductCurrentAlgebra
public import SphericalAging.SphereSpatialSliceFDT

public section

/-! Exact density current of two backward semigroup slices. The backward
equation is used only on the physical sphere; spatial C² and joint jets
suffice for differentiation under the compact spherical integral. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace SphericalAging.SphereTwoFunctionCurrent
open MeasureTheory Set Filter
open scoped Topology
open FiniteModel SphereInitialLaw SphericalIntegrationByParts SphereEntropyDissipation HardSphereDynamics
open SphereGeneratorIntegrationByParts SphereGeneratorAlgebra SphereForwardAdjoint
open SphereProductCurrentAlgebra

theorem product_pairing_hasDerivAt {N p : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N)
    (hA : ∀i,star (A i)=-A i) {ρ ρdot m n : ℝ→Vector N→ℝ}
    (hρ : ContDiff ℝ 2 (Function.uncurry ρ))
    (hdot : Continuous (Function.uncurry ρdot))
    (hderiv : ∀v x,HasDerivAt (fun w => ρ w x) (ρdot v x) v)
    (hm : Continuous (Function.uncurry m)) (hslices : ∀v,ContDiff ℝ 2 (m v))
    (hgen : Continuous (fun z : ℝ×Vector N => rotationGenerator κ β J A (m z.1) z.2))
    (hback : ∀v,0<v→∀x,OnSphere x→HasDerivAt (fun w => m w x)
      (rotationGenerator κ β J A (m v) x) v)
    (hn : Continuous (Function.uncurry n)) (hnslices : ∀v,ContDiff ℝ 2 (n v))
    (hngen : Continuous (fun w : ℝ×Vector N => rotationGenerator κ β J A (n w.1) w.2))
    (hnback : ∀v,0<v→∀x,OnSphere x→HasDerivAt (fun w => n w x)
      (rotationGenerator κ β J A (n v) x) v)
    (T a d z : ℝ) (ha : z<a) (hd : 0<d+z)
    (hpos : ∀x,0<ρ (T+z) x)
    (hPDE : ∀x,OnSphere x→ρdot (T+z) x=forwardDensitySlope κ β J A (ρ (T+z)) x) :
    HasDerivAt (fun v => ∫x : Vector N,ρ (T+v) x*m (a-v) x*n (d+v) x ∂sphereLaw N)
      (-2*(∫x : Vector N,ρ (T+z) x*m (a-z) x*
        rotationGamma κ A (relativeLog β J (ρ (T+z))) (n (d+z)) x ∂sphereLaw N)) z := by
  let δ := min (a-z) (d+z)/2
  have hδ : 0<δ := by dsimp only [δ];exact div_pos (lt_min (sub_pos.mpr ha) hd) (by norm_num)
  let F (v : ℝ) (x : Vector N) := ρ (T+v) x*m (a-v) x*n (d+v) x
  let F' (v : ℝ) (x : Vector N) := ρdot (T+v) x*m (a-v) x*n (d+v) x-
    ρ (T+v) x*rotationGenerator κ β J A (m (a-v)) x*n (d+v) x+
      ρ (T+v) x*m (a-v) x*rotationGenerator κ β J A (n (d+v)) x
  have htc : Continuous (fun w : ℝ×Vector N => (T+w.1,w.2)) :=
    (continuous_const.add continuous_fst).prodMk continuous_snd
  have hac : Continuous (fun w : ℝ×Vector N => (a-w.1,w.2)) :=
    (continuous_const.sub continuous_fst).prodMk continuous_snd
  have hdc : Continuous (fun w : ℝ×Vector N => (d+w.1,w.2)) :=
    (continuous_const.add continuous_fst).prodMk continuous_snd
  have hFc : Continuous (Function.uncurry F) :=
    ((hρ.continuous.comp htc).mul (hm.comp hac)).mul (hn.comp hdc)
  have hF'c : Continuous (Function.uncurry F') :=
    (((hdot.comp htc).mul (hm.comp hac)).mul (hn.comp hdc)).sub
      (((hρ.continuous.comp htc).mul (hgen.comp hac)).mul (hn.comp hdc)) |>.add
        (((hρ.continuous.comp htc).mul (hm.comp hac)).mul (hngen.comp hdc))
  have hD v (hv : v∈Icc (z-δ) (z+δ)) (x : Vector N) (hx : OnSphere x) :
      HasDerivAt (fun w => F w x) (F' v x) v := by
    have hδa : δ≤(a-z)/2 := by dsimp only [δ];exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hδd : δ≤(d+z)/2 := by dsimp only [δ];exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    have hav : 0<a-v := by linarith [hv.2]
    have hdv : 0<d+v := by linarith [hv.1]
    have hρv := (hderiv (T+v) x).comp v ((hasDerivAt_const v T).add (hasDerivAt_id v))
    have ham := (hback (a-v) hav x hx).comp v ((hasDerivAt_const v a).sub (hasDerivAt_id v))
    have hdm := (hnback (d+v) hdv x hx).comp v ((hasDerivAt_const v d).add (hasDerivAt_id v))
    convert (hρv.mul ham).mul hdm using 1
    · rfl
    · dsimp only [F',Function.comp_def,Pi.mul_apply]
      ring
  obtain ⟨K,hK⟩ := ((isCompact_Icc : IsCompact (Icc (z-δ) (z+δ))).prod
      (isCompact_closedBall (0 : Vector N) (Real.sqrt N))).bddAbove_image hF'c.norm.continuousOn
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=sphereLaw N) (F:=F) (F':=F') (bound:=fun _ => K) (x₀:=z) (s:=Icc (z-δ) (z+δ))
    (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall (fun v => (hFc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable))
    (continuous_sphere_integrable hN (hFc.comp (continuous_const.prodMk continuous_id)))
    (hF'c.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (by
      filter_upwards [sphereLaw_norm_ae hN] with x hx v hv
      exact hK ⟨(v,x),⟨hv,by simp only [Metric.mem_closedBall,dist_zero_right,hx,le_refl]⟩,rfl⟩)
    (integrable_const K) (by
      filter_upwards [sphereLaw_support hN] with x hx
      intro v hv
      exact hD v hv x ((onSphere_iff_norm_sq x).mpr hx))
  have hρs : ContDiff ℝ 2 (ρ (T+z)) := by
    simpa only [Function.comp_def,Function.uncurry,id_eq] using
      hρ.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : Vector N => (T+z,x)))
  have he : (∫x : Vector N,F' z x ∂sphereLaw N)=
      -2*(∫x : Vector N,ρ (T+z) x*m (a-z) x*
        rotationGamma κ A (relativeLog β J (ρ (T+z))) (n (d+z)) x ∂sphereLaw N) := by
    rw [←product_current_identity hN κ β J A hA hρs hpos (hslices (a-z)) (hnslices (d+z))]
    apply integral_congr_ae
    filter_upwards [sphereLaw_support hN] with x hx
    dsimp only [F']
    rw [hPDE x ((onSphere_iff_norm_sq x).mpr hx)]
  rw [he] at hh
  exact hh.2

end SphericalAging.SphereTwoFunctionCurrent
