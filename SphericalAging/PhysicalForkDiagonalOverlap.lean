module

public import SphericalAging.PhysicalForkOverlapLaw
public import SphericalAging.ActualOverlapConcentration

public section

/-! Actual same-branch concentration on the late fork window, derived
from the full-model O(1/N) variance and the preceding CK mean bridge. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.PhysicalForkDiagonalOverlap
open MeasureTheory ProbabilityTheory Filter Set FiniteModel HardSphereDynamics
open PhysicalForkConstruction ActualModelOverlapVariance ActualBackgroundOverlapLaw
open ActualOverlapConcentration ActualCompactJointOverlapVariance AnnealedHamiltonianEnergyStein
open CKSpecification StationaryClusterInputs ActualForkMeanBridge PrefixRectangleStability
open scoped NNReal ENNReal Topology InnerProductSpace
variable {N p K : ℕ}

lemma integral_square_bias_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω→ℝ} (hf : MemLp f 2 μ) (a : ℝ) :
    (∫ω,(f ω-a)^2 ∂μ)≤
      2*(∫ω,(f ω-(∫z,f z ∂μ))^2 ∂μ)+2*((∫z,f z ∂μ)-a)^2 := by
  let m := ∫z,f z ∂μ
  have hi (b : ℝ) : Integrable (fun ω => (f ω-b)^2) μ := by
    simpa only [Pi.sub_apply,Real.norm_eq_abs,sq_abs] using (hf.sub (memLp_const b)).integrable_norm_pow'
  have hp (ω : Ω) : (f ω-a)^2≤2*(f ω-m)^2+2*(m-a)^2 := by
    nlinarith [sq_nonneg (f ω-m-(m-a))]
  have hh := integral_mono (hi a) (((hi m).const_mul 2).add (integrable_const (2*(m-a)^2))) hp
  change (∫ω,(f ω-a)^2 ∂μ)≤∫ω,2*(f ω-m)^2+2*(m-a)^2 ∂μ at hh
  rw [integral_add ((hi m).const_mul 2) (integrable_const _),integral_const_mul] at hh
  simpa only [integral_const,probReal_univ,one_smul] using hh

/-- The literal two-time overlap of a whole physical branch has the
actual same-path model law, using the full spliced-path sampler. -/
theorem same_branch_centered_secondMoment (hN : 3≤N) (β : ℝ≥0)
    (T s t : ℝ≥0) (b : Fin K) (a : ℝ) :
    (∫z : WienerForkTransfer.ForkSpace N p K,
      (⟪branch β t T b z,branch β s T b z⟫_ℝ/(N:ℝ)-a)^2
        ∂WienerForkTransfer.forkLaw N p K)=
      ∫z,(actualOverlap (p:=p) β (N+1) (modelRadius_pos N) s t z-a)^2
        ∂AnnealedModelLaw.law N p := by
  have hφ := branchForward_measurePreserving (N:=N) (p:=p) T b
  have he := hφ.quasiMeasurePreserving.ae_eq_comp
    (actualOverlap_ae_joint (p:=p) β (N+1) (modelRadius_pos N) s t)
  calc
    _=∫z,((actualOverlap (p:=p) β (N+1) (modelRadius_pos N) s t
        (branchForward T b z))-a)^2 ∂WienerForkTransfer.forkLaw N p K := by
      apply integral_congr_ae
      filter_upwards [he] with z hz
      change (⟪jointEndpoint β t (branchForward T b z),jointEndpoint β s (branchForward T b z)⟫_ℝ/(N:ℝ)-a)^2=_
      simp only [Function.comp_def] at hz
      rw [hz]
      simp only [Function.comp_def,jointOverlap,FiniteCorrelationIto.overlap,jointEndpoint,real_inner_comm,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
    _=_ := hφ.hasLaw.integral_comp
      (((actualOverlap_memLp hN β (N+1) (modelRadius_pos N) (modelRadius_sq N) s t).sub
        (memLp_const a)).aestronglyMeasurable.pow 2)

/-- Uniform means on the entire last-L same-branch window follow from
the actual dimension limit and the translated stationary cluster. -/
theorem same_branch_mean_ordered_uniform {p : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d) {L : ℝ} (hL : 0≤L)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠn in atTop,∀ᶠj in atTop,∀v∈Icc 0 L,
      |ActualForkMeanBridge.actualMean (N:=dim j) (p:=p) β (dim j+1)
        (modelRadius_pos (dim j)) (T n+v) (T n+L)-c (L-v)|<ε := by
  have hc := Metric.tendstoUniformlyOn_iff.mp (H.correlation L hL) (ε/2) (by positivity)
  filter_upwards [hc] with n hn
  have hA : 0≤T n+L+1 := by linarith [hT n]
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hbridge (T n+L+1) hA)
    (ε/2) (by positivity)] with j hj
  intro v hv
  have hz : (v,L)∈square L := ⟨hv,⟨hL,le_rfl⟩⟩
  have hz' : (T n+v,T n+L)∈square (T n+L+1) :=
    ⟨⟨by linarith [hT n,hv.1],by linarith [hv.2]⟩,
      ⟨by linarith [hT n],by linarith⟩⟩
  have h1 := hj (T n+v,T n+L) hz'
  have h2 := hn (v,L) hz
  simp only [Real.dist_eq] at h1 h2
  rw [abs_sub_comm] at h1 h2
  have hab : |v-L|=L-v := by rw [abs_of_nonpos (sub_nonpos.mpr hv.2)];ring
  rw [hab] at h2
  have ht := abs_sub_le
    (ActualForkMeanBridge.actualMean (N:=dim j) (p:=p) β (dim j+1)
      (modelRadius_pos (dim j)) (T n+v) (T n+L)) (d.C (T n+v) (T n+L)) (c (L-v))
  linarith

/-- The actual diagonal overlap error tends to zero uniformly over the
last fork window, dimension first and then translated stationary time. -/
theorem same_branch_ordered_uniform_L2 {p : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hTop : Tendsto dim atTop atTop)
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d) (L : ℝ≥0)
    {ε : ℝ} (hε : 0<ε) (K : ℕ) :
    ∀ᶠn in atTop,∀ᶠj in atTop,∀v∈Icc (0:ℝ) L,∀b : Fin K,
      (∫z : WienerForkTransfer.ForkSpace (dim j) p K,
        (⟪branch β ((T n).toNNReal+L) (T n).toNNReal b z,
          branch β ((T n).toNNReal+v.toNNReal) (T n).toNNReal b z⟫_ℝ/(dim j:ℝ)
            -c ((L:ℝ)-v))^2 ∂WienerForkTransfer.forkLaw (dim j) p K)<ε := by
  have hm := same_branch_mean_ordered_uniform H hT dim hbridge L.coe_nonneg
    (show 0<Real.sqrt (ε/4) from Real.sqrt_pos.2 (by positivity))
  filter_upwards [hm] with n hn
  have hv : Tendsto (fun j => jointVarianceCeiling p β ((T n).toNNReal+L+1)/(dim j:ℝ))
      atTop (𝓝 0) := (tendsto_const_div_atTop_nhds_zero_nat
        (jointVarianceCeiling p β ((T n).toNNReal+L+1))).comp hTop
  filter_upwards [hn,hTop.eventually (eventually_ge_atTop 3),
    (tendsto_order.mp hv).2 (ε/4) (by positivity)] with j hj hdim hvar
  intro v hv b
  rw [same_branch_centered_secondMoment hdim β (T n).toNNReal
    ((T n).toNNReal+v.toNNReal) ((T n).toNNReal+L) b (c ((L:ℝ)-v))]
  have hs : v.toNNReal≤L := by exact_mod_cast (show (v.toNNReal:ℝ)≤(L:ℝ) by rw [Real.coe_toNNReal _ hv.1];exact hv.2)
  have hconc := actual_overlap_centered_secondMoment_le (p:=p) hdim (by have hp:=h.spin_ge_three;omega)
    β (dim j+1) (modelRadius_pos (dim j)) (modelRadius_sq (dim j))
    ((T n).toNNReal+v.toNNReal) ((T n).toNNReal+L) ((T n).toNNReal+L+1)
    (add_le_add le_rfl hs) (le_add_of_nonneg_right zero_le) (by positivity)
  have hb := integral_square_bias_le
    (actualOverlap_memLp (p:=p) hdim β (dim j+1) (modelRadius_pos (dim j)) (modelRadius_sq (dim j))
      ((T n).toNNReal+v.toNNReal) ((T n).toNNReal+L)) (c ((L:ℝ)-v))
  have htimes : (T n).toNNReal+v.toNNReal=(T n+v).toNNReal ∧
      (T n).toNNReal+L=(T n+(L:ℝ)).toNNReal := by
    constructor <;> apply NNReal.eq <;> simp only [NNReal.coe_add,Real.coe_toNNReal _ (hT n),
      Real.coe_toNNReal _ hv.1,Real.coe_toNNReal _ (by linarith [hT n,hv.1] : 0≤T n+v),
      Real.coe_toNNReal _ (by linarith [hT n,L.coe_nonneg] : 0≤T n+(L:ℝ))]
  have hmean := hj v hv
  change |(∫z,actualOverlap (p:=p) β (dim j+1) (modelRadius_pos (dim j))
    (T n+v).toNNReal (T n+(L:ℝ)).toNNReal z ∂AnnealedModelLaw.law (dim j) p)-c ((L:ℝ)-v)|<Real.sqrt (ε/4) at hmean
  rw [←htimes.1,←htimes.2] at hmean
  have hbias := (sq_lt_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mpr hmean
  rw [sq_abs,Real.sq_sqrt (by positivity : 0≤ε/4)] at hbias
  linarith

end SphericalAging.PhysicalForkDiagonalOverlap
