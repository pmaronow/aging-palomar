module

public import SphericalAging.ForwardQuotients
public import SphericalAging.StationaryPrefixConsequences

public section

/-! Remote later-coordinate derivatives of the actual CK solution for every p ≥ 3.
The proof uses genuine strong tree derivatives, reflected Gram convergence and Taylor's theorem. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped Topology InnerProductSpace
open Set Filter
namespace SphericalAging.RemoteForwardDerivative
open CKSpecification CausalTree CausalTreeRealization ProjectedTreeDrift
  PrefixReflection PrefixRectangleStability ForwardQuotients

@[expose] def projectedQuotient {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (T L η : ℝ) : Space (p-1) :=
  η⁻¹ • (prefixVector h T (T+L+η)-prefixVector h T (T+L))

/-- Reflection determines the actual squared norm of each forward quotient. -/
theorem quotient_norm_sq_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {ι : Type} {F : Filter ι} {T : ι → ℝ}
    {c : ℝ → ℝ} {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η)
    (hQ : TendstoUniformlyOn (fun n => Function.uncurry (futureKernel h (T n)))
      (fun z => c (z.1+z.2)) F (square (L+η))) :
    Tendsto (fun n => ‖projectedQuotient h (T n) L η‖^2) F
      (nhds ((c (2*L+2*η)-2*c (2*L+η)+c (2*L))/η^2)) := by
  have hA : 0 ≤ L+η := by linarith
  have h11 := hQ.tendsto_at (x := (L+η,L+η)) ⟨⟨hA,le_rfl⟩,⟨hA,le_rfl⟩⟩
  have h10 := hQ.tendsto_at (x := (L+η,L)) ⟨⟨hA,le_rfl⟩,⟨hL,by linarith⟩⟩
  have h00 := hQ.tendsto_at (x := (L,L)) ⟨⟨hL,by linarith⟩,⟨hL,by linarith⟩⟩
  have hl := ((h11.sub (h10.const_mul 2)).add h00).div_const (η^2)
  convert hl using 1
  · ext n
    unfold projectedQuotient
    rw [norm_smul, mul_pow, norm_sub_sq_real]
    simp only [Real.norm_eq_abs, abs_inv, abs_of_pos hη, ← real_inner_self_eq_norm_sq]
    change (η⁻¹)^2*(_-2*_+_) = _
    simp only [Function.uncurry_apply_pair, futureKernel, prefixKernel,
      show T n+(L+η)=T n+L+η from by ring]
    field_simp
  · congr 1 <;> ring

/-- A scalar CK later derivative is exactly the pairing with the actual
strong projected derivative whenever the earlier time lies in the prefix. -/
theorem correlationSlope_eq_projected_inner {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T t s : ℝ}
    (hT : 0 ≤ T) (ht : T < t) (hs : 0 ≤ s) (hsT : s ≤ T) :
    correlationSlope p β d t s =
      inner ℝ (projectedDerivative h T t) (ckTreeState h s) := by
  have hd := (projectedTree_hasDerivAt h hb hT ht).inner ℝ
    (hasDerivAt_const t (ckTreeState h s))
  simp only [inner_zero_right, zero_add] at hd
  have he : (fun x => inner ℝ (timePrefix T (ckTreeState h x)) (ckTreeState h s))
      =ᶠ[nhds t] (fun x => d.C x s) := by
    filter_upwards [Ioi_mem_nhds (hT.trans_lt ht)] with x hx
    rw [timePrefix_selfAdjoint, ckTreeState_timePrefix h hb hs hsT,
      ckTreeState_gram h hb hx.le hs]
  have hc := (h.correlation_derivative t s hs (hsT.trans ht.le)).hasDerivAt
    (Ici_mem_nhds (hsT.trans_lt ht))
  exact hc.unique (hd.congr_of_eventuallyEq he.symm)

theorem correlationSlope_abs_le_projected_norm {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T t s : ℝ}
    (hT : 0 ≤ T) (ht : T < t) (hs : 0 ≤ s) (hsT : s ≤ T) :
    |correlationSlope p β d t s| ≤ ‖projectedDerivative h T t‖ := by
  rw [correlationSlope_eq_projected_inner h hb hT ht hs hsT]
  simpa [ckTreeState_norm h hb hs] using
    abs_real_inner_le_norm (projectedDerivative h T t) (ckTreeState h s)

/-- The remote projected-derivative bound along any reflected stationary cluster.
Its uniform eventual form is the precise limsup bound, and it is independent of p. -/
theorem projected_remote_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {ι : Type} {F : Filter ι}
    {T : ι → ℝ} (hT : ∀ᶠ n in F, 0 ≤ T n) {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ 2 c (Ioi 0))
    (hQ : ∀ A : ℝ, 0 ≤ A →
      TendstoUniformlyOn (fun n => Function.uncurry (futureKernel h (T n)))
        (fun z => c (z.1+z.2)) F (square A))
    {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in F, ‖projectedDerivative h (T n) (T n+L)‖ ≤
      Real.sqrt (iteratedDeriv 2 c (2*L))+ε := by
  have hsecond := second_quotient_tendsto hc (by positivity : 0 < 2*L)
  have hzero : Tendsto (fun η : ℝ => Real.sqrt η) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hr := (hzero.const_mul (driftHolder p β)).add hsecond.sqrt
  simp only [mul_zero, zero_add] at hr
  have hs : ∀ᶠ η : ℝ in nhdsWithin 0 (Ioi 0),
      driftHolder p β*Real.sqrt η+
        Real.sqrt ((c (2*L+2*η)-2*c (2*L+η)+c (2*L))/η^2)
          < Real.sqrt (iteratedDeriv 2 c (2*L))+ε/2 := by
    apply hr.eventually (gt_mem_nhds (by linarith))
  obtain ⟨η,hη,hsmall⟩ := (eventually_mem_nhdsWithin.and hs).exists
  have hη' : 0 < η := hη
  have hnormsq := quotient_norm_sq_tendsto h hL.le hη' (hQ (L+η) (by positivity))
  have hnorm : Tendsto (fun n => ‖projectedQuotient h (T n) L η‖) F
      (nhds (Real.sqrt ((c (2*L+2*η)-2*c (2*L+η)+c (2*L))/η^2))) := by
    simpa only [Real.sqrt_sq (norm_nonneg _)] using hnormsq.sqrt
  have hnear := hnorm.eventually (gt_mem_nhds (by linarith :
    Real.sqrt ((c (2*L+2*η)-2*c (2*L+η)+c (2*L))/η^2) <
      Real.sqrt ((c (2*L+2*η)-2*c (2*L+η)+c (2*L))/η^2)+ε/2))
  filter_upwards [hT,hnear] with n hn hnear
  have he := projected_quotient_error h hb hn (by linarith : T n < T n+L) hη'
  change ‖projectedQuotient h (T n) L η-projectedDerivative h (T n) (T n+L)‖ ≤ _ at he
  have ht : ‖projectedDerivative h (T n) (T n+L)‖ ≤
      ‖projectedQuotient h (T n) L η‖+
        ‖projectedDerivative h (T n) (T n+L)-projectedQuotient h (T n) L η‖ :=
    norm_le_norm_add_norm_sub' _ _
  rw [norm_sub_rev] at he
  linarith

/-- Source remote-forward inequality in uniform eventual form, valid for EVERY p ≥ 3.
The only stationary inputs are reflected Gram convergence and ordinary C² regularity. -/
theorem remote_forward_derivative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {ι : Type} {F : Filter ι}
    {T : ι → ℝ} (hT : ∀ᶠ n in F, 0 ≤ T n) {c : ℝ → ℝ}
    (hc : ContDiffOn ℝ 2 c (Ioi 0))
    (hQ : ∀ A : ℝ, 0 ≤ A →
      TendstoUniformlyOn (fun n => Function.uncurry (futureKernel h (T n)))
        (fun z => c (z.1+z.2)) F (square A))
    {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in F, ∀ s : ℝ, 0 ≤ s → s ≤ T n →
      |correlationSlope p β d (T n+L) s| ≤ Real.sqrt (iteratedDeriv 2 c (2*L))+ε := by
  filter_upwards [hT,projected_remote_bound h hb hT hc hQ hL hε] with n hn hbnd
  intro s hs hsT
  exact (correlationSlope_abs_le_projected_norm h hb hn (by linarith) hs hsT).trans hbnd

end SphericalAging.RemoteForwardDerivative
