module

public import SphericalAging.PhysicalForkDiagonalOverlap
public import SphericalAging.FiniteScalarAverageMoments

public section

/-! The genuine fork mean's overlap with a branch's earlier state is an
average of the actual diagonal and distinct-branch overlaps. This derives
the source10.4 last-window mixed overlap, without a center-overlap premise. -/
noncomputable section
set_option maxHeartbeats 1900000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.PhysicalForkOverlapAggregation
open MeasureTheory ProbabilityTheory Filter Set FiniteModel HardSphereDynamics
open PhysicalForkConstruction PhysicalForkOverlapLaw PhysicalForkDiagonalOverlap WienerForkTransfer
open FiniteScalarAverageMoments ForkParameterBounds AnnealedHamiltonianEnergyStein
open CKSpecification StationaryClusterInputs ActualForkMeanBridge SphereFisherHelly ActualSphereForkEndpoints
open scoped NNReal ENNReal Topology InnerProductSpace BigOperators
variable {N p K : ℕ}

@[expose] def pairOverlap (β : ℝ) (T L v : ℝ≥0) (b k : Fin K) (z : ForkSpace N p K) : ℝ :=
  ⟪branch β (T+L) T k z,branch β (T+v) T b z⟫_ℝ/(N:ℝ)

@[expose] def meanOverlap (β : ℝ) (T L v : ℝ≥0) (b : Fin K) (z : ForkSpace N p K) : ℝ :=
  ⟪mean (branch β (T+L) T) z,branch β (T+v) T b z⟫_ℝ/(N:ℝ)

@[expose] def pairTarget (c : ℝ→ℝ) (L v : ℝ) (b k : Fin K) : ℝ :=
  if k=b then c (L-v) else c (L+v)

lemma meanOverlap_eq_average (β : ℝ) (T L v : ℝ≥0) (b : Fin K) (z : ForkSpace N p K) :
    meanOverlap β T L v b z=(K:ℝ)⁻¹*∑k,pairOverlap β T L v b k z := by
  simp only [meanOverlap,mean,pairOverlap,real_inner_smul_left,sum_inner]
  rw [←Finset.sum_div]
  ring

lemma pairTarget_average (hK : 0<K) (c : ℝ→ℝ) (L v : ℝ) (b : Fin K) :
    (K:ℝ)⁻¹*∑k : Fin K,pairTarget c L v b k=mixedOverlap c K L (L-v) := by
  have he : (fun k : Fin K => pairTarget c L v b k)=
      (fun k => c (L+v)+(if k=b then c (L-v)-c (L+v) else 0)) := by
    funext k
    unfold pairTarget
    split_ifs <;> ring
  have hs : (∑k : Fin K,pairTarget c L v b k)=c (L-v)+((K:ℝ)-1)*c (L+v) := by
    rw [he]
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    simp
    ring
  rw [hs,mixedOverlap]
  have he : 2*L-(L-v)=L+v := by ring
  rw [he,div_eq_mul_inv]
  ring

lemma meanOverlap_error_eq_average (hK : 0<K) (β : ℝ) (T L v : ℝ≥0)
    (b : Fin K) (c : ℝ→ℝ) (z : ForkSpace N p K) :
    meanOverlap β T L v b z-mixedOverlap c K L ((L:ℝ)-(v:ℝ))=
      (K:ℝ)⁻¹*∑k,(pairOverlap β T L v b k z-pairTarget c L v b k) := by
  rw [meanOverlap_eq_average,←pairTarget_average hK c (L:ℝ) (v:ℝ) b,Finset.sum_sub_distrib]
  ring

lemma pairOverlap_memLp (hN : 0<N) (β : ℝ) (T L v : ℝ≥0) (b k : Fin K) :
    MemLp (pairOverlap (N:=N) (p:=p) β T L v b k) 2 (forkLaw N p K) := by
  have hY := fork_joint_law (N:=N) (p:=p) (K:=K) β (T+L) T
  have hZ := fork_joint_law (N:=N) (p:=p) (K:=K) β (T+v) T
  have hm := ((branch_memLp hY k).aestronglyMeasurable.inner
    (branch_memLp hZ b).aestronglyMeasurable).mul_const (N:ℝ)⁻¹
  have hm' : AEStronglyMeasurable (pairOverlap (N:=N) (p:=p) β T L v b k) (forkLaw N p K) := by
    change AEStronglyMeasurable (fun z => ⟪branch β (T+L) T k z,branch β (T+v) T b z⟫_ℝ/(N:ℝ)) _
    simpa only [div_eq_mul_inv] using hm
  apply MemLp.of_bound hm' 1
  filter_upwards [branch_norm_sq hY k,branch_norm_sq hZ b] with z hy hz
  rw [Real.norm_eq_abs]
  exact FiniteCorrelationIto.overlap_abs_le_one hN
    ((onSphere_iff_norm_sq _).mpr hy) ((onSphere_iff_norm_sq _).mpr hz)

/-- No branch independence is required to bound the mean's overlap
error by a common diagonal/offdiagonal second-moment bound. -/
theorem meanOverlap_error_le (hN : 0<N) (hK : 0<K) (β : ℝ) (T L v : ℝ≥0)
    (b : Fin K) (c : ℝ→ℝ) (B : ℝ)
    (hB : ∀k : Fin K,(∫z,(pairOverlap (N:=N) (p:=p) β T L v b k z-
      pairTarget c L v b k)^2 ∂forkLaw N p K)≤B) :
    (∫z,(meanOverlap (N:=N) (p:=p) β T L v b z-
      mixedOverlap c K L ((L:ℝ)-(v:ℝ)))^2 ∂forkLaw N p K)≤B := by
  have hh := average_centered_secondMoment_le hK
    (fun k z => pairOverlap (N:=N) (p:=p) β T L v b k z-pairTarget c L v b k) 0 B
    (fun k => (pairOverlap_memLp hN β T L v b k).sub (memLp_const _))
    (fun k => by simpa only [sub_zero] using hB k)
  simpa only [←meanOverlap_error_eq_average hK β T L v b c,sub_zero] using hh.2

/-- The source10.4 Step4 same-branch and mean-branch errors vanish
uniformly on the last-L window in the literal ordered limit. -/
theorem actual_late_overlap_ordered_uniform {p K : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j) (hTop : Tendsto dim atTop atTop)
    (E : ∀j,FisherDensity (dim j) p β)
    (hLaw : ∀j,WaitingDensityLaw β (dim j+1) (modelRadius_pos (dim j)) (E j))
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|(E j).full w-f w|) atTop (𝓝 0))
    (hK : 0<K) (L : ℝ≥0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠn in atTop,∀ᶠj in atTop,∀v∈Icc (0:ℝ) L,∀b : Fin K,
      (∫z : ForkSpace (dim j) p K,
        (pairOverlap β (T n).toNNReal L v.toNNReal b b z-c ((L:ℝ)-v))^2
          ∂forkLaw (dim j) p K)+
      (∫z : ForkSpace (dim j) p K,
        (meanOverlap β (T n).toNNReal L v.toNNReal b z-
          mixedOverlap c K L ((L:ℝ)-v))^2 ∂forkLaw (dim j) p K)<ε := by
  have hd := same_branch_ordered_uniform_L2 H hT dim hTop hbridge L
    (show 0<ε/4 by positivity) K
  have ho := physical_branch_ordered_uniform_L2 H hT dim hDim hTop E hLaw hbridge
    hi hn hL1 L.coe_nonneg (show 0<ε/4 by positivity) K
  filter_upwards [hd,ho] with n hnd hno
  filter_upwards [hnd,hno] with j hjd hjo
  intro v hv b
  have hpair (k : Fin K) : (∫z : ForkSpace (dim j) p K,
      (pairOverlap β (T n).toNNReal L v.toNNReal b k z-
        pairTarget c L v.toNNReal b k)^2 ∂forkLaw (dim j) p K)≤ε/4 := by
    by_cases hkb : k=b
    · subst k
      simpa only [pairOverlap,pairTarget,ite_true,Real.coe_toNNReal _ hv.1] using (hjd v hv b).le
    · have hLmem : (L:ℝ)∈Icc (0:ℝ) L := ⟨L.coe_nonneg,le_rfl⟩
      simpa only [pairOverlap,pairTarget,if_neg hkb,Real.coe_toNNReal _ hv.1,Real.toNNReal_coe] using
        (hjo L hLmem v hv k b hkb).le
  have hmean := meanOverlap_error_le (N:=dim j) (p:=p) (by have hx:=hDim j;omega)
    hK β (T n).toNNReal L v.toNNReal b c (ε/4) hpair
  rw [Real.coe_toNNReal _ hv.1] at hmean
  have hdiag := hjd v hv b
  change (∫z : ForkSpace (dim j) p K,
    (pairOverlap β (T n).toNNReal L v.toNNReal b b z-c ((L:ℝ)-v))^2
      ∂forkLaw (dim j) p K)<ε/4 at hdiag
  linarith

end SphericalAging.PhysicalForkOverlapAggregation
