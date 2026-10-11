module

public import SphericalAging.SpaceTimeTaylorPartition

public section

/-! Actual time increments along continuous state paths converge to the
integral of the observed time slope. Only C¹ time regularity is used, and
the derivative is needed on the open physical time interval. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.SpaceTimeDerivativeRiemann
open HardSphereDynamics LocalSDE
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

@[expose] def timeApprox (f : ℝ → State N → ℝ) (g : ℝ → State N) (T : ℝ≥0) (n : ℕ) : ℝ :=
  ∑ i∈Finset.range n,
    (f (uniformPartitionTime T n (i+1)) (g (uniformPartitionTime T n (i+1)))-
      f (uniformPartitionTime T n i) (g (uniformPartitionTime T n (i+1))))

/-- Genuine deterministic time FTC and compact uniform continuity imply
the time-part limit in the space-time Itô partition identity. The spatial
state is sampled at right endpoints; its observed slope converges uniformly
over the increasingly fine time cells. -/
theorem timeApprox_tendsto (f fdot : ℝ → State N → ℝ) (g : ℝ → State N) (T : ℝ≥0)
    (hfc : ∀ r∈Icc (0 : ℝ) T,ContinuousOn (fun s => f s (g r)) (Icc 0 T))
    (hfd : ∀ r∈Icc (0 : ℝ) T,∀ s∈Ioo (0 : ℝ) T,HasDerivAt (fun u => f u (g r)) (fdot s (g r)) s)
    (hdc : ContinuousOn (fun q : ℝ × ℝ => fdot q.1 (g q.2))
      (Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) T)) :
    Tendsto (fun n => timeApprox f g T (n+1)) atTop
      (𝓝 (∫ s in (0 : ℝ)..(T : ℝ),fdot s (g s))) := by
  by_cases hT : T=0
  · subst T
    have he : (fun n => timeApprox f g 0 (n+1))=(fun _ : ℕ => (0 : ℝ)) := by
      funext n
      simp [timeApprox,uniformPartitionTime]
    simpa only [he,NNReal.coe_zero,intervalIntegral.integral_same] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hTp : 0<(T : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hT)
  have hdiag : ContinuousOn (fun s => fdot s (g s)) (Icc (0 : ℝ) T) :=
    hdc.comp (continuous_id.prodMk continuous_id).continuousOn (fun s hs => ⟨hs,hs⟩)
  have hfixed (r : ℝ) (hr : r∈Icc (0 : ℝ) T) :
      ContinuousOn (fun s => fdot s (g r)) (Icc (0 : ℝ) T) :=
    hdc.comp (continuous_id.prodMk continuous_const).continuousOn (fun s hs => ⟨hs,hr⟩)
  let τ (n i : ℕ) : ℝ := uniformPartitionTime T (n+1) i
  have hτ (n i : ℕ) (hi : i≤n+1) : τ n i∈Icc (0 : ℝ) T := by
    have he := uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n) hi
    constructor
    · exact NNReal.coe_nonneg _
    · exact_mod_cast he.2
  have hτ0 (n : ℕ) : τ n 0=0 := by simp [τ,uniformPartitionTime]
  have hτT (n : ℕ) : τ n (n+1)=(T : ℝ) := by
    dsimp only [τ,uniformPartitionTime]
    push_cast
    field_simp
  have hmono (n i : ℕ) : τ n i≤τ n (i+1) := by
    exact_mod_cast monotone_uniformPartitionTime_general T (n+1) (Nat.le_succ i)
  have hstep (n i : ℕ) : τ n (i+1)-τ n i=(T : ℝ)/(n+1 : ℕ) := by
    dsimp only [τ,uniformPartitionTime]
    push_cast
    ring
  have hsub (n i : ℕ) (hi : i<n+1) : Icc (τ n i) (τ n (i+1))⊆Icc (0 : ℝ) T := by
    intro s hs
    exact ⟨(hτ n i ((Nat.le_succ i).trans hi)).1.trans hs.1,
      hs.2.trans (hτ n (i+1) hi).2⟩
  have hfcell (n i : ℕ) (hi : i<n+1) :
      f (τ n (i+1)) (g (τ n (i+1)))-f (τ n i) (g (τ n (i+1)))=
        ∫ s in τ n i..τ n (i+1),fdot s (g (τ n (i+1))) := by
    symm
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (hmono n i)
      ((hfc _ (hτ n (i+1) hi)).mono (hsub n i hi))
    · intro s hs
      apply hfd _ (hτ n (i+1) hi)
      exact ⟨lt_of_le_of_lt (hτ n i ((Nat.le_succ i).trans hi)).1 hs.1,
        lt_of_lt_of_le hs.2 (hτ n (i+1) hi).2⟩
    · exact ((hfixed _ (hτ n (i+1) hi)).mono (hsub n i hi)).intervalIntegrable_of_Icc (hmono n i)
  have hdiagcell (n i : ℕ) (hi : i<n+1) :
      IntervalIntegrable (fun s => fdot s (g s)) volume (τ n i) (τ n (i+1)) :=
    (hdiag.mono (hsub n i hi)).intervalIntegrable_of_Icc (hmono n i)
  have herror (n : ℕ) : timeApprox f g T (n+1)-
      (∫ s in (0 : ℝ)..(T : ℝ),fdot s (g s))=
        ∑ i∈Finset.range (n+1),∫ s in τ n i..τ n (i+1),
          fdot s (g (τ n (i+1)))-fdot s (g s) := by
    have hi := intervalIntegral.sum_integral_adjacent_intervals (a := τ n)
      (n := n+1) (fun i hi => hdiagcell n i hi)
    rw [hτ0,hτT] at hi
    rw [← hi]
    unfold timeApprox
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_sub
      (((hfixed _ (hτ n (i+1) (Finset.mem_range.mp hi))).mono (hsub n i (Finset.mem_range.mp hi))).intervalIntegrable_of_Icc (hmono n i))
      (hdiagcell n i (Finset.mem_range.mp hi))]
    exact congrArg (fun z => z-(∫ s in τ n i..τ n (i+1),fdot s (g s)))
      (hfcell n i (Finset.mem_range.mp hi))
  have huc := ((isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).prod isCompact_Icc).uniformContinuousOn_of_continuous hdc
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ := ε/(2*(T : ℝ))
  have hδ : 0<δ := div_pos hε (mul_pos (by norm_num) hTp)
  obtain ⟨η,hη,hm⟩ := (Metric.uniformContinuousOn_iff (α := ℝ × ℝ) (β := ℝ)).mp huc δ hδ
  have hmesh : Tendsto (fun n : ℕ => (T : ℝ)/(n+1 : ℕ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat (T : ℝ))
  obtain ⟨m,hm'⟩ := eventually_atTop.mp (hmesh.eventually (eventually_lt_nhds hη))
  refine ⟨m,fun n hn => ?_⟩
  rw [Real.dist_eq,herror]
  have hib (i : ℕ) (hi : i<n+1) :
      ‖∫ s in τ n i..τ n (i+1),fdot s (g (τ n (i+1)))-fdot s (g s)‖≤
        δ*(τ n (i+1)-τ n i) := by
    have hl := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := τ n i) (b := τ n (i+1)) (C := δ) (f := fun s => fdot s (g (τ n (i+1)))-fdot s (g s)) ?_
    · simpa only [abs_of_nonneg (sub_nonneg.mpr (hmono n i)),mul_comm] using hl
    · intro s hs
      have hs' : s∈Icc (τ n i) (τ n (i+1)) := by
        rw [uIoc_of_le (hmono n i)] at hs
        exact ⟨hs.1.le,hs.2⟩
      have hsT := hsub n i hi hs'
      have hdist : dist (s,τ n (i+1)) (s,s)<η := by
        simp only [Prod.dist_eq,dist_self,max_eq_right dist_nonneg,Real.dist_eq,
          abs_of_nonneg (sub_nonneg.mpr hs'.2)]
        rw [max_eq_right (sub_nonneg.mpr hs'.2)]
        calc
          τ n (i+1)-s≤τ n (i+1)-τ n i := sub_le_sub_left hs'.1 _
          _=(T : ℝ)/(n+1 : ℕ) := hstep n i
          _<η := hm' n hn
      have hh := hm _ ⟨hsT,hτ n (i+1) hi⟩ _ ⟨hsT,hsT⟩ hdist
      simpa only [Real.dist_eq,Real.norm_eq_abs] using hh.le
  have hsum : (∑ i∈Finset.range (n+1),δ*(τ n (i+1)-τ n i))=δ*(T : ℝ) := by
    rw [← Finset.mul_sum,Finset.sum_range_sub,hτT,hτ0,sub_zero]
  calc
    _=‖∑ i∈Finset.range (n+1),∫ s in τ n i..τ n (i+1),fdot s (g (τ n (i+1)))-fdot s (g s)‖ := by rw [Real.norm_eq_abs]
    _≤∑ i∈Finset.range (n+1),‖∫ s in τ n i..τ n (i+1),fdot s (g (τ n (i+1)))-fdot s (g s)‖ := norm_sum_le _ _
    _≤∑ i∈Finset.range (n+1),δ*(τ n (i+1)-τ n i) := Finset.sum_le_sum (fun i hi => hib i (Finset.mem_range.mp hi))
    _=δ*(T : ℝ) := hsum
    _<ε := by dsimp only [δ];field_simp;linarith

end SphericalAging.SpaceTimeDerivativeRiemann
