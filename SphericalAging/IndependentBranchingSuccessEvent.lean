module

public import SphericalAging.IndependentBranchingSuccess

public section

/-! Event form of the full-depth branching Jensen estimate, including a
genuine shared initial seed rather than an assumed joint success probability. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.IndependentBranchingSuccessEvent
open Set MeasureTheory IndependentBranchingSuccess ConditionalCloneSuccessJensen
open scoped BigOperators
variable {S G : Type} [MeasurableSpace S] [MeasurableSpace G]

@[expose] def event (K : ℕ) (update : ℕ→S→G→S) (B : Set S) :
    (d : ℕ)→Set (S×TreeSample G K d)
  | 0 => {z | z.1∈B}
  | d+1 => {z | ∀i,(update d z.1 (z.2 i).1,(z.2 i).2)∈event K update B d}

theorem event_measurable (K : ℕ) (update : ℕ→S→G→S)
    (hu : ∀d,Measurable (Function.uncurry (update d))) (B : Set S)
    (hB : MeasurableSet B) (d : ℕ) : MeasurableSet (event K update B d) := by
  induction d with
  | zero => exact hB.preimage measurable_fst
  | succ d ih =>
    change MeasurableSet {z : S×TreeSample G K (d+1) |
      ∀i,(update d z.1 (z.2 i).1,(z.2 i).2)∈event K update B d}
    have he : {z : S×TreeSample G K (d+1) |
      ∀i,(update d z.1 (z.2 i).1,(z.2 i).2)∈event K update B d} =
      ⋂i : Fin K,(fun z : S×TreeSample G K (d+1) =>
        (update d z.1 (z.2 i).1,(z.2 i).2))⁻¹' event K update B d := by ext z;simp
    rw [he]
    apply MeasurableSet.iInter
    intro i
    have hz : Measurable (fun z : S×TreeSample G K (d+1) => z.2 i) :=
      (measurable_pi_apply i).comp measurable_snd
    exact ih.preimage (((hu d).comp (measurable_fst.prodMk hz.fst)).prodMk hz.snd)

theorem score_eq_indicator (K : ℕ) (update : ℕ→S→G→S) (B : Set S) (d : ℕ) :
    Function.uncurry (score K update (B.indicator (fun _ => (1:ℝ))) d)=
      (event K update B d).indicator (fun _ => (1:ℝ)) := by
  classical
  induction d with
  | zero => funext z;simp only [Function.uncurry,score,event,mem_setOf_eq];rfl
  | succ d ih =>
    funext z
    change (∏i,score K update (B.indicator (fun _ => (1:ℝ))) d
      (update d z.1 (z.2 i).1) (z.2 i).2)=_
    have hp i := congrFun ih (update d z.1 (z.2 i).1,(z.2 i).2)
    simp only [Function.uncurry] at hp
    simp_rw [hp]
    by_cases hz : z∈event K update B (d+1)
    · have hall : ∀i,(update d z.1 (z.2 i).1,(z.2 i).2)∈event K update B d := hz
      simp [hall,hz]
    · have hn : ∃i,(update d z.1 (z.2 i).1,(z.2 i).2)∉event K update B d :=
        by simpa only [event,mem_setOf_eq,not_forall] using hz
      obtain ⟨i,hi⟩ := hn
      rw [Set.indicator_of_notMem hz]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Set.indicator_of_notMem hi])

theorem actual_tree_success_probability_lower (μ : Measure S) (ν : Measure G)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (K : ℕ)
    (update : ℕ→S→G→S) (hu : ∀d,Measurable (Function.uncurry (update d)))
    (B : Set S) (hB : MeasurableSet B) (d : ℕ) :
    (∫s,singleMean ν update (B.indicator (fun _ => (1:ℝ))) d s ∂μ)^(K^d)≤
      (μ.prod (treeLaw ν K d)).real (event K update B d) := by
  let f : S→ℝ := B.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hB
  have hb s : 0≤f s ∧ f s≤1 := by
    dsimp only [f]
    by_cases hs : s∈B <;> simp [hs]
  let m := singleMean ν update f d
  let b := treeMean ν K update f d
  have hmm : Measurable m := singleMean_measurable ν update hu f hf d
  have hbm : Measurable b :=
    (score_measurable K update hu f hf d).stronglyMeasurable.integral_prod_right'
      (ν:=treeLaw ν K d) |>.measurable
  have hmb s : 0≤m s ∧ m s≤1 := singleMean_bounds ν update hu f hf hb d s
  have hbb s : 0≤b s ∧ b s≤1 := treeMean_bounds ν K update hu f hf hb d s
  have hmI := bounded_integrable μ m hmm hmb
  have hmpI := bounded_integrable μ (fun s => (m s)^(K^d)) (hmm.pow_const _)
    (fun s => ⟨pow_nonneg (hmb s).1 _,pow_le_one₀ (hmb s).1 (hmb s).2⟩)
  have hbI := bounded_integrable μ b hbm hbb
  have hJ := (convexOn_pow (K^d)).map_integral_le (continuous_pow _).continuousOn
    isClosed_Ici (ae_of_all _ (fun s => (hmb s).1)) hmI hmpI
  have hI := integral_mono hmpI hbI (fun s => actual_tree_success_lower ν K update hu f hf hb d s)
  have hscoreI := bounded_integrable (μ.prod (treeLaw ν K d))
    (Function.uncurry (score K update f d)) (score_measurable K update hu f hf d)
    (fun z => score_bounds K update f hb d z.1 z.2)
  have hjoint := integral_prod (Function.uncurry (score K update f d)) hscoreI
  have he : (∫s,b s ∂μ)=(μ.prod (treeLaw ν K d)).real (event K update B d) := by
    change (∫s,∫z,Function.uncurry (score K update f d) (s,z) ∂treeLaw ν K d ∂μ)=_
    rw [←hjoint]
    change (∫z,Function.uncurry (score K update (B.indicator (fun _ => (1:ℝ))) d) z
      ∂μ.prod (treeLaw ν K d))=_
    rw [score_eq_indicator,integral_indicator_const (1:ℝ) (event_measurable K update hu B hB d)]
    simp only [smul_eq_mul,mul_one]
  exact he ▸ hJ.trans hI

end SphericalAging.IndependentBranchingSuccessEvent
