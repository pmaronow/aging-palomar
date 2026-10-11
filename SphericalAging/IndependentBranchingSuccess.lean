module

public import SphericalAging.ConditionalCloneSuccessJensen

public section

/-! The full-depth independently branching success lower bound of
Huang--Sellke Proposition2.5(a), proved under an explicitly constructed
product tree law. Shared ancestry is retained at every recursive branch. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.IndependentBranchingSuccess
open Set MeasureTheory Filter ConditionalCloneSuccessJensen
open scoped BigOperators
variable {S G : Type} [MeasurableSpace S] [MeasurableSpace G]

@[expose] def TreeSample (G : Type) (K : ℕ) : ℕ→Type
  | 0 => Unit
  | d+1 => Fin K→G×TreeSample G K d

instance treeMeasurable (G : Type) [MeasurableSpace G] (K d : ℕ) : MeasurableSpace (TreeSample G K d) := by
  induction d with
  | zero => exact inferInstanceAs (MeasurableSpace Unit)
  | succ d ih =>
    letI := ih
    exact inferInstanceAs (MeasurableSpace (Fin K→G×TreeSample G K d))

@[expose] def treeLaw (ν : Measure G) (K : ℕ) : (d : ℕ)→Measure (TreeSample G K d)
  | 0 => Measure.dirac ()
  | d+1 => Measure.pi (fun _ : Fin K => ν.prod (treeLaw ν K d))

instance treeProbability (ν : Measure G) [IsProbabilityMeasure ν] (K d : ℕ) :
    IsProbabilityMeasure (treeLaw ν K d) := by
  induction d with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | succ d ih =>
    letI := ih
    exact inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin K => ν.prod (treeLaw ν K d))))

@[expose] def score (K : ℕ) (update : ℕ→S→G→S) (f : S→ℝ) : (d : ℕ)→S→TreeSample G K d→ℝ
  | 0,s,_ => f s
  | d+1,s,z => ∏i,score K update f d (update d s (z i).1) (z i).2

@[expose] def singleMean (ν : Measure G) (update : ℕ→S→G→S) (f : S→ℝ) : ℕ→S→ℝ
  | 0,s => f s
  | d+1,s => ∫g,singleMean ν update f d (update d s g) ∂ν

@[expose] def treeMean (ν : Measure G) (K : ℕ) (update : ℕ→S→G→S) (f : S→ℝ) (d : ℕ) (s : S) : ℝ :=
  ∫z,score K update f d s z ∂treeLaw ν K d

theorem score_measurable (K : ℕ) (update : ℕ→S→G→S)
    (hu : ∀d,Measurable (Function.uncurry (update d))) (f : S→ℝ) (hf : Measurable f) (d : ℕ) :
    Measurable (Function.uncurry (score K update f d)) := by
  induction d with
  | zero => exact hf.comp measurable_fst
  | succ d ih =>
    change Measurable (fun z : S×TreeSample G K (d+1) =>
      ∏i,score K update f d (update d z.1 (z.2 i).1) (z.2 i).2)
    apply Finset.measurable_prod
    intro i _
    have hz : Measurable (fun z : S×TreeSample G K (d+1) => z.2 i) :=
      (measurable_pi_apply i).comp measurable_snd
    have hx := (hu d).comp (measurable_fst.prodMk hz.fst)
    exact ih.comp (hx.prodMk hz.snd)

theorem score_bounds (K : ℕ) (update : ℕ→S→G→S) (f : S→ℝ)
    (hf : ∀s,0≤f s ∧ f s≤1) (d : ℕ) (s : S) (z : TreeSample G K d) :
    0≤score K update f d s z ∧ score K update f d s z≤1 := by
  induction d generalizing s with
  | zero => exact hf s
  | succ d ih => exact ⟨Finset.prod_nonneg (fun i _ => (ih _ _).1),
      Finset.prod_le_one₀ (fun i _ => (ih _ _).1) (fun i _ => (ih _ _).2)⟩

theorem singleMean_measurable (ν : Measure G) [IsProbabilityMeasure ν]
    (update : ℕ→S→G→S) (hu : ∀d,Measurable (Function.uncurry (update d)))
    (f : S→ℝ) (hf : Measurable f) (d : ℕ) : Measurable (singleMean ν update f d) := by
  induction d with
  | zero => exact hf
  | succ d ih => exact (ih.comp (hu d)).stronglyMeasurable.integral_prod_right'.measurable

theorem singleMean_bounds (ν : Measure G) [IsProbabilityMeasure ν]
    (update : ℕ→S→G→S) (hu : ∀d,Measurable (Function.uncurry (update d)))
    (f : S→ℝ) (hfm : Measurable f) (hf : ∀s,0≤f s ∧ f s≤1) (d : ℕ) (s : S) :
    0≤singleMean ν update f d s ∧ singleMean ν update f d s≤1 := by
  induction d generalizing s with
  | zero => exact hf s
  | succ d ih =>
    have hm : Measurable (fun g : G => singleMean ν update f d (update d s g)) :=
      (singleMean_measurable ν update hu f hfm d).comp
      ((hu d).comp (measurable_const.prodMk measurable_id))
    refine ⟨integral_nonneg (fun g => (ih _).1),?_⟩
    have hh := integral_mono (bounded_integrable ν _ hm (fun g => ih _)) (integrable_const (1:ℝ))
      (fun g => (ih _).2)
    simpa only [singleMean,integral_const,probReal_univ,one_smul] using hh

theorem treeMean_bounds (ν : Measure G) [IsProbabilityMeasure ν]
    (K : ℕ) (update : ℕ→S→G→S) (hu : ∀d,Measurable (Function.uncurry (update d)))
    (f : S→ℝ) (hfm : Measurable f) (hf : ∀s,0≤f s ∧ f s≤1) (d : ℕ) (s : S) :
    0≤treeMean ν K update f d s ∧ treeMean ν K update f d s≤1 := by
  have hm : Measurable (score K update f d s) :=
    (score_measurable K update hu f hfm d).comp (measurable_const.prodMk measurable_id)
  refine ⟨integral_nonneg (fun z => (score_bounds K update f hf d s z).1),?_⟩
  have hh := integral_mono (bounded_integrable (treeLaw ν K d) _ hm (score_bounds K update f hf d s))
    (integrable_const (1:ℝ)) (fun z => (score_bounds K update f hf d s z).2)
  simpa only [treeMean,integral_const,probReal_univ,one_smul] using hh

theorem treeMean_succ (ν : Measure G) [IsProbabilityMeasure ν]
    (K : ℕ) (update : ℕ→S→G→S) (hu : ∀d,Measurable (Function.uncurry (update d)))
    (f : S→ℝ) (hfm : Measurable f) (hf : ∀s,0≤f s ∧ f s≤1) (d : ℕ) (s : S) :
    treeMean ν K update f (d+1) s=(∫g,treeMean ν K update f d (update d s g) ∂ν)^K := by
  let h : G×TreeSample G K d→ℝ := fun z => score K update f d (update d s z.1) z.2
  have hm : Measurable h := (score_measurable K update hu f hfm d).comp
    (((hu d).comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
  have hi := bounded_integrable (ν.prod (treeLaw ν K d)) h hm
    (fun z => score_bounds K update f hf d (update d s z.1) z.2)
  have hh := integral_fintype_prod_eq_pow (ι:=Fin K) (μ:=ν.prod (treeLaw ν K d)) h
  change (∫z,∏i,h (z i) ∂Measure.pi (fun _ : Fin K => ν.prod (treeLaw ν K d)))=_
  rw [hh,integral_prod h hi]
  simp only [Fintype.card_fin,treeMean,h]

theorem actual_tree_success_lower (ν : Measure G) [IsProbabilityMeasure ν]
    (K : ℕ) (update : ℕ→S→G→S) (hu : ∀d,Measurable (Function.uncurry (update d)))
    (f : S→ℝ) (hfm : Measurable f) (hf : ∀s,0≤f s ∧ f s≤1) (d : ℕ) (s : S) :
    (singleMean ν update f d s)^(K^d)≤treeMean ν K update f d s := by
  induction d generalizing s with
  | zero =>
    simp only [singleMean,pow_zero,pow_one,treeMean,score,treeLaw,integral_const,
      Measure.real,Measure.dirac_apply_of_mem,mem_univ,ENNReal.toReal_one,one_smul]
    exact le_rfl
  | succ d ih =>
    let m : G→ℝ := fun g => singleMean ν update f d (update d s g)
    let b : G→ℝ := fun g => treeMean ν K update f d (update d s g)
    have hmm : Measurable m := (singleMean_measurable ν update hu f hfm d).comp
      ((hu d).comp (measurable_const.prodMk measurable_id))
    have hbm : Measurable b := by
      have htm := (score_measurable K update hu f hfm d).stronglyMeasurable.integral_prod_right'
        (ν := treeLaw ν K d)
      exact htm.measurable.comp ((hu d).comp (measurable_const.prodMk measurable_id))
    have hmb g : 0≤m g ∧ m g≤1 := singleMean_bounds ν update hu f hfm hf d _
    have hbb g : 0≤b g ∧ b g≤1 := treeMean_bounds ν K update hu f hfm hf d _
    have hmI := bounded_integrable ν m hmm hmb
    have hmpI := bounded_integrable ν (fun g => (m g)^(K^d)) (hmm.pow_const _)
      (fun g => ⟨pow_nonneg (hmb g).1 _,pow_le_one₀ (hmb g).1 (hmb g).2⟩)
    have hbI := bounded_integrable ν b hbm hbb
    have hJ := (convexOn_pow (K^d)).map_integral_le (continuous_pow _).continuousOn isClosed_Ici
      (ae_of_all _ (fun g => (hmb g).1)) hmI hmpI
    have hI := integral_mono hmpI hbI (fun g => ih _)
    rw [treeMean_succ ν K update hu f hfm hf d s]
    have hpow := pow_le_pow_left₀ (pow_nonneg (integral_nonneg (fun g => (hmb g).1)) _)
      (hJ.trans hI) K
    simpa only [←pow_mul,←pow_succ,singleMean,m,b] using hpow

end SphericalAging.IndependentBranchingSuccess
