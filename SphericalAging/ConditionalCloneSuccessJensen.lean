module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul

public section

/-! Genuine independent-clone Jensen inequality used at each tree level
in Huang--Sellke Proposition2.5(a). The joint success probability is
computed under the actual shared-seed and independent-noise product law. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ConditionalCloneSuccessJensen
open Set Filter MeasureTheory
open scoped BigOperators
variable {S G : Type*} [MeasurableSpace S] [MeasurableSpace G]

@[expose] def cloneScore (K : ℕ) (f : S×G→ℝ) (z : S×(Fin K→G)) : ℝ :=
  ∏i,f (z.1,z.2 i)

theorem bounded_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω→ℝ) (hf : Measurable f) (hb : ∀ω,0≤f ω ∧ f ω≤1) : Integrable f μ := by
  apply (integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable
  exact ae_of_all _ (fun ω => by rw [Real.norm_eq_abs,abs_of_nonneg (hb ω).1];exact (hb ω).2)

theorem cloneScore_measurable (K : ℕ) (f : S×G→ℝ) (hf : Measurable f) :
    Measurable (cloneScore K f) := by
  apply Finset.measurable_prod
  intro i _
  exact hf.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

theorem cloneScore_bounds (K : ℕ) (f : S×G→ℝ) (hf : ∀z,0≤f z ∧ f z≤1) (z : S×(Fin K→G)) :
    0≤cloneScore K f z ∧ cloneScore K f z≤1 := by
  refine ⟨Finset.prod_nonneg (fun i _ => (hf _).1),?_⟩
  exact Finset.prod_le_one₀ (fun i _ => (hf _).1) (fun i _ => (hf _).2)

theorem actual_clone_mean_ge (K : ℕ) (μ : Measure S) (ν : Measure G)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : S×G→ℝ) (hf : Measurable f) (hb : ∀z,0≤f z ∧ f z≤1) :
    (∫z,f z ∂μ.prod ν)^K≤
      ∫z,cloneScore K f z ∂μ.prod (Measure.pi (fun _ : Fin K => ν)) := by
  let m : S→ℝ := fun s => ∫g,f (s,g) ∂ν
  have hfm := hf.stronglyMeasurable
  have hmm : StronglyMeasurable m := hfm.integral_prod_right'
  have hmb s : 0≤m s ∧ m s≤1 := by
    have hfs : Measurable (fun g => f (s,g)) := hf.comp (measurable_const.prodMk measurable_id)
    refine ⟨integral_nonneg (fun g => (hb (s,g)).1),?_⟩
    have hh := integral_mono (bounded_integrable ν _ hfs (fun g => hb (s,g))) (integrable_const (1:ℝ))
      (fun g => (hb (s,g)).2)
    simpa only [integral_const,probReal_univ,one_smul] using hh
  have hmi := bounded_integrable μ m hmm.measurable hmb
  have hmpb s : 0≤(m s)^K ∧ (m s)^K≤1 :=
    ⟨pow_nonneg (hmb s).1 _,pow_le_one₀ (hmb s).1 (hmb s).2⟩
  have hmpi := bounded_integrable μ (fun s => (m s)^K) (hmm.measurable.pow_const K) hmpb
  have hcloneI := bounded_integrable (μ.prod (Measure.pi (fun _ : Fin K => ν))) (cloneScore K f)
    (cloneScore_measurable K f hf) (cloneScore_bounds K f hb)
  have hjoint : (∫z,cloneScore K f z ∂μ.prod (Measure.pi (fun _ : Fin K => ν)))=∫s,(m s)^K ∂μ := by
    rw [integral_prod _ hcloneI]
    apply integral_congr_ae
    exact ae_of_all _ (fun s => by
      simpa only [cloneScore,m,Fintype.card_fin] using
        integral_fintype_prod_eq_pow (ι:=Fin K) (μ:=ν) (fun g => f (s,g)))
  have hsingle : (∫z,f z ∂μ.prod ν)=∫s,m s ∂μ := integral_prod f (bounded_integrable _ f hf hb)
  rw [hjoint,hsingle]
  exact (convexOn_pow K).map_integral_le (continuous_pow K).continuousOn isClosed_Ici
    (ae_of_all _ (fun s => (hmb s).1)) hmi hmpi

@[expose] def cloneEvent (K : ℕ) (B : Set (S×G)) : Set (S×(Fin K→G)) :=
  {z | ∀i,(z.1,z.2 i)∈B}

theorem cloneEvent_measurable (K : ℕ) (B : Set (S×G)) (hB : MeasurableSet B) :
    MeasurableSet (cloneEvent K B) := by
  have he : cloneEvent K B=⋂i : Fin K,(fun z : S×(Fin K→G) => (z.1,z.2 i))⁻¹' B := by
    ext z;simp only [cloneEvent,mem_setOf_eq,mem_iInter,mem_preimage]
  rw [he]
  exact MeasurableSet.iInter (fun i => hB.preimage
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))

theorem actual_clone_success_probability_ge (K : ℕ) (μ : Measure S) (ν : Measure G)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (B : Set (S×G)) (hB : MeasurableSet B) :
    (μ.prod ν).real B^K≤(μ.prod (Measure.pi (fun _ : Fin K => ν))).real (cloneEvent K B) := by
  classical
  let f : S×G→ℝ := B.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hB
  have hb z : 0≤f z ∧ f z≤1 := by
    dsimp only [f]
    by_cases hz : z∈B <;> simp [hz]
  have hh := actual_clone_mean_ge K μ ν f hf hb
  have he : cloneScore K f=(cloneEvent K B).indicator (fun _ => (1:ℝ)) := by
    funext z
    by_cases hz : z∈cloneEvent K B
    · have hall : ∀i,(z.1,z.2 i)∈B := hz
      simp only [cloneScore,f,Set.indicator_of_mem hz]
      simp [hall]
    · have hn : ∃i,(z.1,z.2 i)∉B := by simpa only [cloneEvent,mem_setOf_eq,not_forall] using hz
      obtain ⟨i,hi⟩ := hn
      rw [Set.indicator_of_notMem hz]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [f,Set.indicator_of_notMem hi])
  rw [he,integral_indicator_const (1:ℝ) (cloneEvent_measurable K B hB)] at hh
  simpa only [f,integral_indicator_const (1:ℝ) hB,smul_eq_mul,mul_one] using hh

end SphericalAging.ConditionalCloneSuccessJensen
