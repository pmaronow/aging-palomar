module

public import SphericalAging.ForkCurriedSaturation
public import Mathlib.Topology.Instances.NNReal.Lemmas

public section

/-! Genuine fork parameter filters: dimension is handled separately, then
time, error 1/(m+1), branch count and age in that order. No uniformity in
fixed outer parameters is inferred. -/
noncomputable section
namespace SphericalAging.ForkOrderedParameters
open Filter Set
open scoped NNReal Topology

instance curry_neBot {A B : Type*} (la : Filter A) (lb : Filter B)
    [NeBot la] [NeBot lb] : NeBot (la.curry lb) := by
  rw [neBot_iff]
  intro he
  have hh : ∀ᶠz : A×B in la.curry lb,False := by simp [he]
  rw [eventually_curry_iff] at hh
  obtain ⟨a,ha⟩ := hh.exists
  obtain ⟨b,hb⟩ := ha.exists
  exact hb

theorem tendsto_curry_map {A B C D : Type*} {la : Filter A} {lb : Filter B}
    {lc : Filter C} {ld : Filter D} {f : A→C} {g : B→D}
    (hf : Tendsto f la lc) (hg : Tendsto g lb ld) :
    Tendsto (fun z : A×B => (f z.1,g z.2)) (la.curry lb) (lc.curry ld) := by
  intro S hS
  change ∀ᶠz in la.curry lb,(f z.1,g z.2)∈S
  rw [eventually_curry_iff]
  have hh : ∀ᶠc in lc,∀ᶠd in ld,(c,d)∈S := eventually_curry_iff.mp hS
  filter_upwards [hf.eventually hh] with a ha
  exact hg.eventually ha

@[expose] abbrev Parameters := (ℝ≥0×ℕ)×ℕ
@[expose] def orderedFilter : Filter Parameters :=
  ((atTop : Filter ℝ≥0).curry (atTop : Filter ℕ)).curry (atTop : Filter ℕ)
instance orderedFilter_neBot : NeBot orderedFilter := by
  unfold orderedFilter
  infer_instance

@[expose] def age (a : Parameters) : ℝ≥0 := a.1.1
@[expose] def branches (a : Parameters) : ℕ := a.1.2+1
@[expose] def error (a : Parameters) : ℝ := 1/((a.2+1:ℕ):ℝ)

theorem branches_positive (a : Parameters) : 1≤branches a := by simp [branches]
theorem error_positive (a : Parameters) : 0<error a := by unfold error;positivity

theorem age_branches_tendsto :
    Tendsto (fun a => ((age a:ℝ),branches a)) orderedFilter (atTop.curry atTop) := by
  have hL : Tendsto (fun L : ℝ≥0 => (L:ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hK : Tendsto (fun K : ℕ => K+1) atTop atTop :=
    (tendsto_add_atTop_iff_nat 1).mpr tendsto_id
  exact (tendsto_curry_map hL hK).comp
    (tendsto_fst.mono_left curry_le_prod)

theorem error_tendsto_zero : Tendsto error orderedFilter (𝓝 0) := by
  have hm : Tendsto (fun m : ℕ => 1/((m+1:ℕ):ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_const_div_atTop_nhds_zero_nat 1)
  exact hm.comp (tendsto_snd.mono_left curry_le_prod)

@[expose] def trunkTime (t : ℕ→ℝ) (s L : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  max (s+1) (Real.toNNReal (t n-L))

theorem trunkTime_positive (t : ℕ→ℝ) (s L : ℝ≥0) (n : ℕ) : 0<trunkTime t s L n :=
  lt_of_lt_of_le (by positivity : 0<s+1) (le_max_left _ _)

theorem waiting_le_trunkTime (t : ℕ→ℝ) (s L : ℝ≥0) (n : ℕ) : s≤trunkTime t s L n :=
  (by simp : s≤s+1).trans (le_max_left _ _)

theorem trunkTime_tendsto {t : ℕ→ℝ} (ht : Tendsto t atTop atTop) (s L : ℝ≥0) :
    Tendsto (fun n => (trunkTime t s L n:ℝ)) atTop atTop := by
  apply tendsto_atTop_mono _ (tendsto_atTop_add_const_right atTop (-(L:ℝ)) ht)
  intro n
  change t n+(-(L:ℝ))≤(trunkTime t s L n:ℝ)
  rw [←sub_eq_add_neg]
  exact (Real.le_coe_toNNReal _).trans (by exact_mod_cast le_max_right (s+1) (Real.toNNReal (t n-L)))

theorem trunk_end_eventually {t : ℕ→ℝ} (ht : Tendsto t atTop atTop) (s L : ℝ≥0) :
    ∀ᶠn in atTop,(trunkTime t s L n:ℝ)+(L:ℝ)=t n := by
  filter_upwards [ht.eventually (eventually_ge_atTop ((L:ℝ)+(s:ℝ)+1))] with n hn
  have hd : 0≤t n-(L:ℝ) := by linarith [s.coe_nonneg]
  have hmax : s+1≤Real.toNNReal (t n-L) := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ hd]
    simp only [NNReal.coe_add,NNReal.coe_one]
    linarith
  simp only [trunkTime,max_eq_right hmax,Real.coe_toNNReal _ hd]
  ring

end SphericalAging.ForkOrderedParameters
