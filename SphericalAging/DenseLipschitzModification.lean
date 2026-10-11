module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Sequences
public import Mathlib.Tactic

public section

/-! A genuine globally Lipschitz jointly measurable version from fixed
parameter measurability and almost-everywhere pairwise Lipschitz bounds.
The common good event uses only a countable dense parameter set. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.DenseLipschitzModification
open Set Filter MeasureTheory Topology
open scoped Topology NNReal
attribute [local instance] Classical.propDecidable
variable {E F Ω : Type*} [MetricSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [OpensMeasurableSpace E]
  [NormedAddCommGroup F] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace Ω]

@[expose]  def good (D : Set E) (L : ℝ≥0) (f : E→Ω→F) : Set Ω :=
  {ω | ∀x y : D,dist (f x ω) (f y ω)≤L*dist (x:E) (y:E)}

 theorem good_measurable {D : Set E} (hD : D.Countable) (L : ℝ≥0) (f : E→Ω→F)
    (hf : ∀x,Measurable (f x)) : MeasurableSet (good D L f) := by
  letI : Countable D := hD.to_subtype
  simp only [good,setOf_forall]
  apply MeasurableSet.iInter
  intro x
  apply MeasurableSet.iInter
  intro y
  exact measurableSet_le ((hf x).dist (hf y)) measurable_const

 theorem good_ae {D : Set E} (hD : D.Countable) (L : ℝ≥0) (f : E→Ω→F) (μ : Measure Ω)
    (hpair : ∀x y,∀ᵐω ∂μ,dist (f x ω) (f y ω)≤L*dist x y) : ∀ᵐω ∂μ,ω∈good D L f := by
  letI : Countable D := hD.to_subtype
  exact (ae_all_iff.mpr (fun x : D => ae_all_iff.mpr (fun y : D => hpair x y)))

 theorem dense_lipschitz {D : Set E} {L : ℝ≥0} {f : E→Ω→F} {ω : Ω}
    (hω : ω∈good D L f) : LipschitzWith L (fun x : D => f x ω) :=
  LipschitzWith.of_dist_le_mul hω

@[expose]  def version (D : Set E) (hd : Dense D) (L : ℝ≥0) (f : E→Ω→F) (ω : Ω) (x : E) : F :=
  if ω∈good D L f then hd.extend (fun y : D => f y ω) x else 0

 theorem version_lipschitz {D : Set E} (hd : Dense D) (L : ℝ≥0) (f : E→Ω→F) (ω : Ω) :
    LipschitzWith L (version D hd L f ω) := by
  classical
  by_cases hω : ω∈good D L f
  · have he : version D hd L f ω=hd.extend (fun y : D => f y ω) := by
      funext x
      simp only [version,if_pos hω]
    rw [he]
    exact hd.lipschitzWith_extend (dense_lipschitz hω)
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [version,if_neg hω,dist_self]
    exact mul_nonneg L.coe_nonneg dist_nonneg

 theorem version_dense {D : Set E} (hd : Dense D) (L : ℝ≥0) (f : E→Ω→F)
    {ω : Ω} (hω : ω∈good D L f) (x : D) : version D hd L f ω x=f x ω := by
  rw [version,if_pos hω]
  exact hd.extend_eq (dense_lipschitz hω).continuous x

 theorem exists_approximation {D : Set E} (hd : Dense D) (x : E) :
    ∃u : ℕ→E,(∀n,u n∈D) ∧ Tendsto u atTop (𝓝 x) :=
  mem_closure_iff_seq_limit.mp (hd x)

 theorem version_tendsto_dense {D : Set E} (hd : Dense D) (L : ℝ≥0) (f : E→Ω→F)
    {u : ℕ→E} (hu : ∀n,u n∈D) {x : E} (hux : Tendsto u atTop (𝓝 x)) (ω : Ω) :
    Tendsto (fun n => if ω∈good D L f then f (u n) ω else 0) atTop
      (𝓝 (version D hd L f ω x)) := by
  classical
  have hv := ((version_lipschitz hd L f ω).continuous.tendsto x).comp hux
  convert hv using 1
  funext n
  change (if ω∈good D L f then f (u n) ω else 0)=version D hd L f ω (u n)
  by_cases hω : ω∈good D L f
  · rw [if_pos hω]
    exact (version_dense hd L f hω ⟨u n,hu n⟩).symm
  · simp only [if_neg hω,version]

 theorem version_section_measurable {D : Set E} (hD : D.Countable) (hd : Dense D)
    (L : ℝ≥0) (f : E→Ω→F) (hf : ∀x,Measurable (f x)) (x : E) :
    Measurable (fun ω => version D hd L f ω x) := by
  classical
  obtain ⟨u,hu,hux⟩ := exists_approximation hd x
  apply measurable_of_tendsto_metrizable
    (f:=fun n ω => if ω∈good D L f then f (u n) ω else 0)
  · intro n
    exact Measurable.ite (good_measurable hD L f hf) (hf (u n)) measurable_const
  · rw [tendsto_pi_nhds]
    exact version_tendsto_dense hd L f hu hux

 theorem version_measurable {D : Set E} (hD : D.Countable) (hd : Dense D)
    (L : ℝ≥0) (f : E→Ω→F) (hf : ∀x,Measurable (f x)) :
    Measurable (fun z : Ω×E => version D hd L f z.1 z.2) := by
  have hm := measurable_uncurry_of_continuous_of_measurable
    (u:=fun x ω => version D hd L f ω x)
    (fun ω => (version_lipschitz hd L f ω).continuous)
    (version_section_measurable hD hd L f hf)
  exact hm.comp measurable_swap

 theorem version_ae {D : Set E} (hD : D.Countable) (hd : Dense D)
    (L : ℝ≥0) (f : E→Ω→F) (μ : Measure Ω)
    (hpair : ∀x y,∀ᵐω ∂μ,dist (f x ω) (f y ω)≤L*dist x y) (x : E) :
    (fun ω => version D hd L f ω x)=ᵐ[μ]f x := by
  classical
  obtain ⟨u,hu,hux⟩ := exists_approximation hd x
  have hc : ∀ᵐω ∂μ,∀n,dist (f (u n) ω) (f x ω)≤L*dist (u n) x :=
    ae_all_iff.mpr (fun n => hpair (u n) x)
  filter_upwards [good_ae hD L f μ hpair,hc] with ω hω hbound
  have hv := version_tendsto_dense hd L f hu hux ω
  simp only [if_pos hω] at hv
  have hz : Tendsto (fun n => (L:ℝ)*dist (u n) x) atTop (𝓝 0) := by
    have hd : Tendsto (fun n => dist (u n) x) atTop (𝓝 0) := by
      simpa only [dist_self] using hux.dist (tendsto_const_nhds (x:=x))
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (L:ℝ)) atTop (𝓝 (L:ℝ))).mul hd
  have hf : Tendsto (fun n => f (u n) ω) atTop (𝓝 (f x ω)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun n => dist_nonneg) hbound hz
  exact tendsto_nhds_unique hv hf

 theorem exists_jointly_measurable_lipschitz_version (L : ℝ≥0) (f : E→Ω→F) (μ : Measure Ω)
    (hf : ∀x,Measurable (f x))
    (hpair : ∀x y,∀ᵐω ∂μ,dist (f x ω) (f y ω)≤L*dist x y) :
    ∃g : Ω×E→F,Measurable g ∧ (∀ω,LipschitzWith L (fun x => g (ω,x))) ∧
      ∀x,(fun ω => g (ω,x))=ᵐ[μ]f x := by
  obtain ⟨D,hD,hd⟩ := TopologicalSpace.exists_countable_dense E
  exact ⟨fun z => version D hd L f z.1 z.2,version_measurable hD hd L f hf,
    version_lipschitz hd L f,version_ae hD hd L f μ hpair⟩

end SphericalAging.DenseLipschitzModification
