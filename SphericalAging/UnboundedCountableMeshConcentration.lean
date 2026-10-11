module

public import SphericalAging.CountableCenteredSup
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Set

public section

/-! An unbounded countable random family is controlled by a genuine L²
envelope, a finite mesh and a weighted good-event modulus. Exceptional
events are charged by Cauchy--Schwarz, with no supremum moment premise. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace SphericalAging.UnboundedCountableMeshConcentration
open CountableCenteredSup
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {Ω ι κ : Type*} [MeasurableSpace Ω] [Countable ι] [Nonempty ι] [Fintype κ]
    {P : Measure Ω} [IsProbabilityMeasure P]

theorem mean_abs_le_envelope (Y : ι→Ω→ℝ) (hY : ∀i,MemLp (Y i) 2 P)
    {U : Ω→ℝ} (hU : MemLp U 2 P) (hYb : ∀ᵐω ∂P,∀i,|Y i ω|≤U ω) (i : ι) :
    |∫ω,Y i ω ∂P|≤∫ω,U ω ∂P :=
  abs_integral_le_integral_abs.trans (integral_mono_ae ((hY i).integrable (by norm_num)).abs
    (hU.integrable (by norm_num)) (hYb.mono (fun ω hω => hω i)))

theorem centeredSup_bounds_of_envelope (Y : ι→Ω→ℝ) (hY : ∀i,MemLp (Y i) 2 P)
    {U : Ω→ℝ} (hU : MemLp U 2 P) (hUn : ∀ᵐω ∂P,0≤U ω)
    (hYb : ∀ᵐω ∂P,∀i,|Y i ω|≤U ω) :
    ∀ᵐω ∂P,0≤centeredSup Y P ω ∧ centeredSup Y P ω≤U ω+(∫z,U z ∂P) := by
  have hm := mean_abs_le_envelope Y hY hU hYb
  filter_upwards [hYb,hUn] with ω hω _
  have he (i : ι) : |Y i ω-∫z,Y i z ∂P|≤U ω+(∫z,U z ∂P) :=
    (abs_sub _ _).trans (add_le_add (hω i) (hm i))
  have hbd : BddAbove (range (fun i : ι => |Y i ω-∫z,Y i z ∂P|)) :=
    ⟨U ω+(∫z,U z ∂P),by rintro _ ⟨i,rfl⟩;exact he i⟩
  exact ⟨(abs_nonneg _).trans (le_ciSup hbd (Classical.arbitrary ι)),ciSup_le he⟩

theorem centeredSup_memLp_two_of_envelope (Y : ι→Ω→ℝ) (hY : ∀i,MemLp (Y i) 2 P)
    {U : Ω→ℝ} (hU : MemLp U 2 P) (hUn : ∀ᵐω ∂P,0≤U ω)
    (hYb : ∀ᵐω ∂P,∀i,|Y i ω|≤U ω) : MemLp (centeredSup Y P) 2 P := by
  have hEU : 0≤∫z,U z ∂P := integral_nonneg_of_ae hUn
  apply (hU.add (memLp_const (∫z,U z ∂P))).of_le (centeredSup_aestronglyMeasurable Y hY)
  filter_upwards [centeredSup_bounds_of_envelope Y hY hU hUn hYb,hUn] with ω hb hn
  simpa only [Real.norm_eq_abs,Pi.add_apply,abs_of_nonneg hb.1,abs_of_nonneg (add_nonneg hn hEU)] using hb.2

theorem event_integral_le_sqrt_moment_probability {U : Ω→ℝ} (hU : MemLp U 2 P)
    (hUn : ∀ᵐω ∂P,0≤U ω) {bad : Set Ω} (hbad : MeasurableSet bad) :
    (∫ω,bad.indicator U ω ∂P)≤Real.sqrt ((∫ω,(U ω)^2 ∂P)*P.real bad) := by
  have hg : MemLp (bad.indicator (fun _ : Ω => (1:ℝ))) (ENNReal.ofReal 2) P :=
    memLp_indicator_const _ hbad 1 (Or.inr (measure_ne_top P bad))
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two hUn
    (.of_forall (fun ω => by by_cases h : ω∈bad <;> simp [h])) (by simpa using hU) hg
  have he : (fun ω => U ω*bad.indicator (fun _ : Ω => (1:ℝ)) ω)=bad.indicator U := by
    funext ω
    by_cases h : ω∈bad <;> simp [h]
  have he2 : (fun ω => (bad.indicator (fun _ : Ω => (1:ℝ)) ω)^(2:ℝ))=
      bad.indicator (fun _ : Ω => (1:ℝ)) := by
    funext ω
    by_cases h : ω∈bad <;> simp [h]
  rw [he,he2,integral_indicator_const 1 hbad] at hh
  simpa only [Real.rpow_two,←Real.sqrt_eq_rpow,smul_eq_mul,mul_one,
    ←Real.sqrt_mul (integral_nonneg (fun ω => sq_nonneg (U ω)))] using hh

/-- Weighted good-event mesh comparison for the literal expected centered
countable supremum. Every supremum measurability and integrability input is
derived from the L² envelope. -/
theorem centeredSup_integral_le (Y : ι→Ω→ℝ) (Z : κ→Ω→ℝ) (π : ι→κ)
    (hY : ∀i,MemLp (Y i) 2 P) (hZ : ∀k,MemLp (Z k) 2 P)
    {U : Ω→ℝ} (hU : MemLp U 2 P) (hUn : ∀ᵐω ∂P,0≤U ω)
    (hYb : ∀ᵐω ∂P,∀i,|Y i ω|≤U ω) (hZb : ∀ᵐω ∂P,∀k,|Z k ω|≤U ω)
    {bad : Set Ω} (hbad : MeasurableSet bad) {e : ℝ} (he : 0≤e)
    (hgood : ∀ᵐω ∂P,ω∉bad→∀i,|Y i ω-Z (π i) ω|≤e*(1+U ω)) :
    (∫ω,centeredSup Y P ω ∂P)≤
      (∑k : κ,∫ω,|Z k ω-∫z,Z k z ∂P| ∂P)+
      2*e*(1+(∫ω,U ω ∂P))+4*Real.sqrt ((∫ω,(U ω)^2 ∂P)*P.real bad) := by
  have hUi := hU.integrable (by norm_num : (1:ℝ≥0∞)≤2)
  have hEi := hUi.indicator hbad
  let G : Ω→ℝ := fun ω => e*(1+U ω)+2*bad.indicator U ω
  let a : ℝ := e*(1+(∫ω,U ω ∂P))+2*(∫ω,bad.indicator U ω ∂P)
  have hGi : Integrable G P := ((integrable_const (1:ℝ)).add hUi).const_mul e |>.add (hEi.const_mul 2)
  have h1i : Integrable (fun ω => e*(1+U ω)) P := ((integrable_const (1:ℝ)).add hUi).const_mul e
  have hGE : (∫ω,G ω ∂P)=a := by
    dsimp only [G,a]
    rw [integral_add h1i (hEi.const_mul 2),integral_const_mul,integral_const_mul,
      integral_add (integrable_const (1:ℝ)) hUi]
    simp only [integral_const,probReal_univ,smul_eq_mul,mul_one]
  have hGap : ∀ᵐω ∂P,∀i,|Y i ω-Z (π i) ω|≤G ω := by
    filter_upwards [hYb,hZb,hgood,hUn] with ω hYω hZω hω hn
    intro i
    by_cases hb : ω∈bad
    · dsimp only [G]
      rw [indicator_of_mem hb]
      have hg := mul_nonneg he (by linarith : 0≤1+U ω)
      exact (abs_sub _ _).trans (by linarith [hYω i,hZω (π i)])
    · simpa only [G,indicator_of_notMem hb,mul_zero,add_zero] using hω hb i
  have hmean (i : ι) : |(∫ω,Y i ω ∂P)-(∫ω,Z (π i) ω ∂P)|≤a := by
    have hh := abs_integral_le_integral_abs (f:=fun ω => Y i ω-Z (π i) ω) (μ:=P)
    have hg := integral_mono_ae (((hY i).integrable (by norm_num)).sub
      ((hZ (π i)).integrable (by norm_num))).abs hGi (hGap.mono (fun ω hω => hω i))
    rw [integral_sub ((hY i).integrable (by norm_num)) ((hZ (π i)).integrable (by norm_num))] at hh
    exact hh.trans (hg.trans_eq hGE)
  have hZi (k : κ) : Integrable (fun ω => |Z k ω-∫z,Z k z ∂P|) P :=
    (((hZ k).integrable (by norm_num)).sub (integrable_const _)).abs
  have hgrid (ω : Ω) (k : κ) : |Z k ω-∫z,Z k z ∂P|≤∑j : κ,|Z j ω-∫z,Z j z ∂P| :=
    Finset.single_le_sum (f:=fun j : κ => |Z j ω-∫z,Z j z ∂P|) (fun j _ => abs_nonneg _) (Finset.mem_univ k)
  have hsup : ∀ᵐω ∂P,centeredSup Y P ω≤(∑k : κ,|Z k ω-∫z,Z k z ∂P|)+G ω+a := by
    filter_upwards [hGap] with ω hω
    apply ciSup_le
    intro i
    have heq : Y i ω-∫z,Y i z ∂P=(Y i ω-Z (π i) ω)+(Z (π i) ω-∫z,Z (π i) z ∂P)+
        ((∫z,Z (π i) z ∂P)-(∫z,Y i z ∂P)) := by ring
    rw [heq]
    have h₁ := abs_add_le (Y i ω-Z (π i) ω) (Z (π i) ω-∫z,Z (π i) z ∂P)
    have h₂ := abs_add_le ((Y i ω-Z (π i) ω)+(Z (π i) ω-∫z,Z (π i) z ∂P))
      ((∫z,Z (π i) z ∂P)-(∫z,Y i z ∂P))
    have hm := hmean i
    rw [abs_sub_comm] at hm
    linarith [hω i,hgrid ω (π i)]
  have hi := integral_mono_ae ((centeredSup_memLp_two_of_envelope Y hY hU hUn hYb).integrable (by norm_num))
    (((integrable_finsetSum Finset.univ (fun k _ => hZi k)).add hGi).add (integrable_const a)) hsup
  have hEbound := event_integral_le_sqrt_moment_probability hU hUn hbad
  have hSi : Integrable (fun ω => ∑k : κ,|Z k ω-∫z,Z k z ∂P|) P :=
    integrable_finsetSum Finset.univ (fun k _ => hZi k)
  have hSGi : Integrable (fun ω => (∑k : κ,|Z k ω-∫z,Z k z ∂P|)+G ω) P := hSi.add hGi
  change (∫ω,centeredSup Y P ω ∂P)≤(∫ω,(∑k : κ,|Z k ω-∫z,Z k z ∂P|)+G ω+a ∂P) at hi
  rw [integral_add hSGi (integrable_const a),
    integral_add hSi hGi,
    integral_finsetSum Finset.univ (fun k _ => hZi k),hGE] at hi
  simp only [integral_const,probReal_univ,smul_eq_mul,mul_one] at hi
  dsimp only [a] at hi
  linarith

end SphericalAging.UnboundedCountableMeshConcentration
