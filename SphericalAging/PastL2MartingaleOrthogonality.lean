module

public import SphericalAging.VectorIto
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

public section

/-! Genuine L² orthogonality of a full-filtration martingale increment
against an arbitrary unbounded square-integrable past observable. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.PastL2MartingaleOrthogonality
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

 theorem past_L2_increment_mean_zero (M : ℝ≥0→Ω→ℝ) (hM : Martingale M F P)
    (s t : ℝ≥0) (hst : s≤t) (hMs : MemLp (M s) 2 P) (hMt : MemLp (M t) 2 P)
    (Y : Ω→ℝ) (hY : StronglyMeasurable[F s] Y) (hY2 : MemLp Y 2 P) :
    Integrable (fun ω => Y ω*(M t ω-M s ω)) P ∧
      (∫ ω,Y ω*(M t ω-M s ω) ∂P)=0 := by
  have hd : Integrable (M t-M s) P := (hMt.sub hMs).integrable (by norm_num)
  have hi : Integrable (Y*(M t-M s)) P := memLp_one_iff_integrable.mp (hY2.mul (hMt.sub hMs))
  have hc : P[M t-M s|F s]=ᵐ[P] (fun _ => (0 : ℝ)) := by
    have hh := condExp_sub (hM.integrable t) (hM.integrable s) (F s)
    have hself := condExp_of_stronglyMeasurable (F.le s) (hM.stronglyAdapted s) (hM.integrable s)
    rw [hself] at hh
    filter_upwards [hh,hM.condExp_ae_eq hst] with ω hω hmt
    rw [hω]
    simp only [Pi.sub_apply,hmt,sub_self]
  refine ⟨hi,?_⟩
  calc
    _=∫ ω,P[Y*(M t-M s)|F s] ω ∂P := (integral_condExp (F.le s)).symm
    _=∫ ω,Y ω*P[M t-M s|F s] ω ∂P := integral_congr_ae
      (condExp_mul_of_stronglyMeasurable_left hY hi hd)
    _=0 := by
      have he : (fun ω => Y ω*P[M t-M s|F s] ω)=ᵐ[P] (fun _ => (0 : ℝ)) :=
        hc.mono (fun ω hω => by dsimp only at hω ⊢;rw [hω];simp)
      rw [integral_congr_ae he]
      simp

end SphericalAging.PastL2MartingaleOrthogonality
