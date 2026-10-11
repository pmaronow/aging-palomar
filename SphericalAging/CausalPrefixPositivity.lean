module

public import SphericalAging.CausalTreePositivity

public section

/-! Actual causal time-prefix centers preserve positivity, by the genuine
Volterra Picard construction and the closed leaf-label cone. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace SphericalAging.CausalPrefixPositivity
open CKSpecification CausalTree CausalTreeRealization CausalTreePositivity GreenCovariance
local instance (α : Type*) : DecidableEq α := Classical.decEq α

/-- The actual projected initial/white response feature is positive even when
the prefix lies strictly before the terminal time. -/
theorem ckBaseVector_prefix_nonnegative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (T : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Nonnegative (timePrefix T (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) t)) := by
  intro τ
  by_cases he : τ = CausalTree.Tree.leaf
  · subst τ
    rw [timePrefix_apply,fiberPrefix_leaf,fiberLabelIsometry_leaf]
    change LpProductTensor.Nonnegative (leafLabelIsometry (leafPrefix T
      (lp.single (E := fun τ : CausalTree.Tree (p-1) => (fiber τ).Carrier) 2 CausalTree.Tree.leaf
        (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) t) CausalTree.Tree.leaf)))
    rw [lp.single_apply_self]
    exact (leafLabel_nonnegative_iff _).mpr
      (leafPrefix_nonnegative T _ (leafResponseFeature_nonnegative h hb ht))
  · have hz : baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) t τ = 0 :=
      lp.single_apply_ne _ _ _ he
    rw [timePrefix_apply,hz,map_zero,map_zero]
    exact LpProductTensor.nonnegative_zero _

/-- True positivity at every projected Picard stage, using actual completed
prefix/grafting intertwining and Bochner integration of the closed cone. -/
theorem ckTreeIterate_prefix_nonnegative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (T : ℝ) (n : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    Nonnegative (timePrefix T (ckTreeIterate p β d (clampedResponse_continuous h) n t)) := by
  induction n generalizing t with
  | zero => exact ckBaseVector_prefix_nonnegative h hb T ht
  | succ n ih =>
    change Nonnegative (timePrefix T
      (baseVector (p-1) (clampedResponse d) (clampedResponse_continuous h) t+
      (β*Real.sqrt p) • ∫ u in (0 : ℝ)..max 0 t, clampedResponse d (max 0 t) u •
        graftPower (ckTreeIterate p β d (clampedResponse_continuous h) n u)))
    have hint : IntervalIntegrable (fun u => clampedResponse d t u •
        graftPower (ckTreeIterate p β d (clampedResponse_continuous h) n u)) volume 0 t :=
      treeIterate_integrable (p-1) (β*Real.sqrt p)
        (clampedResponse d) (clampedResponse_continuous h) n t 0 t
    rw [max_eq_right ht,timePrefix_add,timePrefix_smul,timePrefix_intervalIntegral T hint]
    apply nonnegative_add (ckBaseVector_prefix_nonnegative h hb T ht)
    apply nonnegative_smul (mul_nonneg h.beta_pos.le (Real.sqrt_nonneg _))
    have hc : Continuous (fun u => timePrefix T
        (clampedResponse d t u • graftPower (ckTreeIterate p β d (clampedResponse_continuous h) n u))) := by
      exact (timePrefixL (p-1) T).continuous.comp
        (((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)).smul
          ((graftPower_continuous (p-1)).comp
            (treeIterate_continuous (p-1) (β*Real.sqrt p) (clampedResponse d)
              (clampedResponse_continuous h) n)))
    have hi := hc.intervalIntegrable (μ := volume) 0 t
    apply nonnegative_intervalIntegral ht _ hi
    intro u hu
    rw [timePrefix_smul,timePrefix_graftPower]
    apply nonnegative_smul
    · rw [clampedResponse_eq hu.1 hu.2]
      exact hb.2 t u hu.1 hu.2
    · exact graftPower_nonnegative (ih hu.1)

/-- Positivity of the actual final prefix center follows by genuine strong
convergence, continuity of the prefix, and closedness of the function cone. -/
theorem ckTreeState_prefix_nonnegative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (T : ℝ)
    {t : ℝ} (ht : 0 ≤ t) : Nonnegative (timePrefix T (ckTreeState h t)) :=
  (nonnegative_isClosed (p-1)).mem_of_tendsto
    ((timePrefixL (p-1) T).continuous.tendsto _ |>.comp (ckTreeIterate_tendsto h hb ht))
    (Eventually.of_forall (fun n => ckTreeIterate_prefix_nonnegative h hb T n ht))

end SphericalAging.CausalPrefixPositivity
