module

public import SphericalAging.UnitRegularTreeGeometry

public section

/-! Recursive exactification of the actual approximate local tree. Each new
child is constructed from its original local Gram entries at the corrected
parent; no exact configuration is assumed. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.RegularTreeExactification
open FiniteModel RegularTreeEnergyTelescoping UnitRegularTreeGeometry
open UniformOrthogonalForkExactification ApproximateForkMovedBase
open scoped InnerProductSpace
variable {N K : ℕ}

theorem exists_correction_at_root (hKN : K<N) (qmin η : ℝ) (hmin : 0<qmin)
    (hη : 0≤η) (q e : ℕ→ℝ) (hq : Monotone q) (hqlow : ∀l,qmin≤q l)
    (he : ∀l,0≤e l) (d : ℕ)
    (hstep : ∀l,l<d→e (l+1)=error K (3*η+2*e l))
    (hbaseSmall : ∀l,l<d→Real.sqrt (3*η+2*e l)≤qmin)
    (hsmall : ∀l,l<d→4*((K+1:ℕ):ℝ)*Real.sqrt (3*η+2*e l)≤1)
    (z : TreeData (Vector N) K d) (hz : ApproximateTree q η d z)
    (τ : Vector N) (hτ : ‖τ‖^2=q 0) (hclose : ‖τ-root d z‖≤e 0) :
    ∃w : TreeData (Vector N) K d,
      ExactTree q d w ∧ TreeDistance e d z w ∧ root d w=τ := by
  classical
  induction d generalizing q e τ with
  | zero => exact ⟨τ,hτ,hclose,rfl⟩
  | succ d ih =>
    have hball (i : Fin K) : ‖root d (z.2 i)‖≤1 :=
      approximate_root_ball _ η d _ (hz.2.2.2.2 i)
    have hnorm (i : Fin K) : |‖root d (z.2 i)‖^2-q 1|≤η :=
      approximate_root_norm (fun l => q (l+1)) η d _ (hz.2.2.2.2 i)
    obtain ⟨t,htn,htx,htt,htclose⟩ := actual_moved_base_exactification hKN z.1 τ
      (fun i => root d (z.2 i)) qmin (q 0) (q 1) η (e 0) hmin (hqlow 0)
      (hq (by omega : 0≤1)) hη (he 0) hτ hball hclose hnorm hz.2.2.1 hz.2.2.2.1
      (hbaseSmall 0 (by omega)) (hsmall 0 (by omega))
    have hchildren (i : Fin K) : ∃w : TreeData (Vector N) K d,
        ExactTree (fun l => q (l+1)) d w ∧
        TreeDistance (fun l => e (l+1)) d (z.2 i) w ∧ root d w=t i := by
      apply ih (fun l => q (l+1)) (fun l => e (l+1))
        (fun a b hab => hq (Nat.add_le_add_right hab 1)) (fun l => hqlow (l+1))
        (fun l => he (l+1))
      · intro l hl
        exact hstep (l+1) (by omega)
      · intro l hl
        exact hbaseSmall (l+1) (by omega)
      · intro l hl
        exact hsmall (l+1) (by omega)
      · exact hz.2.2.2.2 i
      · exact htn i
      · simpa only [hstep 0 (by omega),Nat.zero_add] using htclose i
    choose w hw using hchildren
    refine ⟨(τ,w),?_,?_,rfl⟩
    · simp only [ExactTree]
      refine ⟨hτ,?_,?_,?_,fun i => (hw i).1⟩
      · intro i;rw [(hw i).2.2];exact htn i
      · intro i;rw [(hw i).2.2];exact htx i
      · intro i j hij;rw [(hw i).2.2,(hw j).2.2];exact htt i j hij
    · exact ⟨hclose,fun i => (hw i).2.1⟩

end SphericalAging.RegularTreeExactification
