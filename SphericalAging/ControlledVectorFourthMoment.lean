module

public import SphericalAging.ControlledVectorFourthLocalization

public section

/-! Removing genuine control-process stopping by pathwise continuity and Fatou. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ControlledVectorFourthMoment
open HardSphereDynamics PredictableDriftTime VectorIto ClosedHitStopping
  LinearSDELocalization VectorSourceFourthMoment ControlledVectorFourthLocalization
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N L : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem controlled_solution_fourthMoment (D : BrownianDriver N P F)
    (Y : ℝ≥0→Ω→State N) (hYa : StronglyAdapted F Y)
    (hYc : ∀omega,Continuous (fun t => Y t omega))
    (W : ℝ≥0→Ω→State L) (hWa : StronglyAdapted F W)
    (hWc : ∀omega,Continuous (fun t => W t omega))
    (R0 M C : ℝ≥0) (hW0 : ∀omega,‖W 0 omega‖≤R0)
    (hYW : ∀t omega,‖Y t omega‖≤‖W t omega‖) (T : ℝ≥0)
    (G : ℝ≥0×Ω→ℝ) (hG : Integrable G (nonnegativeLebesgueMeasure.prod P))
    (hGpos : ∀ᵐq∂nonnegativeLebesgueMeasure.prod P,0≤G q)
    (A : Fin N→PredictableProcessL2 F P) (U : Fin N→Fin N→PredictableProcessL2 F P)
    (hAsupport : ∀i,∀ᵐq∂nonnegativeLebesgueMeasure.prod P,q.1∉Ioc 0 T→(A i : TimeProcessL2 P) q=0)
    (hnoise : ∀i j,∀ᵐq∂nonnegativeLebesgueMeasure.prod P,
      ‖(U i j : TimeProcessL2 P) q‖≤(C:ℝ)*(1+‖W q.1 q.2‖)^2)
    (hproduction : ∀ᵐq∂nonnegativeLebesgueMeasure.prod P,q.1∈Ioc 0 T→
      fourthProduction (Y q.1 q.2) (fun i => (A i : TimeProcessL2 P) q)
        (fun i j => (U i j : TimeProcessL2 P) q)≤(M:ℝ)*‖Y q.1 q.2‖^4+G q)
    (heq : ∀t,t≤T→∀i,(fun omega => Y t omega i)=ᵐ[P] fun omega =>
      Y 0 omega i+driftVersion (A i) T t omega+vectorProcess D (U i) t omega)
    (t : ℝ≥0) (ht : t≤T) :
    MemLp (Y t) 4 P ∧ (∫omega,‖Y t omega‖^4∂P)≤
      ((∫omega,‖Y 0 omega‖^4∂P)+(∫q,G q∂nonnegativeLebesgueMeasure.prod P))*Real.exp ((M:ℝ)*t) := by
  classical
  let R (n : ℕ) : ℝ≥0 := R0+n+1
  have hR (n : ℕ) : R0≤R n := by
    change (R0:ℝ)≤(R0:ℝ)+(n:ℝ)+1
    have hn : (0:ℝ)≤n := by positivity
    linarith
  let Z (n : ℕ) : Ω→State N := stoppedState Y (radiusHit W T (R n)) t
  have hZm (n : ℕ) : AEStronglyMeasurable (Z n) P :=
    ((stoppedState_stronglyAdapted Y hYa hYc
      (isStoppingTime_radiusHit W hWa hWc T (R n)) t).mono (F.le t)).aestronglyMeasurable
  have hZb (n : ℕ) (omega : Ω) : ‖Z n omega‖≤R n :=
    (hYW _ _).trans (level_le_upTo_hit (fun r eta => ‖W r eta‖)
      (fun eta => (hWc eta).norm) T (R n) (fun eta => (hW0 eta).trans (hR n)) omega
      (min t (radiusHit W T (R n) omega)) (min_le_right _ _))
  have hZi (n : ℕ) : Integrable (fun omega => ‖Z n omega‖^4) P := by
    have hm : MemLp (Z n) 4 P := MemLp.of_bound (hZm n) (R n) (.of_forall (hZb n))
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat,Real.rpow_natCast] using hm.integrable_norm_rpow'
  have hlim : ∀ᵐomega∂P,Tendsto (fun n => Z n omega) atTop (𝓝 (Y t omega)) := .of_forall (fun omega => by
    obtain ⟨B,hB⟩ := (isCompact_Icc (a:=(0:ℝ≥0)) (b:=T)).exists_bound_of_continuousOn
      ((hWc omega).norm.continuousOn)
    obtain ⟨n,hn⟩ := exists_nat_gt B
    have hev : ∀ᶠk:ℕ in atTop,Z k omega=Y t omega := by
      filter_upwards [eventually_ge_atTop n] with k hk
      have hk' : (n:ℝ)≤k := by exact_mod_cast hk
      have hBR : B<R k := by
        change B<(R0:ℝ)+(k:ℝ)+1
        nlinarith [R0.coe_nonneg]
      have hτ : radiusHit W T (R k) omega=T := radiusHit_eq_horizon_of_bound W hWc T (R k) omega
        (fun r hr => by
          have hh := hB r ⟨bot_le,hr⟩
          rw [Real.norm_of_nonneg (norm_nonneg _)] at hh
          exact hh.trans_lt hBR)
      simp only [Z,stoppedState,hτ,min_eq_left ht]
    exact tendsto_const_nhds.congr' (hev.mono (fun _ hh => hh.symm)))
  let B : ℝ := ((∫omega,‖Y 0 omega‖^4∂P)+(∫q,G q∂nonnegativeLebesgueMeasure.prod P))*Real.exp ((M:ℝ)*t)
  have hB : 0≤B := mul_nonneg
    (add_nonneg (integral_nonneg (fun _ => by positivity)) (integral_nonneg_of_ae hGpos))
    (Real.exp_pos _).le
  have hi := fourthMoment_of_ae_tendsto Z (Y t) B hB hZm
    ((hYa t).mono (F.le t)).aestronglyMeasurable hZi
    (fun n => controlled_stopped_fourthMoment D Y hYa hYc W hWa hWc R0 M C hW0 hYW
      T G hG hGpos A U hAsupport hnoise hproduction heq (R n) (hR n) t ht) hlim
  refine ⟨?_,hi.2⟩
  apply (integrable_norm_rpow_iff ((hYa t).mono (F.le t)).aestronglyMeasurable
    (by norm_num : (4:ℝ≥0∞)≠0) (by norm_num : (4:ℝ≥0∞)≠∞)).mp
  simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat,Real.rpow_natCast] using hi.1

end SphericalAging.ControlledVectorFourthMoment
