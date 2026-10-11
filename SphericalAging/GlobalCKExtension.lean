module

public import SphericalAging.FiniteResponseComparison

public section

/-! Harmless globally continuous extensions of a physical CK solution.
These are only asserted to satisfy the actual CK equations on finite physical
horizons. Clamping does not assert an equation at negative times. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalAging.GlobalCKExtension
open CKSpecification GreenCovariance BackwardResponse CKLocalExistence
open FiniteGreenCovarianceClosure CovarianceIteration

@[expose] def clampedData (d : CKData) : CKData where
  C := clampedCorrelation d
  R := clampedResponse d
  multiplier := clampedMultiplier d

theorem clampedResponse_idempotent (d : CKData) (t u : ℝ) :
    clampedResponse (clampedData d) t u=clampedResponse d t u := by
  simp only [clampedResponse,clampedData,max_eq_right (le_max_left (0 : ℝ) u),
    max_eq_left (le_max_right t (max 0 u))]

theorem responseSlope_continuous_of_data (p : ℕ) (β : ℝ) (d : CKData)
    (hC : Continuous (Function.uncurry d.C)) (hR : Continuous (Function.uncurry d.R))
    (hLam : Continuous d.multiplier) : Continuous (Function.uncurry (responseSlope p β d)) := by
  unfold responseSlope xiDoublePrime
  apply Continuous.add
  · exact (hLam.comp continuous_fst).neg.mul hR
  · apply continuous_const.mul
    apply continuous_integral_endpoints
    · exact ((((continuous_const.mul continuous_const).mul
        ((hC.comp (continuous_fst.fst.prodMk continuous_snd)).pow _)).mul
        (hR.comp (continuous_fst.fst.prodMk continuous_snd))).mul
        (hR.comp (continuous_snd.prodMk continuous_fst.snd)))
    · exact continuous_snd
    · exact continuous_fst

theorem correlationSlope_continuous_of_data (p : ℕ) (β : ℝ) (d : CKData)
    (hC : Continuous (Function.uncurry d.C)) (hR : Continuous (Function.uncurry d.R))
    (hLam : Continuous d.multiplier) : Continuous (Function.uncurry (correlationSlope p β d)) := by
  unfold correlationSlope xiDoublePrime xiPrime
  apply Continuous.add
  · apply Continuous.add
    · exact (hLam.comp continuous_fst).neg.mul hC
    · apply continuous_const.mul
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      · exact ((((continuous_const.mul continuous_const).mul
          ((hC.comp (continuous_fst.fst.prodMk continuous_snd)).pow _)).mul
          (hR.comp (continuous_fst.fst.prodMk continuous_snd))).mul
          (hC.comp (continuous_snd.prodMk continuous_fst.snd)))
      · exact continuous_fst
  · apply continuous_const.mul
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · exact (continuous_const.mul
        ((hC.comp (continuous_fst.fst.prodMk continuous_snd)).pow _)).mul
        (hR.comp (continuous_fst.snd.prodMk continuous_snd))
    · exact continuous_snd

theorem memoryMass_clampedData (p : ℕ) (d : CKData) {t : ℝ} (ht : 0 ≤ t) :
    memoryMass p (clampedData d) t=memoryMass p d t := by
  unfold memoryMass clampedData
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  dsimp
  rw [clampedCorrelation_eq ht hu.1,clampedResponse_eq hu.1 hu.2]

theorem responseSlope_clampedData (p : ℕ) (β : ℝ) (d : CKData) {t s : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    responseSlope p β (clampedData d) t s=responseSlope p β d t s := by
  unfold responseSlope
  dsimp only [clampedData, clampedMultiplier]
  rw [max_eq_right (hs.trans hst),clampedResponse_eq hs hst]
  congr 1
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hst] at hu
  dsimp
  rw [clampedCorrelation_eq (hs.trans hst) (hs.trans hu.1),
    clampedResponse_eq (hs.trans hu.1) hu.2,clampedResponse_eq hs hu.1]

theorem correlationSlope_clampedData (p : ℕ) (β : ℝ) (d : CKData) {t s : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    correlationSlope p β (clampedData d) t s=correlationSlope p β d t s := by
  have ht := hs.trans hst
  unfold correlationSlope
  dsimp only [clampedData, clampedMultiplier]
  rw [max_eq_right ht,clampedCorrelation_eq ht hs]
  congr 1
  · congr 1
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp
    rw [clampedCorrelation_eq ht hu.1,clampedResponse_eq hu.1 hu.2,
      clampedCorrelation_eq hu.1 hs]
  · congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hs] at hu
    dsimp
    rw [clampedCorrelation_eq ht hu.1,clampedResponse_eq hu.1 hu.2]

/-- The globally clamped functions satisfy exactly the original CK equations
on every finite physical horizon, with globally continuous harmless values
outside it. -/
theorem clampedData_on_horizon {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKEquations p β d) (hT : 0 < T) : CKOnHorizon p β T (clampedData d) := by
  have hC := clampedCorrelation_continuous h
  have hR := clampedResponse_continuous h
  have hLam := clampedMultiplier_continuous h
  refine ⟨h.spin_ge_three,h.beta_pos,hT,hC,hR,hLam,?_,?_,?_,?_,?_,?_,
    correlationSlope_continuous_of_data p β (clampedData d) hC hR hLam,
    responseSlope_continuous_of_data p β (clampedData d) hC hR hLam⟩
  · intro t s
    exact h.correlation_symmetric _ _ (le_max_left _ _) (le_max_left _ _)
  · intro t ht
    change clampedCorrelation d t t=1
    rw [clampedCorrelation_eq ht.1 ht.1]
    exact h.correlation_diagonal t ht.1
  · intro t ht
    change clampedResponse d t t=1
    rw [clampedResponse_eq ht.1 (le_refl t)]
    exact h.response_diagonal t ht.1
  · intro t ht
    change clampedMultiplier d t=1+β^2*(p : ℝ)^2*memoryMass p (clampedData d) t
    rw [memoryMass_clampedData p d ht.1]
    unfold clampedMultiplier
    rw [max_eq_right ht.1]
    exact h.multiplier_eq t ht.1
  · intro t ht s hs
    rw [correlationSlope_clampedData p β d hs.1 hs.2]
    apply ((h.correlation_derivative t s hs.1 hs.2).mono
      (fun x hx => hx.1)).congr_of_mem
    · intro x hx
      exact clampedCorrelation_eq (hs.1.trans hx.1) hs.1
    · exact ⟨hs.2,ht.2⟩
  · intro t ht s hs
    rw [responseSlope_clampedData p β d hs.1 hs.2]
    apply ((h.response_derivative t s hs.1 hs.2).mono
      (fun x hx => hx.1)).congr_of_mem
    · intro x hx
      exact clampedResponse_eq hs.1 hx.1
    · exact ⟨hs.2,ht.2⟩

theorem clampedData_nonnegative {T : ℝ} {d : CKData} (hb : PhysicalBounds d) :
    NonnegativeOnHorizon T (clampedData d) := by
  constructor
  · intro t ht s hs
    exact clampedCorrelation_nonnegative hb t s
  · intro t ht s hs
    exact clampedResponse_nonnegative hb t s

/-- Every height iterate is unchanged by the harmless extension, because
causal response clamping is idempotent. -/
theorem covarianceIterate_clampedData (p : ℕ) (β : ℝ) (d : CKData) (n : ℕ) :
    covarianceIterate p β (clampedData d) n=covarianceIterate p β d n := by
  have hr : clampedResponse (clampedData d)=clampedResponse d := by
    funext t u
    exact clampedResponse_idempotent d t u
  have hbase : baseCovariance (clampedData d)=baseCovariance d := by
    funext t s
    unfold baseCovariance initialTerm whiteTerm
    rw [hr]
  induction n with
  | zero => exact hbase
  | succ n ih =>
    change covarianceMap p β (clampedData d) (covarianceIterate p β (clampedData d) n)=_
    rw [ih]
    funext t s
    unfold covarianceMap coloredCovariance
    rw [hbase,hr]
    rfl

/-- Original global CK covariance iterates converge uniformly on every
physical compact square. The globally clamped extension is used only to
instantiate the already proved finite-horizon theorem. -/
theorem global_covarianceIterate_tendstoUniformlyOn {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (hT : 0 < T) :
    TendstoUniformlyOn (fun n => Function.uncurry (covarianceIterate p β d n))
      (Function.uncurry d.C) atTop (Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) T) := by
  have hc := covarianceIterate_tendstoUniformlyOn (clampedData_on_horizon h hT)
    (clampedData_nonnegative hb)
  rw [Metric.tendstoUniformlyOn_iff] at hc ⊢
  intro ε hε
  filter_upwards [hc ε hε] with n hn z hz
  have hh := hn z hz
  rw [covarianceIterate_clampedData] at hh
  change dist (clampedCorrelation d z.1 z.2) (covarianceIterate p β d n z.1 z.2)<ε at hh
  rw [clampedCorrelation_eq hz.1.1 hz.2.1] at hh
  exact hh

theorem global_covarianceIterate_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Tendsto (fun n => covarianceIterate p β d n t s) atTop (𝓝 (d.C t s)) := by
  let T := max 1 (max t s)
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  exact (global_covarianceIterate_tendstoUniformlyOn h hb hT).tendsto_at
    (show (t,s) ∈ Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) T from
      ⟨⟨ht,(le_max_left t s).trans (le_max_right _ _)⟩,
        ⟨hs,(le_max_right t s).trans (le_max_right _ _)⟩⟩)

/-- All finite Gram matrices of a global physical CK correlation are
positive semidefinite, by the actual covariance iteration and its limit. -/
theorem global_correlation_psd {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) : PositiveSemidefiniteCorrelation d := by
  intro n times weights htimes
  let T : ℝ := 1+∑ i, |times i|
  have hsum : 0 ≤ ∑ i, |times i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hT : 0 < T := by dsimp [T]; linarith
  have hmem : ∀ i, times i ∈ Icc 0 T := by
    intro i
    have hi : |times i| ≤ ∑ j, |times j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (times j)) (Finset.mem_univ i)
    exact ⟨htimes i, by dsimp [T]; linarith [le_abs_self (times i)]⟩
  have hg := CovariancePSD.correlation_psd (clampedData_on_horizon h hT)
    (clampedData_nonnegative hb) n times weights hmem
  convert hg using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change _=weights i*weights j*clampedCorrelation d (times i) (times j)
  rw [clampedCorrelation_eq (htimes i) (htimes j)]

/-- Global iteration retains the entrywise physical bound at every height. -/
theorem global_covarianceIterate_bounds {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (n : ℕ)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    0 ≤ covarianceIterate p β d n t s ∧ covarianceIterate p β d n t s ≤ d.C t s := by
  let T := max 1 (max t s)
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have htT : t ∈ Icc 0 T := ⟨ht,(le_max_left t s).trans (le_max_right _ _)⟩
  have hsT : s ∈ Icc 0 T := ⟨hs,(le_max_right t s).trans (le_max_right _ _)⟩
  have hg := covarianceIterate_bounds (clampedData_on_horizon h hT)
    (clampedData_nonnegative hb) n t htT s hsT
  rw [covarianceIterate_clampedData] at hg
  change 0 ≤ covarianceIterate p β d n t s ∧
    covarianceIterate p β d n t s ≤ clampedCorrelation d t s at hg
  rw [clampedCorrelation_eq ht hs] at hg
  exact hg

/-- Every covariance iterate is genuinely continuous on the full extended
plane; its physical values and convergence are unchanged by clamping. -/
theorem global_covarianceIterate_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (n : ℕ) :
    Continuous (Function.uncurry (covarianceIterate p β d n)) := by
  have hg := covarianceIterate_continuous (clampedData_on_horizon h (T := 1) (by norm_num)) n
  rw [covarianceIterate_clampedData] at hg
  exact hg

end SphericalAging.GlobalCKExtension
