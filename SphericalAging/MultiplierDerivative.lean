module

public import SphericalAging.ResponseCompactness

public section

/-! Actual differentiation of CK energy memory and its multiplier.
All differentiation hypotheses below are derived from the CK equations. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace SphericalAging.MultiplierDerivative
open CKSpecification GreenCovariance GreenCovarianceClosure BackwardResponse
open CKPhysicalConsequences

/-- The correlation row extended constantly at its own causal diagonal. -/
@[expose] def causalCorrelation (d : CKData) (t u : ℝ) : ℝ :=
  d.C (max t (max 0 u)) (max 0 u)

@[expose] def causalCorrelationSlope (p : ℕ) (β : ℝ) (d : CKData) (t u : ℝ) : ℝ :=
  correlationSlope p β d (max t (max 0 u)) (max 0 u)

@[expose] def memoryDensity (p : ℕ) (d : CKData) (t u : ℝ) : ℝ :=
  causalCorrelation d t u^(p-1)*clampedResponse d t u

@[expose] def memoryDensitySlope (p : ℕ) (β : ℝ) (d : CKData) (t u : ℝ) : ℝ :=
  ((p-1 : ℕ) : ℝ)*causalCorrelation d t u^(p-2)*causalCorrelationSlope p β d t u*
    clampedResponse d t u+
    causalCorrelation d t u^(p-1)*clampedResponseSlope p β d t u

theorem causalCorrelation_eq {d : CKData} {t u : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) :
    causalCorrelation d t u=d.C t u := by
  simp [causalCorrelation,max_eq_right hu,max_eq_left hut]

theorem causalCorrelationSlope_eq {p : ℕ} {β : ℝ} {d : CKData} {t u : ℝ}
    (hu : 0 ≤ u) (hut : u ≤ t) :
    causalCorrelationSlope p β d t u=correlationSlope p β d t u := by
  simp [causalCorrelationSlope,max_eq_right hu,max_eq_left hut]

theorem causalCorrelation_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (causalCorrelation d)) :=
  h.correlation_continuous.comp_continuous
    (show Continuous (fun z : ℝ × ℝ => (max z.1 (max 0 z.2),max 0 z.2)) by fun_prop)
    (fun z => ⟨(le_max_left 0 z.2).trans (le_max_right z.1 (max 0 z.2)),le_max_left 0 z.2⟩)

theorem causalCorrelationSlope_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (causalCorrelationSlope p β d)) :=
  h.correlation_slope_continuous.comp_continuous
    (show Continuous (fun z : ℝ × ℝ => (max z.1 (max 0 z.2),max 0 z.2)) by fun_prop)
    (fun z => ⟨le_max_left 0 z.2,le_max_right z.1 (max 0 z.2)⟩)

theorem memoryDensity_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (memoryDensity p d)) :=
  ((causalCorrelation_continuous h).pow (p-1)).mul (clampedResponse_continuous h)

theorem memoryDensitySlope_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (memoryDensitySlope p β d)) :=
  (((continuous_const.mul ((causalCorrelation_continuous h).pow (p-2))).mul
      (causalCorrelationSlope_continuous h)).mul (clampedResponse_continuous h)).add
    (((causalCorrelation_continuous h).pow (p-1)).mul (clampedResponseSlope_continuous h))

theorem memoryDensitySlope_eq {p : ℕ} {β : ℝ} {d : CKData} {t u : ℝ}
    (hu : 0 ≤ u) (hut : u ≤ t) :
    memoryDensitySlope p β d t u=((p-1 : ℕ) : ℝ)*d.C t u^(p-2)*
      correlationSlope p β d t u*d.R t u+d.C t u^(p-1)*responseSlope p β d t u := by
  rw [memoryDensitySlope,causalCorrelation_eq hu hut,causalCorrelationSlope_eq hu hut,
    clampedResponse_eq hu hut,clampedResponseSlope_eq hu hut]

theorem physicalDensity_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t u : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) :
    HasDerivWithinAt (fun x => d.C x u^(p-1)*d.R x u)
      (memoryDensitySlope p β d t u) (Ici u) t := by
  have hd := ((h.correlation_derivative t u hu hut).pow (p-1)).mul
    (h.response_derivative t u hu hut)
  rw [memoryDensitySlope_eq hu hut]
  convert hd using 1

theorem memoryDensity_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t u : ℝ} (hu : 0 ≤ u) (hut : u < t) :
    HasDerivAt (fun x => memoryDensity p d x u) (memoryDensitySlope p β d t u) t := by
  have hd := (physicalDensity_hasDerivWithinAt h hu hut.le).hasDerivAt (Ici_mem_nhds hut)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hut] with x hx
  rw [memoryDensity,causalCorrelation_eq hu hx.le,clampedResponse_eq hu hx.le]

theorem memoryDensity_integral_eq {p : ℕ} {d : CKData} {t : ℝ} (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t,memoryDensity p d t u)=memoryMass p d t := by
  unfold memoryMass
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  rw [memoryDensity,causalCorrelation_eq hu.1 hu.2,clampedResponse_eq hu.1 hu.2]

/-- Actual moving-upper-limit Leibniz rule for the nonlinear CK memory.
Only a pointwise positive time is required; no derivative of λ is assumed. -/
theorem memoryMass_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (memoryMass p d)
      (1+∫ u in (0 : ℝ)..t,memoryDensitySlope p β d t u) t := by
  have hDrow : Continuous (fun u => memoryDensitySlope p β d t u) :=
    (memoryDensitySlope_continuous h).comp (continuous_const.prodMk continuous_id)
  obtain ⟨M₀,hM₀⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (show ContinuousOn (Function.uncurry (memoryDensitySlope p β d))
      (Icc (0 : ℝ) (t+1) ×ˢ Icc (0 : ℝ) (t+1)) from
      (memoryDensitySlope_continuous h).continuousOn)
  let M : ℝ≥0 := ⟨max M₀ 0,le_max_right M₀ 0⟩
  have hLip : ∀ u ∈ Icc 0 t, LipschitzOnWith M (fun x => memoryDensity p d x u) (Iic (t+1)) := by
    intro u hu
    have hc := causal_clamp_lipschitzOn (f := fun x => d.C x u^(p-1)*d.R x u)
      (f' := fun x => memoryDensitySlope p β d x u) (M := M) (a := u) (r := t+1)
      (by linarith [hu.2])
      (fun x hx => physicalDensity_hasDerivWithinAt h hu.1 hx.1)
      (fun x hx => (hM₀ (x,u) ⟨⟨hu.1.trans hx.1,hx.2⟩,⟨hu.1,by linarith [hu.2]⟩⟩).trans
        (le_max_left M₀ 0))
    convert hc using 1
    funext x
    simp only [memoryDensity,causalCorrelation,clampedResponse,max_eq_right hu.1]
  have hd := moving_integral_hasDerivAt_of_lipschitz (memoryDensity_continuous h) hDrow ht.le
    (Iic_mem_nhds (by linarith : t < t+1)) hLip
    (fun u hu => memoryDensity_hasDerivAt h hu.1 hu.2)
  have hdiag : memoryDensity p d t t=1 := by
    rw [memoryDensity,causalCorrelation_eq ht.le (le_refl t),clampedResponse_eq ht.le (le_refl t),
      h.correlation_diagonal t ht.le,h.response_diagonal t ht.le,one_pow,one_mul]
  rw [hdiag] at hd
  apply (show HasDerivAt (fun x => ∫ u in (0 : ℝ)..x,memoryDensity p d x u)
    (1+∫ u in (0 : ℝ)..t,memoryDensitySlope p β d t u) t by convert hd using 1; ring).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with x hx
  exact (memoryDensity_integral_eq hx.le).symm

theorem multiplier_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 < t) :
    HasDerivAt d.multiplier (β^2*(p : ℝ)^2*
      (1+∫ u in (0 : ℝ)..t,memoryDensitySlope p β d t u)) t := by
  have hd := ((memoryMass_hasDerivAt h ht).const_mul (β^2*(p : ℝ)^2)).const_add 1
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with x hx
  exact h.multiplier_eq x hx.le

@[expose] def lowerWeight (p : ℕ) (d : CKData) (t u : ℝ) : ℝ :=
  clampedResponse d t u*clampedCorrelation d t u^(p-2)

@[expose] def powerWeight (p : ℕ) (d : CKData) (t u : ℝ) : ℝ := clampedCorrelation d t u^(p-1)

@[expose] def mixedMoment (p : ℕ) (d : CKData) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..t,
    clampedResponse d t u*clampedResponse d t v*clampedCorrelation d t u^(p-2)*
      clampedCorrelation d t v^(p-2)*clampedCorrelation d u v

@[expose] def nestedMoment (p : ℕ) (d : CKData) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, lowerWeight p d t u*
    (∫ v in (0 : ℝ)..u,powerWeight p d t v*clampedResponse d u v)

@[expose] def firstRowMoment (p : ℕ) (d : CKData) (t u : ℝ) : ℝ :=
  lowerWeight p d t u*(∫ v in (0 : ℝ)..t,lowerWeight p d t v*clampedCorrelation d v u)

@[expose] def secondRowMoment (p : ℕ) (d : CKData) (t u : ℝ) : ℝ :=
  lowerWeight p d t u*(∫ v in (0 : ℝ)..u,powerWeight p d t v*clampedResponse d u v)

@[expose] def thirdRowMoment (p : ℕ) (d : CKData) (t u : ℝ) : ℝ :=
  powerWeight p d t u*(∫ v in u..t,lowerWeight p d t v*clampedResponse d v u)

theorem lowerWeight_continuous {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) :
    Continuous (Function.uncurry (lowerWeight p d)) :=
  (clampedResponse_continuous h).mul ((clampedCorrelation_continuous h).pow (p-2))

theorem powerWeight_continuous {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) :
    Continuous (Function.uncurry (powerWeight p d)) :=
  (clampedCorrelation_continuous h).pow (p-1)

theorem firstRowMoment_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t : ℝ) : Continuous (firstRowMoment p d t) :=
  ((lowerWeight_continuous h).comp (continuous_const.prodMk continuous_id)).mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (((lowerWeight_continuous h).comp (continuous_const.prodMk continuous_snd)).mul
        ((clampedCorrelation_continuous h).comp (continuous_snd.prodMk continuous_fst))) 0 t)

theorem secondRowMoment_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t : ℝ) : Continuous (secondRowMoment p d t) :=
  ((lowerWeight_continuous h).comp (continuous_const.prodMk continuous_id)).mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (((powerWeight_continuous h).comp (continuous_const.prodMk continuous_snd)).mul
        (clampedResponse_continuous h)) continuous_id)

theorem thirdRowMoment_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t : ℝ) : Continuous (thirdRowMoment p d t) :=
  ((powerWeight_continuous h).comp (continuous_const.prodMk continuous_id)).mul
    (continuous_integral_endpoints
      (((lowerWeight_continuous h).comp (continuous_const.prodMk continuous_snd)).mul
        ((clampedResponse_continuous h).comp continuous_swap)) continuous_id continuous_const)

theorem clampedMemory_lowerWeight (p : ℕ) (β : ℝ) (d : CKData) (t u : ℝ) :
    clampedMemory p β d t u=β^2*(p : ℝ)*((p : ℝ)-1)*lowerWeight p d t u := by
  unfold clampedMemory xiDoublePrime lowerWeight
  ring

theorem coloredForcing_powerWeight (p : ℕ) (β : ℝ) (d : CKData) (u t : ℝ) :
    coloredForcing p β d u t=β^2*(p : ℝ)*
      (∫ v in (0 : ℝ)..u,powerWeight p d t v*clampedResponse d u v) := by
  unfold coloredForcing powerWeight
  congr 1
  apply intervalIntegral.integral_congr
  intro v _
  ring

theorem memoryDensitySlope_linear {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t u : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) :
    memoryDensitySlope p β d t u=
      (-(p : ℝ)*d.multiplier t)*(powerWeight p d t u*clampedResponse d t u)+
      (β^2*(p : ℝ)*((p : ℝ)-1)^2)*firstRowMoment p d t u+
      (β^2*(p : ℝ)*((p : ℝ)-1))*secondRowMoment p d t u+
      (β^2*(p : ℝ)*((p : ℝ)-1))*thirdRowMoment p d t u := by
  rw [memoryDensitySlope_eq hu hut,correlationSlope_linear (hu.trans hut) hu,
    responseSlope_linear_memory hu hut,←clampedCorrelation_eq (hu.trans hut) hu,
    ←clampedResponse_eq hu hut,coloredForcing_powerWeight]
  have hp1 : 1 ≤ p := by have hh := h.spin_ge_three; omega
  have hcast : ((p-1 : ℕ) : ℝ)=(p : ℝ)-1 := by
    rw [Nat.cast_sub hp1,Nat.cast_one]
  have hpow : clampedCorrelation d t u^(p-1)=clampedCorrelation d t u^(p-2)*clampedCorrelation d t u := by
    rw [show p-1=(p-2)+1 by have hp := h.spin_ge_three; omega,pow_succ]
  simp_rw [clampedMemory_lowerWeight,mul_assoc,intervalIntegral.integral_const_mul]
  unfold firstRowMoment secondRowMoment thirdRowMoment lowerWeight powerWeight
  rw [hcast,hpow]
  ring

theorem firstRowMoment_integral {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t : ℝ) :
    (∫ u in (0 : ℝ)..t,firstRowMoment p d t u)=mixedMoment p d t := by
  unfold firstRowMoment mixedMoment
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  have hsym : clampedCorrelation d v u=clampedCorrelation d u v :=
    h.correlation_symmetric _ _ (le_max_left _ _) (le_max_left _ _)
  rw [hsym]
  unfold lowerWeight
  ring

theorem thirdRowMoment_integral {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t,thirdRowMoment p d t u)=nestedMoment p d t := by
  have hSigma : Continuous (Function.uncurry (lowerWeight p d)) := lowerWeight_continuous h
  have hA : Continuous (powerWeight p d t) :=
    (powerWeight_continuous h).comp (continuous_const.prodMk continuous_id)
  have hh := TriangleUniqueness.weighted_triangle_memory_diagonal (clampedResponse_continuous h)
    hSigma hA ht
  unfold thirdRowMoment nestedMoment
  rw [hh]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  congr 1
  apply intervalIntegral.integral_congr
  intro v _
  ring

theorem integral_four_linear_combinations {F G H J : ℝ → ℝ} {a b : ℝ}
    (hF : Continuous F) (hG : Continuous G) (hH : Continuous H) (hJ : Continuous J)
    (c₁ c₂ c₃ c₄ : ℝ) :
    (∫ u in a..b,c₁*F u+c₂*G u+c₃*H u+c₄*J u)=
      c₁*(∫ u in a..b,F u)+c₂*(∫ u in a..b,G u)+
        c₃*(∫ u in a..b,H u)+c₄*(∫ u in a..b,J u) := by
  rw [intervalIntegral.integral_add
    (f := fun u => c₁*F u+c₂*G u+c₃*H u) (g := fun u => c₄*J u)
    ((((hF.const_mul c₁).add (hG.const_mul c₂)).add (hH.const_mul c₃)).intervalIntegrable a b)
    ((hJ.const_mul c₄).intervalIntegrable a b),
    intervalIntegral.integral_add (f := fun u => c₁*F u+c₂*G u) (g := fun u => c₃*H u)
      (((hF.const_mul c₁).add (hG.const_mul c₂)).intervalIntegrable a b)
      ((hH.const_mul c₃).intervalIntegrable a b),
    intervalIntegral.integral_add (f := fun u => c₁*F u) (g := fun u => c₂*G u)
      ((hF.const_mul c₁).intervalIntegrable a b)
      ((hG.const_mul c₂).intervalIntegrable a b)]
  simp only [intervalIntegral.integral_const_mul]

/-- The exact two-moment formula for the derivative of the memory, including
its actual triangular Fubini reduction. -/
theorem memoryDensitySlope_integral {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t,memoryDensitySlope p β d t u)=
      -(p : ℝ)*d.multiplier t*memoryMass p d t+
        β^2*(p : ℝ)*((p : ℝ)-1)^2*mixedMoment p d t+
        2*β^2*(p : ℝ)*((p : ℝ)-1)*nestedMoment p d t := by
  have hmass : Continuous (fun u => powerWeight p d t u*clampedResponse d t u) :=
    ((powerWeight_continuous h).comp (continuous_const.prodMk continuous_id)).mul
      ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id))
  have he : (∫ u in (0 : ℝ)..t,memoryDensitySlope p β d t u)=
      ∫ u in (0 : ℝ)..t,
        (-(p : ℝ)*d.multiplier t)*(powerWeight p d t u*clampedResponse d t u)+
        (β^2*(p : ℝ)*((p : ℝ)-1)^2)*firstRowMoment p d t u+
        (β^2*(p : ℝ)*((p : ℝ)-1))*secondRowMoment p d t u+
        (β^2*(p : ℝ)*((p : ℝ)-1))*thirdRowMoment p d t u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    exact memoryDensitySlope_linear h hu.1 hu.2
  rw [he,integral_four_linear_combinations hmass (firstRowMoment_continuous h t)
    (secondRowMoment_continuous h t) (thirdRowMoment_continuous h t),
    firstRowMoment_integral h t,thirdRowMoment_integral h ht]
  have hm : (∫ u in (0 : ℝ)..t,powerWeight p d t u*clampedResponse d t u)=memoryMass p d t := by
    unfold powerWeight memoryMass
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp only
    rw [clampedCorrelation_eq ht hu.1,clampedResponse_eq hu.1 hu.2]
  rw [hm]
  unfold secondRowMoment nestedMoment
  ring

/-- Actual λ derivative, ready for the two genuine Hilbert moment bounds. -/
theorem multiplier_two_moment_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 < t) :
    HasDerivAt d.multiplier (β^2*(p : ℝ)^2*
      (1-(p : ℝ)*d.multiplier t*memoryMass p d t+
        β^2*(p : ℝ)*((p : ℝ)-1)^2*mixedMoment p d t+
        2*β^2*(p : ℝ)*((p : ℝ)-1)*nestedMoment p d t)) t := by
  have hd := multiplier_hasDerivAt h ht
  rw [memoryDensitySlope_integral h ht.le] at hd
  convert hd using 1
  ring

end SphericalAging.MultiplierDerivative
