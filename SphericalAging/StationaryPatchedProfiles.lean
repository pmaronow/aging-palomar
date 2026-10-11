module

public import SphericalAging.StationaryCorrectedCriticalProfiles

public section

/-! Actual patched comparison profiles for critical endpoint bounds. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryPatchedProfiles
noncomputable section
open StationaryNormalization StationaryPowerProfiles StationaryComparison

@[expose] def joinAt (T : ℝ) (f g : ℝ → ℝ) (s : ℝ) : ℝ := if s≤T then f s else g s

theorem joinAt_left (T : ℝ) (f g : ℝ → ℝ) (s : ℝ) (hs : s≤T) : joinAt T f g s=f s := ite_eq_left hs

theorem joinAt_right (T : ℝ) (f g : ℝ → ℝ) (s : ℝ) (hs : T<s) : joinAt T f g s=g s := ite_eq_right (not_le.mpr hs)

theorem joinAt_deriv_left (T : ℝ) (f g : ℝ → ℝ) (s : ℝ) (hs : s<T) :
    deriv (joinAt T f g) s=deriv f s := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Iio_mem_nhds hs] with x hx
  exact joinAt_left T f g x hx.le

theorem joinAt_deriv_right (T : ℝ) (f g : ℝ → ℝ) (s : ℝ) (hs : T<s) :
    deriv (joinAt T f g) s=deriv g s := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds hs] with x hx
  exact joinAt_right T f g x hx

/-- Genuine monotonicity across the join follows from matching endpoint
values; a derivative sign is not assumed for the patched profile. -/
theorem joinAt_antitone (T : ℝ) (f g : ℝ → ℝ) (hT : 0≤T)
    (hf : AntitoneOn f (Icc 0 T)) (hg : AntitoneOn g (Ici T)) (hmatch : f T=g T) :
    AntitoneOn (joinAt T f g) (Ici 0) := by
  intro x hx y hy hxy
  change 0≤x at hx
  change 0≤y at hy
  by_cases hxt : x≤T
  · rw [joinAt_left T f g x hxt]
    by_cases hyt : y≤T
    · rw [joinAt_left T f g y hyt]
      exact hf ⟨hx,hxt⟩ ⟨hy,hyt⟩ hxy
    · rw [joinAt_right T f g y (lt_of_not_ge hyt)]
      exact (hg (mem_Ici.mpr le_rfl) (mem_Ici.mpr (le_of_not_ge hyt)) (le_of_not_ge hyt)).trans
        (by rw [← hmatch]; exact hf ⟨hx,hxt⟩ ⟨hT,le_rfl⟩ hxt)
  · have hyt : T<y := (lt_of_not_ge hxt).trans_le hxy
    rw [joinAt_right T f g x (lt_of_not_ge hxt),joinAt_right T f g y hyt]
    exact hg (mem_Ici.mpr (le_of_not_ge hxt)) (mem_Ici.mpr hyt.le) hxy

/-- Lipschitz bounds on the two compact pieces give a genuine Lipschitz
bound across the join, by splitting the distance at its matching value. -/
theorem joinAt_lipschitzOn (T B : ℝ) (f g : ℝ → ℝ) (Kf Kg : ℝ≥0)
    (hT : 0≤T) (hB : T≤B) (hf : LipschitzOnWith Kf f (Icc 0 T))
    (hg : LipschitzOnWith Kg g (Icc T B)) (hmatch : f T=g T) :
    LipschitzOnWith (max Kf Kg) (joinAt T f g) (Icc 0 B) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  wlog hxy : x≤y generalizing x y
  · rw [dist_comm (joinAt T f g x),dist_comm x]
    exact this y hy x hx (le_of_not_ge hxy)
  by_cases hxt : x≤T
  · rw [joinAt_left T f g x hxt]
    by_cases hyt : y≤T
    · rw [joinAt_left T f g y hyt]
      exact (hf.dist_le_mul x ⟨hx.1,hxt⟩ y ⟨hy.1,hyt⟩).trans
        (mul_le_mul_of_nonneg_right (show (Kf:ℝ)≤(max Kf Kg:ℝ≥0) from le_max_left _ _) dist_nonneg)
    · rw [joinAt_right T f g y (lt_of_not_ge hyt)]
      have h1 := hf.dist_le_mul x ⟨hx.1,hxt⟩ T ⟨hT,le_rfl⟩
      have h2 := hg.dist_le_mul T ⟨le_rfl,hB⟩ y ⟨(le_of_not_ge hyt),hy.2⟩
      rw [← hmatch] at h2
      have hsum : dist x T+dist T y=dist x y := by
        rw [Real.dist_eq,Real.dist_eq,Real.dist_eq,
          abs_of_nonpos (by linarith : x-T≤0),abs_of_nonpos (by linarith : T-y≤0),abs_of_nonpos (by linarith : x-y≤0)]
        ring
      calc
        dist (f x) (g y) ≤ dist (f x) (f T)+dist (f T) (g y) := dist_triangle _ _ _
        _ ≤ (max Kf Kg:ℝ≥0)*dist x T+(max Kf Kg:ℝ≥0)*dist T y := by
          exact add_le_add (h1.trans (mul_le_mul_of_nonneg_right (show (Kf:ℝ)≤(max Kf Kg:ℝ≥0) from le_max_left _ _) dist_nonneg))
            (h2.trans (mul_le_mul_of_nonneg_right (show (Kg:ℝ)≤(max Kf Kg:ℝ≥0) from le_max_right _ _) dist_nonneg))
        _ = (max Kf Kg:ℝ≥0)*dist x y := by rw [← mul_add,hsum]
  · have hyt : T<y := (lt_of_not_ge hxt).trans_le hxy
    rw [joinAt_right T f g x (lt_of_not_ge hxt),joinAt_right T f g y hyt]
    exact (hg.dist_le_mul x ⟨(le_of_not_ge hxt),hx.2⟩ y ⟨hyt.le,hy.2⟩).trans
      (mul_le_mul_of_nonneg_right (show (Kg:ℝ)≤(max Kf Kg:ℝ≥0) from le_max_right _ _) dist_nonneg)


/-- A finite Lipschitz bound on every compact subinterval of a ray. -/
@[expose] def LocallyLipschitzOnRay (f : ℝ → ℝ) (A : ℝ) : Prop :=
  ∀ B : ℝ, A≤B → ∃ K : ℝ≥0, LipschitzOnWith K f (Icc A B)

theorem locallyLipschitzOnRay_of_C1 (f : ℝ → ℝ) (A : ℝ) (hf : ContDiffOn ℝ 1 f (Ici A)) :
    LocallyLipschitzOnRay f A := by
  intro B _
  exact (hf.mono (fun s hs => hs.1)).exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc

theorem locallyLipschitzOnRay_mono (f : ℝ → ℝ) (A B : ℝ) (hAB : A≤B)
    (hf : LocallyLipschitzOnRay f A) : LocallyLipschitzOnRay f B := by
  intro C hC
  obtain ⟨K,hK⟩ := hf C (hAB.trans hC)
  exact ⟨K,hK.mono (fun s hs => ⟨hAB.trans hs.1,hs.2⟩)⟩

/-- Actual local Lipschitz gluing applies also to a previously patched piece. -/
theorem joinAt_locallyLipschitz (T : ℝ) (f g : ℝ → ℝ) (hT : 0≤T)
    (hf : LocallyLipschitzOnRay f 0) (hg : LocallyLipschitzOnRay g T) (hmatch : f T=g T) :
    LocallyLipschitzOnRay (joinAt T f g) 0 := by
  intro B hB
  obtain ⟨Kf,hKf⟩ := hf T hT
  obtain ⟨Kg,hKg⟩ := hg (max T B) (le_max_left _ _)
  have hLip := joinAt_lipschitzOn T (max T B) f g Kf Kg hT (le_max_left _ _) hKf hKg hmatch
  exact ⟨max Kf Kg,hLip.mono (fun s hs => ⟨hs.1,hs.2.trans (le_max_right _ _)⟩)⟩

theorem locallyLipschitzOnRay_locally_AC (f : ℝ → ℝ) (hf : LocallyLipschitzOnRay f 0) :
    ∀ B≥0, AbsolutelyContinuousOnInterval f 0 B := by
  intro B hB
  obtain ⟨K,hK⟩ := hf B hB
  have hK' : LipschitzOnWith K f (uIcc 0 B) := by simpa only [uIcc_of_le hB] using hK
  exact hK'.absolutelyContinuousOnInterval

@[expose] def scaledTail (h T τ : ℝ) (f : ℝ → ℝ) (s : ℝ) : ℝ := h*f ((s-T)/τ)

theorem scaledTail_C1 (h T τ : ℝ) (f : ℝ → ℝ) (hτ : 0<τ)
    (hf : ContDiffOn ℝ 1 f (Ici 0)) : ContDiffOn ℝ 1 (scaledTail h T τ f) (Ici T) := by
  have hc : ContDiffOn ℝ 1 (fun s : ℝ => (s-T)/τ) (Ici T) := by fun_prop
  have hmap : MapsTo (fun s : ℝ => (s-T)/τ) (Ici T) (Ici 0) := by
    intro s hs
    change T≤s at hs
    exact div_nonneg (sub_nonneg.mpr hs) hτ.le
  exact contDiffOn_const.mul (hf.comp hc hmap)

theorem scaledTail_antitone (h T τ : ℝ) (f : ℝ → ℝ) (hh : 0≤h) (hτ : 0<τ)
    (hf : AntitoneOn f (Ici 0)) : AntitoneOn (scaledTail h T τ f) (Ici T) := by
  intro x hx y hy hxy
  change T≤x at hx
  change T≤y at hy
  exact mul_le_mul_of_nonneg_left
    (hf (div_nonneg (sub_nonneg.mpr hx) hτ.le) (div_nonneg (sub_nonneg.mpr hy) hτ.le)
      (div_le_div_of_nonneg_right (sub_le_sub_right hxy T) hτ.le)) hh

theorem scaledTail_initial (h T τ : ℝ) (f : ℝ → ℝ) (hf : f 0=1) : scaledTail h T τ f T=h := by
  simp only [scaledTail,sub_self,zero_div,hf,mul_one]

@[expose] def lowerPatch (u : ℝ → ℝ) (h T τ : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  joinAt T u (scaledTail h T τ f)

@[expose] def upperPatch (u : ℝ → ℝ) (h T0 T1 τ : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  joinAt T0 u (joinAt T1 (fun _ => h) (scaledTail h T1 τ f))

/-- The lower comparison patch has genuine local absolute continuity. -/
theorem lowerPatch_locally_AC (u f : ℝ → ℝ) (h T τ : ℝ) (hT : 0≤T) (hτ : 0<τ)
    (hu : ContDiffOn ℝ 1 u (Ici 0)) (hf : ContDiffOn ℝ 1 f (Ici 0)) (huT : u T=h) (hf0 : f 0=1) :
    ∀ B≥0, AbsolutelyContinuousOnInterval (lowerPatch u h T τ f) 0 B := by
  apply locallyLipschitzOnRay_locally_AC
  exact joinAt_locallyLipschitz T u (scaledTail h T τ f) hT
    (locallyLipschitzOnRay_of_C1 u 0 hu)
    (locallyLipschitzOnRay_of_C1 _ T (scaledTail_C1 h T τ f hτ hf))
    (huT.trans (scaledTail_initial h T τ f hf0).symm)

/-- The plateau and tail first form a local Lipschitz function, which is then
joined to u. Thus both corners of the actual upper patch are harmless. -/
theorem upperPatch_locally_AC (u f : ℝ → ℝ) (h T0 T1 τ : ℝ) (hT0 : 0≤T0) (hT1 : T0≤T1) (hτ : 0<τ)
    (hu : ContDiffOn ℝ 1 u (Ici 0)) (hf : ContDiffOn ℝ 1 f (Ici 0)) (huT : u T0=h) (hf0 : f 0=1) :
    ∀ B≥0, AbsolutelyContinuousOnInterval (upperPatch u h T0 T1 τ f) 0 B := by
  have hT1z : 0≤T1 := hT0.trans hT1
  have hinner := joinAt_locallyLipschitz T1 (fun _ => h) (scaledTail h T1 τ f) hT1z
    (locallyLipschitzOnRay_of_C1 _ 0 contDiffOn_const)
    (locallyLipschitzOnRay_of_C1 _ T1 (scaledTail_C1 h T1 τ f hτ hf))
    (scaledTail_initial h T1 τ f hf0).symm
  apply locallyLipschitzOnRay_locally_AC
  exact joinAt_locallyLipschitz T0 u _ hT0 (locallyLipschitzOnRay_of_C1 u 0 hu)
    (locallyLipschitzOnRay_mono _ 0 T0 hT0 hinner)
    (by rw [joinAt_left T1 (fun _ => h) (scaledTail h T1 τ f) T0 hT1]; exact huT)


theorem joinAt_values (T : ℝ) (f g : ℝ → ℝ)
    (hf : ∀ s∈Icc 0 T,f s∈Icc 0 1) (hg : ∀ s∈Ici T,g s∈Icc 0 1) :
    ∀ s∈Ici 0,joinAt T f g s∈Icc 0 1 := by
  intro s hs
  by_cases hst : s≤T
  · rw [joinAt_left T f g s hst]
    exact hf s ⟨hs,hst⟩
  · rw [joinAt_right T f g s (lt_of_not_ge hst)]
    exact hg s (le_of_not_ge hst)

theorem scaledTail_values (h T τ : ℝ) (f : ℝ → ℝ) (hh0 : 0≤h) (hh1 : h≤1) (hτ : 0<τ)
    (hf : ∀ s∈Ici 0,f s∈Icc 0 1) : ∀ s∈Ici T,scaledTail h T τ f s∈Icc 0 1 := by
  intro s hs
  obtain ⟨hf0,hf1⟩ := hf ((s-T)/τ) (div_nonneg (sub_nonneg.mpr hs) hτ.le)
  exact ⟨mul_nonneg hh0 hf0,(mul_le_mul_of_nonneg_left hf1 hh0).trans (by simpa only [mul_one] using hh1)⟩

/-- Actual admissibility of the lower patch, including its join corner. -/
theorem lowerPatch_admissible (u f : ℝ → ℝ) (h T τ : ℝ)
    (hT : 0≤T) (hτ : 0<τ) (huC1 : ContDiffOn ℝ 1 u (Ici 0)) (hfC1 : ContDiffOn ℝ 1 f (Ici 0))
    (hu : AdmissibleProfile u) (hf : AdmissibleProfile f) (huT : u T=h) :
    AdmissibleProfile (lowerPatch u h T τ f) := by
  have hh0 : 0≤h := by rw [← huT]; exact (hu.values T hT).1
  have hh1 : h≤1 := by rw [← huT]; exact (hu.values T hT).2
  exact {
    locally_AC := lowerPatch_locally_AC u f h T τ hT hτ huC1 hfC1 huT hf.initial
    nonincreasing := joinAt_antitone T u _ hT (hu.nonincreasing.mono (fun s hs => hs.1))
      (scaledTail_antitone h T τ f hh0 hτ hf.nonincreasing) (huT.trans (scaledTail_initial h T τ f hf.initial).symm)
    values := joinAt_values T u _ (fun s hs => hu.values s hs.1) (scaledTail_values h T τ f hh0 hh1 hτ hf.values)
    initial := by rw [lowerPatch,joinAt_left T u _ 0 hT,hu.initial]
  }

/-- Actual admissibility of the upper patch with both corners. -/
theorem upperPatch_admissible (u f : ℝ → ℝ) (h T0 T1 τ : ℝ)
    (hT0 : 0≤T0) (hT1 : T0≤T1) (hτ : 0<τ)
    (huC1 : ContDiffOn ℝ 1 u (Ici 0)) (hfC1 : ContDiffOn ℝ 1 f (Ici 0))
    (hu : AdmissibleProfile u) (hf : AdmissibleProfile f) (huT : u T0=h) :
    AdmissibleProfile (upperPatch u h T0 T1 τ f) := by
  have hh0 : 0≤h := by rw [← huT]; exact (hu.values T0 hT0).1
  have hh1 : h≤1 := by rw [← huT]; exact (hu.values T0 hT0).2
  have hinnerAnti := joinAt_antitone T1 (fun _ => h) (scaledTail h T1 τ f) (hT0.trans hT1)
    (by intro x hx y hy hxy; exact le_rfl)
    (scaledTail_antitone h T1 τ f hh0 hτ hf.nonincreasing)
    (scaledTail_initial h T1 τ f hf.initial).symm
  have hinnerValues := joinAt_values T1 (fun _ => h) (scaledTail h T1 τ f)
    (fun s _ => ⟨hh0,hh1⟩) (scaledTail_values h T1 τ f hh0 hh1 hτ hf.values)
  exact {
    locally_AC := upperPatch_locally_AC u f h T0 T1 τ hT0 hT1 hτ huC1 hfC1 huT hf.initial
    nonincreasing := joinAt_antitone T0 u _ hT0 (hu.nonincreasing.mono (fun s hs => hs.1))
      (hinnerAnti.mono (fun s hs => hT0.trans hs))
      (by rw [joinAt_left T1 (fun _ => h) _ T0 hT1]; exact huT)
    values := joinAt_values T0 u _ (fun s hs => hu.values s hs.1) (fun s hs => hinnerValues s (hT0.trans hs))
    initial := by rw [upperPatch,joinAt_left T0 u _ 0 hT0,hu.initial]
  }

/-- Ordinary derivatives of each tail are derived by actual affine chain rule. -/
theorem scaledTail_hasDerivAt (h T τ s : ℝ) (f : ℝ → ℝ)
    (hf : DifferentiableAt ℝ f ((s-T)/τ)) :
    HasDerivAt (scaledTail h T τ f) ((h/τ)*deriv f ((s-T)/τ)) s := by
  have hd := (hf.hasDerivAt.comp s (((hasDerivAt_id s).sub_const T).div_const τ)).const_mul h
  convert hd using 1
  · rfl
  · ring


/-- Before the join, the actual residual only sees the original segment. -/
theorem joinAt_early_residual (M u g : ℝ → ℝ) (T t : ℝ) (ht : 0≤t) (htT : t<T) :
    profileResidual M (joinAt T u g) t=profileResidual M u t := by
  unfold profileResidual
  rw [joinAt_deriv_left T u g t htT,joinAt_left T u g t htT.le]
  congr 1
  unfold causalConvolution
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  have hsT : s<T := hs.2.trans_lt htT
  have htsT : t-s≤T := by linarith [hs.1]
  change M (joinAt T u g (t-s))*deriv (joinAt T u g) s=M (u (t-s))*deriv u s
  rw [joinAt_left T u g (t-s) htsT,joinAt_deriv_left T u g s hsT]

/-- The normalized profile has its actual ordinary derivative away from zero. -/
theorem normalized_profile_hasDerivAt (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) (t : ℝ) (ht : 0<t) :
    HasDerivAt (normalizedProfile q c) (-normalizedResponse q r t) t := by
  have hd := ((h.profile_C1.differentiableOn (by norm_num)) t ht.le).hasDerivWithinAt
  rw [h.derivative t ht.le] at hd
  exact hd.hasDerivAt (Ici_mem_nhds ht)

/-- The finite initial response mass is obtained by genuine FTC. -/
theorem normalized_response_initial_mass (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) (T : ℝ) (hT : 0≤T) :
    (∫ s in 0..T,normalizedResponse q r s)=1-normalizedProfile q c T := by
  have hi : IntervalIntegrable (fun s => -normalizedResponse q r s) volume 0 T := by
    exact (h.response_continuous.mono (fun s hs => hs.1)).neg.intervalIntegrable_of_Icc hT
  have hd := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
    (h.profile_C1.continuousOn.mono (fun s hs => hs.1))
    (fun t ht => normalized_profile_hasDerivAt p β γ q c r h t ht.1) hi
  rw [intervalIntegral.integral_neg,h.initial_profile] at hd
  linarith

/-- The memory-response balance is exact even at the right endpoint t=0. -/
theorem normalized_memory_response_balance (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) (T : ℝ) (hT : 0≤T) :
    causalConvolution (fun s => normalizedMemory q (purePhi p (β^2) γ) (normalizedProfile q c s))
      (normalizedResponse q r) T=normalizedProfile q c T-normalizedResponse q r T := by
  have he := h.equation T hT
  rw [h.derivative T hT] at he
  have hc : causalConvolution (fun s => normalizedMemory q (purePhi p (β^2) γ) (normalizedProfile q c s))
      (fun s => derivWithin (normalizedProfile q c) (Ici 0) s) T =
      -causalConvolution (fun s => normalizedMemory q (purePhi p (β^2) γ) (normalizedProfile q c s))
        (normalizedResponse q r) T := by
    unfold causalConvolution
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hT] at hs
    change _*derivWithin (normalizedProfile q c) (Ici 0) s=-(_*normalizedResponse q r s)
    rw [h.derivative s hs.1]
    ring
  rw [hc] at he
  linarith

end
end SphericalAging.StationaryPatchedProfiles
