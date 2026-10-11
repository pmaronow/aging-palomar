module

public import SphericalAging.RemoteResponseTheorem
public import SphericalAging.StrongResponseConsequences
public import SphericalAging.StationaryFamilyReflection

public section

/-! Complete local source 11.1 for every pure p≥3. Recent-profile
convergence is derived from the preceding stationary cluster compactness
and threshold ceiling. The zero-plateau argument uses the genuine white
prefix; the positive-plateau argument uses the actual finite forks10.4 and
unweighted Brownian bridge3.4. No strong-row conclusion is a hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace SphericalAging.StrongResponseTheorem
open CKSpecification ProfileCenterEnergy StationaryClusterInputs
  StationaryMultiplierSelection StationaryFamilySelection StationaryFamilyReflection
  StrongResponseConsequences FiniteForkStanding ExternalFieldUniformCost
  WeightedBrownianTheorem

/-- The full response-row theorem in the general positive-plateau case.
Every remote localization bound is derived by source11.11. -/
theorem positive_plateau_source11_1 {p : ℕ} (hp : 3≤p)
    {β ell e q : ℝ} {d : CKData} {c r : ℝ→ℝ}
    (hβ : 0<β) (h : CKEquations p β d) (H : Profile c r q)
    (hq : 0<q) (hq1 : q<1)
    (hell : ell=PlateauAlgebra.multiplier p β q)
    (he : e=(ell-1)/((p:ℝ)*β))
    (hr : ∀u,0<u→0≤r u)
    (hm : β^2*PlateauAlgebra.marginalityPolynomial p q=1)
    (hR : ∀A : ℝ,0≤A→TendstoUniformlyOn
      (fun T (z : ℝ×ℝ) => d.R (T+z.1) (T+z.2))
      (fun z => r (z.1-z.2)) atTop (PrefixRectangleStability.triangle A))
    (hPub : ∀Lip : ℝ≥0,PublishedFieldThreshold p Lip)
    {dim : ℕ→ℕ} (hDim : ∀n,1≤dim n) (hTop : Tendsto dim atTop atTop)
    (F : Forks dim p β e c r)
    (hprimitive : ∀L T : ℝ≥0,∀u : ℝ≥0,u≤T→Tendsto
      (fun n => brownianPrimitive (dim n) p β (T+L) u) atTop
      (𝓝 (∫v in (0:ℝ)..(u:ℝ),d.R (T+L) v))) : Conclusions d r := by
  have hi : IntegrableOn r (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr H.integrable_r
  exact wholeclaims_of_remote h H.continuous_r hi hR
    (RemoteResponseTheorem.source11_11 hp hβ h H hq hq1 hell he hr hm
      hPub hDim hTop F hprimitive).2.2

/-- The selected stationary profile is unique, using the preceding
compactness and finite-age threshold ceiling, rather than a uniqueness
conclusion supplied to the response theorem. -/
theorem selected_cluster_unique {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ}
    (H : Cluster h T c r ell q) (hcompact : ClusterCompactness h)
    (hceiling : PrefixCeiling h) :
    ∀U c' r' ell' q',Cluster h U c' r' ell' q'→
      ell'=ell ∧ ∀t : ℝ,0≤t→c' t=c t ∧ r' t=r t := by
  obtain ⟨ell₀,q₀,c₀,r₀,T₀,H₀,hl,hunique⟩ :=
    common_stationary_cluster h hcompact hceiling
  have hH := hunique T c r ell q H
  intro U c' r' ell' q' H'
  have hU := hunique U c' r' ell' q' H'
  refine ⟨hU.1.trans hH.1.symm,?_⟩
  intro t ht
  exact ⟨(hU.2 t ht).1.trans (hH.2 t ht).1.symm,
    (hU.2 t ht).2.trans (hH.2 t ht).2.symm⟩

/-- All printed clauses of source11.1, including the squared remote-tail
limits and χ(t,0)/√t→0. The positive-plateau finite-fork and primitive
inputs are requested only when q>0. The q=0 proof needs neither. -/
theorem source11_1 {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ}
    (H : Cluster h T c r ell q) (hcompact : ClusterCompactness h)
    (hceiling : PrefixCeiling h)
    (hPub : ∀Lip : ℝ≥0,PublishedFieldThreshold p Lip)
    {dim : ℕ→ℕ} (hDim : ∀n,1≤dim n) (hTop : Tendsto dim atTop atTop)
    (hFork : 0<q→Forks dim p β ((ell-1)/((p:ℝ)*β)) c r)
    (hprimitive : 0<q→∀L T : ℝ≥0,∀u : ℝ≥0,u≤T→Tendsto
      (fun n => brownianPrimitive (dim n) p β (T+L) u) atTop
      (𝓝 (∫v in (0:ℝ)..(u:ℝ),d.R (T+L) v))) : Conclusions d r := by
  have hunique := selected_cluster_unique H hcompact hceiling
  have hR := fun A hA => (whole_family_uniform H hcompact hunique A hA).2
  by_cases hq : q=0
  · have hc : Tendsto c atTop (𝓝 0) := by simpa only [hq] using H.plateau
    have hi : IntegrableOn r (Ici 0) :=
      (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr H.integrable_response
    exact zero_plateau_source11_1 h hc H.stationary.continuous_r hi hR
      (whole_family_reflection H hcompact hunique)
  · have hqpos : 0<q := by have hs := H.scalar.1;exact lt_of_le_of_ne hs (Ne.symm hq)
    exact positive_plateau_source11_1 h.spin_ge_three h.beta_pos h H.profile hqpos
      H.plateau_lt_one H.scalar.2.1 rfl (fun u hu => (H.physical u hu.le).1)
      (cluster_marginality H hceiling hqpos).1 hR hPub hDim hTop
      (hFork hqpos) (hprimitive hqpos)

end SphericalAging.StrongResponseTheorem
