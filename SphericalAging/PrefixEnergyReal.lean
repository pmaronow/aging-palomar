module

public import SphericalAging.PrefixEnergyLimit

public section

/-! Filter form of the actual prefix-energy calculation. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace Topology
open Set Filter MeasureTheory
namespace SphericalAging.PrefixEnergyReal
open CKSpecification PrefixReflection PrefixEnergyLimit CausalTreeRealization

theorem prefix_energy_tendsto_filter {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {ι : Type*} {F : Filter ι} [F.IsCountablyGenerated] {T : ι → ℝ} (hT : ∀ n, 0 ≤ T n)
    {c r : ℝ → ℝ} {ell L : ℝ} (hL : 0 ≤ L)
    (hR : ∀ τ ∈ Icc 0 L, Tendsto (fun n => d.R (T n+L) (T n+L-τ)) F (nhds (r τ)))
    (hC : ∀ τ ∈ Icc 0 L, Tendsto (fun n => d.C (T n+L) (T n+L-τ)) F (nhds (c τ)))
    (hQ : ∀ τ ∈ Icc 0 L, Tendsto (fun n => futureKernel h (T n) (L-τ) L) F
      (nhds (c (2*L-τ))))
    (hlambda : Tendsto (fun n => d.multiplier (T n+L)) F (nhds ell)) :
    Tendsto (fun n => treeEnergy p (prefixVector h (T n) (T n+L))) F
      (nhds ((ell-1)/((p : ℝ)*β) + β*(p : ℝ)*
        (∫ τ in (0 : ℝ)..L, r τ*(c (2*L-τ)^(p-1)-c τ^(p-1))))) := by
  have hI : Tendsto (fun n => ∫ τ in (0 : ℝ)..L, lagIntegrand h (T n) L τ) F
      (nhds (∫ τ in (0 : ℝ)..L, r τ*(c (2*L-τ)^(p-1)-c τ^(p-1)))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (2 : ℝ))
    · exact Eventually.of_forall (fun n => (lagIntegrand_continuous h hb (T n) L).aestronglyMeasurable)
    · exact Eventually.of_forall (fun n => ae_of_all _ (fun τ _ => by
        simpa only [Real.norm_eq_abs] using lagIntegrand_abs_le_two h hb (T n) L τ))
    · exact intervalIntegrable_const
    · apply ae_of_all
      intro τ hτ
      rw [uIoc_of_le hL] at hτ
      have hτ' : τ ∈ Icc 0 L := Ioc_subset_Icc_self hτ
      have hl := (hR τ hτ').mul ((hQ τ hτ').pow (p-1) |>.sub ((hC τ hτ').pow (p-1)))
      convert hl using 1
      funext n
      exact lagIntegrand_eq h (hT n) hτ'
  have hE : Tendsto (fun n => energy p β d (T n+L)) F
      (nhds ((ell-1)/((p : ℝ)*β))) := by
    have hquot : Tendsto (fun n => (d.multiplier (T n+L)-1)/((p : ℝ)*β)) F
        (nhds ((ell-1)/((p : ℝ)*β))) :=
      (hlambda.sub tendsto_const_nhds).div_const ((p : ℝ)*β)
    convert hquot using 1
    funext n
    exact energy_eq_multiplier_quotient h (add_nonneg (hT n) hL)
  have hl : Tendsto (fun n => energy p β d (T n+L) +
      β*(p : ℝ)*(∫ τ in (0 : ℝ)..L, lagIntegrand h (T n) L τ)) F
      (nhds ((ell-1)/((p : ℝ)*β) + β*(p : ℝ)*
        (∫ τ in (0 : ℝ)..L, r τ*(c (2*L-τ)^(p-1)-c τ^(p-1))))) :=
    hE.add (tendsto_const_nhds.mul hI)
  convert hl using 1
  funext n
  exact exact_lag_energy_subtraction h hb (hT n) hL


end SphericalAging.PrefixEnergyReal
