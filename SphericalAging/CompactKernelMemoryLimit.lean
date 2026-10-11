module

public import SphericalAging.UniformCausalMemoryIntegration

public section

/-! Nonlinear compact CK memories are continuous under uniform kernel
limits. The proof integrates only the causal prism and permits merely
integrable approximating rows. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal
namespace SphericalAging.CompactKernelMemoryLimit
open UniformBoundedKernelOperations UniformCausalMemoryIntegration
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] abbrev Kernel := ℝ≥0→ℝ≥0→ℝ
@[expose] abbrev Times := ℝ≥0×ℝ≥0×ℝ≥0

@[expose] def square (T : ℝ≥0) : Set (ℝ≥0×ℝ≥0) := {z | z.1≤T ∧ z.2≤T}
@[expose] def triangle (T : ℝ≥0) : Set (ℝ≥0×ℝ≥0) := {z | z.2≤z.1 ∧ z.1≤T}
@[expose] def timeCube (T : ℝ≥0) : Set Times := {z | z.1≤T ∧ z.2.1≤T ∧ z.2.2≤T}
@[expose] def causalPrism (T : ℝ≥0) : Set (Times×ℝ) := {q | q.1∈timeCube T ∧ q.2∈Icc 0 (q.1.1 : ℝ)}

@[expose] def correlationMemory (C R : Kernel) (n m : ℕ) (z : Times) : ℝ :=
  ∫u in (0 : ℝ)..(z.1 : ℝ),(C u.toNNReal z.2.1)^n*(C u.toNNReal z.2.2)^m*R z.1 u.toNNReal

@[expose] def gammaMemory (C G R : Kernel) (n : ℕ) (z : Times) : ℝ :=
  ∫u in (0 : ℝ)..(z.1 : ℝ),(C u.toNNReal z.1)^n*G u.toNNReal z.2.2*R z.1 u.toNNReal

lemma prism_waiting_le {T : ℝ≥0} {q : Times×ℝ} (hq : q∈causalPrism T) : q.2.toNNReal≤T := by
  apply NNReal.coe_le_coe.mp
  rw [Real.coe_toNNReal _ hq.2.1]
  exact hq.2.2.trans (show (q.1.1 : ℝ)≤T from hq.1.1)

lemma prism_waiting_le_terminal {T : ℝ≥0} {q : Times×ℝ} (hq : q∈causalPrism T) : q.2.toNNReal≤q.1.1 := by
  apply NNReal.coe_le_coe.mp
  rw [Real.coe_toNNReal _ hq.2.1]
  exact hq.2.2

variable {A : Type*} {L : Filter A} [NeBot L]

 theorem correlationMemory_uniform_limit {Cn Rn : A→Kernel} {C R : Kernel} {T : ℝ≥0} {Q : ℝ}
    (hQ : 0≤Q) (hC : TendstoUniformlyOn (fun j => fun z : ℝ≥0×ℝ≥0 => Cn j z.1 z.2)
      (Function.uncurry C) L (square T))
    (hR : TendstoUniformlyOn (fun j => fun z : ℝ≥0×ℝ≥0 => Rn j z.1 z.2)
      (Function.uncurry R) L (triangle T))
    (hCn : ∀j z,z∈square T → |Cn j z.1 z.2|≤1)
    (hRn : ∀j z,z∈triangle T → |Rn j z.1 z.2|≤Q)
    (hCc : Continuous (Function.uncurry C)) (hRc : Continuous (Function.uncurry R))
    (n m : ℕ)
    (hI : ∀j z,z∈timeCube T → IntervalIntegrable
      (fun u : ℝ => (Cn j u.toNNReal z.2.1)^n*(Cn j u.toNNReal z.2.2)^m*Rn j z.1 u.toNNReal)
        volume 0 (z.1 : ℝ)) :
    TendstoUniformlyOn (fun j => correlationMemory (Cn j) (Rn j) n m)
      (correlationMemory C R n m) L (timeCube T) := by
  have hcB := uniform_limit_abs_bound hC hCn
  have hrB := uniform_limit_abs_bound hR hRn
  have hA := (hC.comp (fun q : Times×ℝ => (q.2.toNNReal,q.1.2.1))).mono
    (show causalPrism T⊆{q | (q.2.toNNReal,q.1.2.1)∈square T} from
      fun q hq => ⟨prism_waiting_le hq,hq.1.2.1⟩)
  have hS := (hC.comp (fun q : Times×ℝ => (q.2.toNNReal,q.1.2.2))).mono
    (show causalPrism T⊆{q | (q.2.toNNReal,q.1.2.2)∈square T} from
      fun q hq => ⟨prism_waiting_le hq,hq.1.2.2⟩)
  have hResp := (hR.comp (fun q : Times×ℝ => (q.1.1,q.2.toNNReal))).mono
    (show causalPrism T⊆{q | (q.1.1,q.2.toNNReal)∈triangle T} from
      fun q hq => ⟨prism_waiting_le_terminal hq,hq.1.1⟩)
  have hnA : ∀j q,q∈causalPrism T → |Cn j q.2.toNNReal q.1.2.1|≤1 :=
    fun j q hq => hCn j (q.2.toNNReal,q.1.2.1) ⟨prism_waiting_le hq,hq.1.2.1⟩
  have hnS : ∀j q,q∈causalPrism T → |Cn j q.2.toNNReal q.1.2.2|≤1 :=
    fun j q hq => hCn j (q.2.toNNReal,q.1.2.2) ⟨prism_waiting_le hq,hq.1.2.2⟩
  have hcA : ∀q,q∈causalPrism T → |C q.2.toNNReal q.1.2.1|≤1 :=
    fun q hq => hcB (q.2.toNNReal,q.1.2.1) ⟨prism_waiting_le hq,hq.1.2.1⟩
  have hcS : ∀q,q∈causalPrism T → |C q.2.toNNReal q.1.2.2|≤1 :=
    fun q hq => hcB (q.2.toNNReal,q.1.2.2) ⟨prism_waiting_le hq,hq.1.2.2⟩
  have hmS := uniform_pow_of_bound (by norm_num : (0 : ℝ)≤1) hS hnS hcS m
  have hbody := uniform_power_product (by norm_num : (0 : ℝ)≤1) hQ hA hmS hResp hnA hcA
    (fun j q hq => by rw [abs_pow];exact pow_le_one₀ (abs_nonneg _) (hnS j q hq))
    (fun q hq => by rw [abs_pow];exact pow_le_one₀ (abs_nonneg _) (hcS q hq))
    (fun q hq => hrB (q.1.1,q.2.toNNReal) ⟨prism_waiting_le_terminal hq,hq.1.1⟩) n
  apply uniform_causal_interval_integral (D := timeCube T) (endpoint := fun z : Times => (z.1 : ℝ))
    (F := fun j z (u : ℝ) => (Cn j u.toNNReal z.2.1)^n*(Cn j u.toNNReal z.2.2)^m*Rn j z.1 u.toNNReal)
    (f := fun (z : Times) (u : ℝ) => (C u.toNNReal z.2.1)^n*(C u.toNNReal z.2.2)^m*R z.1 u.toNNReal) T.coe_nonneg
    (fun z hz => ⟨z.1.coe_nonneg,hz.1⟩) hI _ hbody
  intro z hz
  exact ((((hCc.comp (show Continuous (fun u : ℝ => (u.toNNReal,z.2.1)) by fun_prop)).pow n).mul
    ((hCc.comp (show Continuous (fun u : ℝ => (u.toNNReal,z.2.2)) by fun_prop)).pow m)).mul
      (hRc.comp (show Continuous (fun u : ℝ => (z.1,u.toNNReal)) by fun_prop))).intervalIntegrable 0 z.1

 theorem gammaMemory_uniform_limit {Cn Gn Rn : A→Kernel} {C G R : Kernel} {T : ℝ≥0} {B Q : ℝ}
    (hB : 0≤B) (hQ : 0≤Q)
    (hC : TendstoUniformlyOn (fun j => fun z : ℝ≥0×ℝ≥0 => Cn j z.1 z.2) (Function.uncurry C) L (square T))
    (hG : TendstoUniformlyOn (fun j => fun z : ℝ≥0×ℝ≥0 => Gn j z.1 z.2) (Function.uncurry G) L (square T))
    (hR : TendstoUniformlyOn (fun j => fun z : ℝ≥0×ℝ≥0 => Rn j z.1 z.2) (Function.uncurry R) L (triangle T))
    (hCn : ∀j z,z∈square T → |Cn j z.1 z.2|≤1)
    (hGn : ∀j z,z∈square T → |Gn j z.1 z.2|≤B)
    (hRn : ∀j z,z∈triangle T → |Rn j z.1 z.2|≤Q)
    (hCc : Continuous (Function.uncurry C)) (hGc : Continuous (Function.uncurry G))
    (hRc : Continuous (Function.uncurry R)) (n : ℕ)
    (hI : ∀j z,z∈timeCube T → IntervalIntegrable
      (fun u : ℝ => (Cn j u.toNNReal z.1)^n*Gn j u.toNNReal z.2.2*Rn j z.1 u.toNNReal)
        volume 0 (z.1 : ℝ)) :
    TendstoUniformlyOn (fun j => gammaMemory (Cn j) (Gn j) (Rn j) n)
      (gammaMemory C G R n) L (timeCube T) := by
  have hcB := uniform_limit_abs_bound hC hCn
  have hgB := uniform_limit_abs_bound hG hGn
  have hrB := uniform_limit_abs_bound hR hRn
  have hA := (hC.comp (fun q : Times×ℝ => (q.2.toNNReal,q.1.1))).mono
    (show causalPrism T⊆{q | (q.2.toNNReal,q.1.1)∈square T} from fun q hq => ⟨prism_waiting_le hq,hq.1.1⟩)
  have hS := (hG.comp (fun q : Times×ℝ => (q.2.toNNReal,q.1.2.2))).mono
    (show causalPrism T⊆{q | (q.2.toNNReal,q.1.2.2)∈square T} from fun q hq => ⟨prism_waiting_le hq,hq.1.2.2⟩)
  have hResp := (hR.comp (fun q : Times×ℝ => (q.1.1,q.2.toNNReal))).mono
    (show causalPrism T⊆{q | (q.1.1,q.2.toNNReal)∈triangle T} from fun q hq => ⟨prism_waiting_le_terminal hq,hq.1.1⟩)
  have hbody := uniform_power_product hB hQ hA hS hResp
    (fun j q hq => hCn j (q.2.toNNReal,q.1.1) ⟨prism_waiting_le hq,hq.1.1⟩)
    (fun q hq => hcB (q.2.toNNReal,q.1.1) ⟨prism_waiting_le hq,hq.1.1⟩)
    (fun j q hq => hGn j (q.2.toNNReal,q.1.2.2) ⟨prism_waiting_le hq,hq.1.2.2⟩)
    (fun q hq => hgB (q.2.toNNReal,q.1.2.2) ⟨prism_waiting_le hq,hq.1.2.2⟩)
    (fun q hq => hrB (q.1.1,q.2.toNNReal) ⟨prism_waiting_le_terminal hq,hq.1.1⟩) n
  apply uniform_causal_interval_integral (D := timeCube T) (endpoint := fun z : Times => (z.1 : ℝ))
    (F := fun j z (u : ℝ) => (Cn j u.toNNReal z.1)^n*Gn j u.toNNReal z.2.2*Rn j z.1 u.toNNReal)
    (f := fun (z : Times) (u : ℝ) => (C u.toNNReal z.1)^n*G u.toNNReal z.2.2*R z.1 u.toNNReal) T.coe_nonneg
    (fun z hz => ⟨z.1.coe_nonneg,hz.1⟩) hI _ hbody
  intro z hz
  exact ((((hCc.comp (show Continuous (fun u : ℝ => (u.toNNReal,z.1)) by fun_prop)).pow n).mul
    (hGc.comp (show Continuous (fun u : ℝ => (u.toNNReal,z.2.2)) by fun_prop))).mul
      (hRc.comp (show Continuous (fun u : ℝ => (z.1,u.toNNReal)) by fun_prop))).intervalIntegrable 0 z.1

end SphericalAging.CompactKernelMemoryLimit
