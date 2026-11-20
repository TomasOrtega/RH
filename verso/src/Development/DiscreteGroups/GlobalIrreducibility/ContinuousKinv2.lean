import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.KmatMulKinv

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands ValuativeRel Filter Topology

namespace DiscreteGroups.sglob.LConvKir

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

/- English proof (translation)
The claim follows from `continuous_matrix fun p q => by by_cases hp : p = jj · simp only [Kmat, Matrix.of_apply, if_pos hp]; exact continuous_apply q · simp only [Kmat, Matrix.of_apply, if_neg hp]; exact continuous_const`.
-/
theorem continuous_Kmat (jj : Fin (m + 1)) :
    Continuous (Kmat jj : (Fin (m + 1) → k) → Matrix (Fin (m + 1)) (Fin (m + 1)) k) :=
  continuous_matrix fun p q => by
    by_cases hp : p = jj
    · simp only [Kmat, Matrix.of_apply, if_pos hp]; exact continuous_apply q
    · simp only [Kmat, Matrix.of_apply, if_neg hp]; exact continuous_const

/- English proof (translation)
The claim follows from `continuous_matrix fun p q => by by_cases hp : p = jj · by_cases hq : q = jj · simp only [Kinv2, Matrix.of_apply, if_pos hp, if_pos hq]; exact continuous_snd · simp only [Kinv2, Matrix.of_apply, if_pos hp, if_neg hq] exact ((continuous_apply q).comp continuous_fst).neg.mul continu …`.
-/
theorem continuous_Kinv2 (jj : Fin (m + 1)) :
    Continuous (Kinv2 jj : (Fin (m + 1) → k) × k → Matrix (Fin (m + 1)) (Fin (m + 1)) k) :=
  continuous_matrix fun p q => by
    by_cases hp : p = jj
    · by_cases hq : q = jj
      · simp only [Kinv2, Matrix.of_apply, if_pos hp, if_pos hq]; exact continuous_snd
      · simp only [Kinv2, Matrix.of_apply, if_pos hp, if_neg hq]
        exact ((continuous_apply q).comp continuous_fst).neg.mul continuous_snd
    · simp only [Kinv2, Matrix.of_apply, if_neg hp]; exact continuous_const

/- English proof (translation)
Take `⟨O, hO, hOS⟩` from `Units.isInducing_embedProduct.isOpen_iff.1 hS`. Set `H : (Fin (m + 1) → k) → Matrix (Fin (m + 1)) (Fin (m + 1)) k × (Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵐᵒᵖ` to `fun a => (Kmat jj a, MulOpposite.op (Kinv jj a))`. Establish `hee : (Pi.single jj (1 : k) : Fin (m + 1) → k) jj = 1` using `by simp`. Establish `hHc : ContinuousAt H (Pi.single jj 1)`. Establish `hinv : ContinuousAt (fun a : Fin (m + 1) → k => (a jj)⁻¹) (Pi.single jj 1)`.

Establish `h0 : (Pi.single jj (1 : k) : Fin (m + 1) → k) jj ≠ 0` using `by rw [hee]; exact one_ne_zero`. Conclude with `((continuous_apply jj).continuousAt (x := Pi.single jj 1)).inv₀ h0`. Conclude with `(continuous_Kmat jj).continuousAt.prodMk (MulOpposite.continuous_op.continuousAt.comp ((continuous_Kinv2 jj).continuousAt.comp (continuousAt_id.prodMk hinv)))`. Establish `hHe : H (Pi.single jj 1) ∈ O`. Establish `h1' : (1 : GL (Fin (m + 1)) k) ∈ (Units.embedProduct (Matrix (Fin (m + 1)) (Fin (m + 1)) k)) ⁻¹' O`.

Rewrite using `[hOS]`. Conclude with `h1`. Establish `hH1 : H (Pi.single jj 1) = Units.embedProduct _ (1 : GL (Fin (m + 1)) k)`. Simplify using `only [H, Units.embedProduct_apply, Units.val_one, inv_one, Kmat_single, Kinv_single]`. Rewrite using `[hH1]`.

Conclude with `h1'`. Establish `hcomp : ContinuousAt (fun b : Fin (m + 1) → k => H (Pi.single jj 1 + b)) 0` using `hHc.comp_of_eq ((continuous_const.add continuous_id).continuousAt) (by simp)`. Establish `hN` using `hcomp.preimage_mem_nhds (hO.mem_nhds (by show H (Pi.single jj 1 + 0) ∈ O; rw [add_zero]; exact hHe))`. Rewrite `hN` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, -, t, ht, hIt⟩` from `hN`.

Establish `hT : (⋂ i, t i) ∩ {x : k | valuation k x < ((1 : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)} ∈ 𝓝 (0 : k)` using `Filter.inter_mem (Filter.iInter_mem.2 ht) ((IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun _ hx => hx⟩)`. Take `⟨γ, hγ⟩` from `(IsValuativeTopology.mem_nhds_zero_iff _).1 hT`. Use `⟨γ, fun a ha => ?_⟩` and prove the remaining obligations. Establish `hb : ∀ i, a i - (Pi.single jj (1 : k) : Fin (m + 1) → k) i ∈ (⋂ i, t i) ∩ {x : k | valuation k x < ((1 : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)}` using `fun i => hγ (ha i)`. Establish `hmem : H a ∈ O`.

Use `hIt (a := a - Pi.single jj 1) (fun i _ => Set.mem_iInter.1 (hb i).1 i)` as an intermediate fact. Simplify using `using this`. Establish `haj : a jj ≠ 0`. Introduce `h0`. Establish `h2` using `(hb jj).2`.

Simplify using `[h0] at h2`. Use `⟨⟨Kmat jj a, Kinv jj a, Kmat_mul_Kinv jj a haj, Kinv_mul_Kmat jj a haj⟩, ?_, rfl, rfl⟩` and prove the remaining obligations. Rewrite using `[← hOS]`. Use `show Units.embedProduct _ _ ∈ O`. Rewrite using `[Units.embedProduct_apply]`.

Conclude with `hmem`.
-/
theorem kappa_nbhd (S : Set (GL (Fin (m + 1)) k)) (hS : IsOpen S) (h1 : (1 : GL (Fin (m + 1)) k) ∈ S)
    (jj : Fin (m + 1)) : ∃ γ : (ValueGroupWithZero k)ˣ, ∀ a : Fin (m + 1) → k,
      (∀ i, valuation k (a i - (Pi.single jj (1 : k) : Fin (m + 1) → k) i) < γ) →
      ∃ κ : GL (Fin (m + 1)) k, κ ∈ S ∧ (κ : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = Kmat jj a ∧
        ((κ⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = Kinv jj a := by
  obtain ⟨O, hO, hOS⟩ := Units.isInducing_embedProduct.isOpen_iff.1 hS
  let H : (Fin (m + 1) → k) → Matrix (Fin (m + 1)) (Fin (m + 1)) k × (Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵐᵒᵖ :=
    fun a => (Kmat jj a, MulOpposite.op (Kinv jj a))
  have hee : (Pi.single jj (1 : k) : Fin (m + 1) → k) jj = 1 := by simp
  have hHc : ContinuousAt H (Pi.single jj 1) := by
    have hinv : ContinuousAt (fun a : Fin (m + 1) → k => (a jj)⁻¹) (Pi.single jj 1) := by
      have h0 : (Pi.single jj (1 : k) : Fin (m + 1) → k) jj ≠ 0 := by rw [hee]; exact one_ne_zero
      exact ((continuous_apply jj).continuousAt (x := Pi.single jj 1)).inv₀ h0
    exact (continuous_Kmat jj).continuousAt.prodMk (MulOpposite.continuous_op.continuousAt.comp
      ((continuous_Kinv2 jj).continuousAt.comp (continuousAt_id.prodMk hinv)))
  have hHe : H (Pi.single jj 1) ∈ O := by
    have h1' : (1 : GL (Fin (m + 1)) k) ∈ (Units.embedProduct (Matrix (Fin (m + 1)) (Fin (m + 1)) k)) ⁻¹' O := by
      rw [hOS]; exact h1
    have hH1 : H (Pi.single jj 1) = Units.embedProduct _ (1 : GL (Fin (m + 1)) k) := by
      simp only [H, Units.embedProduct_apply, Units.val_one, inv_one, Kmat_single, Kinv_single]
    rw [hH1]; exact h1'
  have hcomp : ContinuousAt (fun b : Fin (m + 1) → k => H (Pi.single jj 1 + b)) 0 :=
    hHc.comp_of_eq ((continuous_const.add continuous_id).continuousAt) (by simp)
  have hN := hcomp.preimage_mem_nhds (hO.mem_nhds (by show H (Pi.single jj 1 + 0) ∈ O; rw [add_zero]; exact hHe))
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, -, t, ht, hIt⟩ := hN
  have hT : (⋂ i, t i) ∩ {x : k | valuation k x < ((1 : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)} ∈ 𝓝 (0 : k) :=
    Filter.inter_mem (Filter.iInter_mem.2 ht) ((IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun _ hx => hx⟩)
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).1 hT
  refine ⟨γ, fun a ha => ?_⟩
  have hb : ∀ i, a i - (Pi.single jj (1 : k) : Fin (m + 1) → k) i ∈
      (⋂ i, t i) ∩ {x : k | valuation k x < ((1 : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)} :=
    fun i => hγ (ha i)
  have hmem : H a ∈ O := by
    have := hIt (a := a - Pi.single jj 1) (fun i _ => Set.mem_iInter.1 (hb i).1 i)
    simpa using this
  have haj : a jj ≠ 0 := by
    intro h0
    have h2 := (hb jj).2
    simp [h0] at h2
  refine ⟨⟨Kmat jj a, Kinv jj a, Kmat_mul_Kinv jj a haj, Kinv_mul_Kmat jj a haj⟩, ?_, rfl, rfl⟩
  rw [← hOS]
  show Units.embedProduct _ _ ∈ O
  rw [Units.embedProduct_apply]
  exact hmem

end DiscreteGroups.sglob.LConvKir
