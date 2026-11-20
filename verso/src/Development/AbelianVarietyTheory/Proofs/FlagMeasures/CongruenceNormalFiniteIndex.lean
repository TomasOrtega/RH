import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.CongTop

/- English proof (translation)
Introduce `I`. Take `⟨-, -, -, hKc, -, hK, hg⟩` from `GlobalTheory.CongTop.adelic_topology I`. Use `⟨hK, fun g hg1 => ?_⟩` and prove the remaining obligations. Take `⟨hKgo, ⟨H, hH⟩, hnorm⟩` from `hg g hg1`. Use `⟨⟨H, hH⟩, hKgo, hnorm, ?_⟩` and prove the remaining obligations.

Establish `hopen : ∀ t ∈ I.Kset, IsOpen {x : I.Gf | t⁻¹ * x ∈ I.Kg g}` using `fun t _ => hKgo.preimage (continuous_mul_left t⁻¹)`. Establish `hsub : I.Kset ⊆ ⋃ t ∈ I.Kset, {x : I.Gf | t⁻¹ * x ∈ I.Kg g}`. Introduce `x hx`. Use `Set.mem_biUnion hx ?_` and prove the remaining obligations. Use `show x⁻¹ * x ∈ I.Kg g`.

Rewrite using `[inv_mul_cancel, ← hH]`. Conclude with `H.one_mem`. Take `⟨b, -, hb, hcov⟩` from `hKc.elim_finite_subcover_image hopen hsub`. Use `⟨hb.toFinset, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨t, ht, hxt⟩` from `Set.mem_iUnion₂.mp (hcov hx)`.

Conclude with `⟨t, hb.mem_toFinset.mpr ht, hxt⟩`.
-/
theorem congruence_normal_finite_index : ∀ (I : AutInst), (∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kset) ∧ ∀ g : ℕ, 1 ≤ g → (∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kg g) ∧ IsOpen (I.Kg g) ∧ (∀ x ∈ I.Kset, ∀ y ∈ I.Kg g, x * y * x⁻¹ ∈ I.Kg g) ∧ ∃ s : Finset I.Gf, ∀ x ∈ I.Kset, ∃ t ∈ s, t⁻¹ * x ∈ I.Kg g := by
  intro I
  obtain ⟨-, -, -, hKc, -, hK, hg⟩ := GlobalTheory.CongTop.adelic_topology I
  refine ⟨hK, fun g hg1 => ?_⟩
  obtain ⟨hKgo, ⟨H, hH⟩, hnorm⟩ := hg g hg1
  refine ⟨⟨H, hH⟩, hKgo, hnorm, ?_⟩

  have hopen : ∀ t ∈ I.Kset, IsOpen {x : I.Gf | t⁻¹ * x ∈ I.Kg g} := fun t _ =>
    hKgo.preimage (continuous_mul_left t⁻¹)
  have hsub : I.Kset ⊆ ⋃ t ∈ I.Kset, {x : I.Gf | t⁻¹ * x ∈ I.Kg g} := by
    intro x hx
    refine Set.mem_biUnion hx ?_
    show x⁻¹ * x ∈ I.Kg g
    rw [inv_mul_cancel, ← hH]
    exact H.one_mem
  obtain ⟨b, -, hb, hcov⟩ := hKc.elim_finite_subcover_image hopen hsub
  refine ⟨hb.toFinset, fun x hx => ?_⟩
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp (hcov hx)
  exact ⟨t, hb.mem_toFinset.mpr ht, hxt⟩

end GlobalTheory.CongTop
