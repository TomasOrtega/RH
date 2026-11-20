import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonListLength
open CategoryTheory Polynomial

namespace GlobalTheory.SerCmp

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem zOf_character {G : Type} [Group G] [Fintype G] (τ : FDRep ℂ G) :
    GlobalTheory.GLq.zOf τ.character = Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ := by
  unfold GlobalTheory.GLq.zOf Formalism.IrreducibleCountingLemmas.TYPES.zIdem
  rw [FDRep.char_one]
  rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem zOf_coeff {G : Type} [Group G] [Fintype G] (χ : G → ℂ) (y : G) :
    (GlobalTheory.GLq.zOf χ).coeff y = χ 1 / (Fintype.card G : ℂ) * χ y⁻¹ := by
  classical
  unfold GlobalTheory.GLq.zOf
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem character_eq_zero_of_finrank {G : Type} [Group G] (τ : FDRep ℂ G)
    (h : Module.finrank ℂ τ.V = 0) (x : G) : τ.character x = 0 := by
  have : Subsingleton τ.V := Module.finrank_zero_iff.mp h
  unfold FDRep.character
  rw [Subsingleton.elim (τ.ρ x) 0]
  exact map_zero _

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Clear the denominators using the available nonvanishing facts. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem character_eq_of_zOf_eq {G : Type} [Group G] [Fintype G] (σ τ : FDRep ℂ G)
    (h : GlobalTheory.GLq.zOf σ.character = GlobalTheory.GLq.zOf τ.character) : σ.character = τ.character := by
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hy : ∀ y : G, σ.character 1 * σ.character y = τ.character 1 * τ.character y := by
    intro y
    have h1 := zOf_coeff σ.character y⁻¹
    have h2 := zOf_coeff τ.character y⁻¹
    rw [h, h2, inv_inv] at h1
    field_simp at h1
    first | exact h1.symm | linear_combination (-1 : ℂ) * h1
  have h1 := hy 1
  rw [FDRep.char_one, FDRep.char_one] at h1
  have h2 : Module.finrank ℂ σ.V * Module.finrank ℂ σ.V = Module.finrank ℂ τ.V * Module.finrank ℂ τ.V := by
    exact_mod_cast h1
  have h3 : Module.finrank ℂ σ.V = Module.finrank ℂ τ.V := Nat.mul_self_inj.mp h2
  funext y
  by_cases h0 : Module.finrank ℂ τ.V = 0
  · rw [character_eq_zero_of_finrank τ h0, character_eq_zero_of_finrank σ (h3.trans h0)]
  · have h4 := hy y
    rw [FDRep.char_one, FDRep.char_one, h3] at h4
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr h0) h4

/- English proof (translation)
Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem finsum_zOf_eq_finsum_zIdem {G : Type} [Group G] [Fintype G] (Q : (G → ℂ) → Prop) :
    ∑ᶠ χ ∈ {χ : G → ℂ | GlobalTheory.GLq.IsIrr χ ∧ Q χ}, GlobalTheory.GLq.zOf χ =
      ∑ᶠ (z : MonoidAlgebra ℂ G) (_ : ∃ τ : FDRep ℂ G, CategoryTheory.Simple τ ∧
        Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ = z ∧ Q τ.character), z := by
  have hinj : Set.InjOn (GlobalTheory.GLq.zOf (G := G)) {χ : G → ℂ | GlobalTheory.GLq.IsIrr χ ∧ Q χ} := by
    rintro a ⟨⟨V, -, hV⟩, -⟩ b ⟨⟨U, -, hU⟩, -⟩ hab
    obtain rfl : V.character = a := funext hV
    obtain rfl : U.character = b := funext hU
    exact character_eq_of_zOf_eq V U hab
  rw [← finsum_mem_image (f := fun z : MonoidAlgebra ℂ G => z) hinj]
  refine finsum_congr fun z => ?_
  have hiff : (z ∈ GlobalTheory.GLq.zOf '' {χ : G → ℂ | GlobalTheory.GLq.IsIrr χ ∧ Q χ}) =
      ∃ τ : FDRep ℂ G, CategoryTheory.Simple τ ∧ Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ = z ∧ Q τ.character := by
    apply propext
    constructor
    · rintro ⟨a, ⟨⟨V, hs, hV⟩, hQ⟩, rfl⟩
      obtain rfl : V.character = a := funext hV
      exact ⟨V, hs, (zOf_character V).symm, hQ⟩
    · rintro ⟨V, hs, rfl, hQ⟩
      exact ⟨V.character, ⟨⟨V, hs, fun _ => rfl⟩, hQ⟩, zOf_character V⟩
  rw [hiff]

end GlobalTheory.SerCmp
