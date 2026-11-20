import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonListLength
open CategoryTheory Polynomial

namespace GlobalTheory.SerCmp

/- English proof (translation)
Unfold `GlobalTheory.GLq.zOf Formalism.IrreducibleCountingLemmas.TYPES.zIdem`. Rewrite using `[FDRep.char_one]`. Both sides reduce to the same expression.
-/
theorem zOf_character {G : Type} [Group G] [Fintype G] (τ : FDRep ℂ G) :
    GlobalTheory.GLq.zOf τ.character = Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ := by
  unfold GlobalTheory.GLq.zOf Formalism.IrreducibleCountingLemmas.TYPES.zIdem
  rw [FDRep.char_one]
  rfl

/- English proof (translation)
Unfold `GlobalTheory.GLq.zOf`. Rewrite using `[MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]`. Simplify using `only [MonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem zOf_coeff {G : Type} [Group G] [Fintype G] (χ : G → ℂ) (y : G) :
    (GlobalTheory.GLq.zOf χ).coeff y = χ 1 / (Fintype.card G : ℂ) * χ y⁻¹ := by
  classical
  unfold GlobalTheory.GLq.zOf
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Establish `: Subsingleton τ.V` using `Module.finrank_zero_iff.mp h`. Unfold `FDRep.character`. Rewrite using `[Subsingleton.elim (τ.ρ x) 0]`. Conclude with `map_zero _`.
-/
theorem character_eq_zero_of_finrank {G : Type} [Group G] (τ : FDRep ℂ G)
    (h : Module.finrank ℂ τ.V = 0) (x : G) : τ.character x = 0 := by
  have : Subsingleton τ.V := Module.finrank_zero_iff.mp h
  unfold FDRep.character
  rw [Subsingleton.elim (τ.ρ x) 0]
  exact map_zero _

/- English proof (translation)
Establish `hc : (Fintype.card G : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Establish `hy : ∀ y : G, σ.character 1 * σ.character y = τ.character 1 * τ.character y`. Introduce `y`. Establish `h1` using `zOf_coeff σ.character y⁻¹`. Establish `h2` using `zOf_coeff τ.character y⁻¹`.

Rewrite `h1` using `[h, h2, inv_inv]`. Clear denominators, using `at h1` for the nonvanishing conditions. Apply the tactic sequence `first | exact h1.symm | linear_combination (-1 : ℂ) * h1`. Establish `h1` using `hy 1`. Rewrite `h1` using `[FDRep.char_one, FDRep.char_one]`.

Establish `h2 : Module.finrank ℂ σ.V * Module.finrank ℂ σ.V = Module.finrank ℂ τ.V * Module.finrank ℂ τ.V`. Conclude with `h1` after adjusting the coercions. Establish `h3 : Module.finrank ℂ σ.V = Module.finrank ℂ τ.V` using `Nat.mul_self_inj.mp h2`. Use function extensionality and compare the values at `y`. Distinguish the cases in `h0 : Module.finrank ℂ τ.V = 0`.

Rewrite using `[character_eq_zero_of_finrank τ h0, character_eq_zero_of_finrank σ (h3.trans h0)]`. Establish `h4` using `hy y`. Rewrite `h4` using `[FDRep.char_one, FDRep.char_one, h3]`. Conclude with `mul_left_cancel₀ (Nat.cast_ne_zero.mpr h0) h4`.
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
Establish `hinj : Set.InjOn (GlobalTheory.GLq.zOf (G` using `G)) {χ : G → ℂ | GlobalTheory.GLq.IsIrr χ ∧ Q χ} := by`. Introduce and unpack `a ⟨⟨V, -, hV⟩, -⟩ b ⟨⟨U, -, hU⟩, -⟩ hab`. Take `rfl : V.character = a` from `funext hV`. Take `rfl : U.character = b` from `funext hU`. Conclude with `character_eq_of_zOf_eq V U hab`.

Rewrite using `[← finsum_mem_image (f := fun z : MonoidAlgebra ℂ G => z) hinj]`. Use `finsum_congr fun z => ?_` and prove the remaining obligations. Establish `hiff : (z ∈ GlobalTheory.GLq.zOf '' {χ : G → ℂ | GlobalTheory.GLq.IsIrr χ ∧ Q χ}) = ∃ τ : FDRep ℂ G, CategoryTheory.Simple τ ∧ Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ = z ∧ Q τ.character`. Apply `propext` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, ⟨⟨V, hs, hV⟩, hQ⟩, rfl⟩`. Take `rfl : V.character = a` from `funext hV`. Conclude with `⟨V, hs, (zOf_character V).symm, hQ⟩`. Introduce and unpack `⟨V, hs, rfl, hQ⟩`. Conclude with `⟨V.character, ⟨⟨V, hs, fun _ => rfl⟩, hQ⟩, zOf_character V⟩`.

Rewrite using `[hiff]`.
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
