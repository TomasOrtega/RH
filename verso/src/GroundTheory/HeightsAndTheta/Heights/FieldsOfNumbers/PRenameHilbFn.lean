import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsRename
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.IntNumRelabel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

/- English proof (translation)
Establish `h : P.comap (rename σ) = P.comap (renameEquiv F σ)` using `rfl`. Rewrite using `[h]`. Conclude with `Ideal.map_comap_of_surjective _ (renameEquiv F σ).surjective P`.
-/
theorem map_comap_renameEquiv {F : Type u} [Field F] {S K' : Type} {κ : S → Type}
    {ι' : K' → Type} (σ : (Σ s, κ s) ≃ (Σ k', ι' k')) (P : Ideal (MRing ι' F)) :
    (P.comap (rename σ)).map (renameEquiv F σ) = P := by
  have h : P.comap (rename σ) = P.comap (renameEquiv F σ) := rfl
  rw [h]
  exact Ideal.map_comap_of_surjective _ (renameEquiv F σ).surjective P

/- English proof (translation)
Introduce `F _ S K' _ _ κ ι' E σ hσ P m`. Establish `h` using `Relabel.hilbFn_map_rename E σ hσ (P.comap (rename σ)) (m ∘ E.symm)`. Rewrite `h` using `[map_comap_renameEquiv σ P]`. Rewrite using `[h]`. Use `congr 1`.

Use function extensionality and compare the values at `s`. Simplify using the standard rewrite rules.
-/
theorem RenameHilbFn.proof : RenameHilbFn.Statement.{u} := by
  intro F _ S K' _ _ κ ι' E σ hσ P m
  have h := Relabel.hilbFn_map_rename E σ hσ (P.comap (rename σ)) (m ∘ E.symm)
  rw [map_comap_renameEquiv σ P] at h
  rw [h]
  congr 1
  funext s
  simp

end

end GroundTheory.Heights₂.Heights.FieldNumbers
