import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep

/- English proof (translation)
Introduce `F E _ _ _ _ _ c n G ⟨hc, _, hG, hdet⟩`. Set `σ : E →+* E` to `(c : E →+* E)`. Establish `he : ∀ x y : Fin n → E, hermE c G x y = x ⬝ᵥ G *ᵥ (σ ∘ y)` using `fun x y => (GlobalTheory.HermDiag.dotProduct_mulVec_comp_eq_sum σ G x y).symm`. Take `⟨v, hv⟩` from `GlobalTheory.HermDiag.exists_orthogonal_basis_dotProduct (c := σ) two_ne_zero hc hG`. Establish `hd` using `GlobalTheory.HermDiag.congr_diagonal_of_orthogonal σ v hv`.

Use `⟨v, fun i => ?_, fun i j hij => ?_, v.span_eq⟩` and prove the remaining obligations. Rewrite using `[he]`. Conclude with `GlobalTheory.HermDiag.ne_zero_of_congr_diagonal (GlobalTheory.HermDiag.det_of_basis_ne_zero v) hd hdet i`. Rewrite using `[he]`. Conclude with `hv i j hij`.
-/
theorem exists_anisotropic_orthogonal_basis :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G →
      ∃ x : Fin n → Fin n → E, (∀ i, hermE c G (x i) (x i) ≠ 0) ∧
        (∀ i j, i ≠ j → hermE c G (x i) (x j) = 0) ∧ Submodule.span E (Set.range x) = ⊤ := by
  intro F E _ _ _ _ _ c n G ⟨hc, _, hG, hdet⟩
  let σ : E →+* E := (c : E →+* E)
  have he : ∀ x y : Fin n → E, hermE c G x y = x ⬝ᵥ G *ᵥ (σ ∘ y) := fun x y =>
    (GlobalTheory.HermDiag.dotProduct_mulVec_comp_eq_sum σ G x y).symm
  obtain ⟨v, hv⟩ := GlobalTheory.HermDiag.exists_orthogonal_basis_dotProduct (c := σ) two_ne_zero hc hG
  have hd := GlobalTheory.HermDiag.congr_diagonal_of_orthogonal σ v hv
  refine ⟨v, fun i => ?_, fun i j hij => ?_, v.span_eq⟩
  · rw [he]
    exact GlobalTheory.HermDiag.ne_zero_of_congr_diagonal (GlobalTheory.HermDiag.det_of_basis_ne_zero v) hd hdet i
  · rw [he]
    exact hv i j hij

end GlobalTheory.UnRep
