import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem exists_redGL_eq {N : ℕ} (g : GL (Fin 2) (ZMod N))
    (hg : Matrix.det (g : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1) : ∃ γ : SL(2, ℤ), redGL N γ = g := by
  obtain ⟨γ, hγ⟩ := GlobalTheory.specialLinearGroup_map_zmod_surjective (Fin 2) N ⟨(g : Matrix (Fin 2) (Fin 2) (ZMod N)), hg⟩
  refine ⟨γ, Units.ext ?_⟩
  show ((Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ) : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = g
  rw [hγ]; rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dg_conj_lift : ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ), (∀ γ : SL(2, ℤ), ∃ γ' : SL(2, ℤ), dg u * redGL N γ' = redGL N γ * dg u) ∧ ∀ γ' : SL(2, ℤ), ∃ γ : SL(2, ℤ), dg u * redGL N γ' = redGL N γ * dg u := by
  intro N _ u
  have hdet : ∀ γ : SL(2, ℤ), Matrix.det ((redGL N γ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
    intro γ
    exact (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ).2
  have hconj : ∀ (a g : GL (Fin 2) (ZMod N)), Matrix.det ((g : Matrix (Fin 2) (Fin 2) (ZMod N))) = 1 →
      Matrix.det (((a⁻¹ * g * a : GL (Fin 2) (ZMod N))) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
    intro a g hg
    simp only [Units.val_mul, Matrix.det_mul]
    rw [hg, mul_one, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  refine ⟨fun γ => ?_, fun γ' => ?_⟩
  · obtain ⟨γ', h⟩ := exists_redGL_eq _ (hconj (dg u) (redGL N γ) (hdet γ))
    refine ⟨γ', ?_⟩
    rw [h]; group
  · obtain ⟨γ, h⟩ := exists_redGL_eq _ (hconj (dg u)⁻¹ (redGL N γ') (hdet γ'))
    refine ⟨γ, ?_⟩
    rw [h]; group

end GlobalTheory.FN
