import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem matrixChar_iff_isChar : ∀ (G : Type) [Group G] (χ : G → ℂ),
    (∃ (n : ℕ) (ρ : G →* GL (Fin n) ℂ), ∀ x, χ x = Matrix.trace (ρ x : Matrix (Fin n) (Fin n) ℂ)) ↔
      IsChar ℂ ℂ χ := by
  intro G _ χ
  constructor
  · rintro ⟨n, ρ, hρ⟩
    refine ⟨n, (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)).toRingEquiv.toMonoidHom.comp
      ((Units.coeHom _).comp ρ), fun g => ?_⟩
    rw [hρ g]
    show _ = Representation.character _ g
    rw [Representation.character,
      LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix']
    change _ = (LinearMap.toMatrix' (Matrix.toLin' _)).trace
    rw [LinearMap.toMatrix'_toLin']
    rfl
  · rintro ⟨n, ρ, hρ⟩
    refine ⟨n, Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp ρ.asGroupHom, fun g => ?_⟩
    rw [hρ g]
    show Representation.character _ g = _
    rw [Representation.character,
      LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix']
    rfl

end GlobalTheory.BI
