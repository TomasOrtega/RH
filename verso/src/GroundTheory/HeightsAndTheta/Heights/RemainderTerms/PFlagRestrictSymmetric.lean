import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem rename_comp_restrictToBlock (f N : ℕ) (τ : Fin f) (π : Equiv.Perm (Fin N)) :
    (rename π).comp (restrictToBlock f N τ) =
      (restrictToBlock f N τ).comp (blockPermute f N (Function.update 1 τ π)) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨σ, i⟩
  by_cases h : σ = τ
  · subst h
    simp [restrictToBlock, blockPermute]
  · simp [restrictToBlock, blockPermute, h]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem FlagRestrictSymmetric.proof : FlagRestrictSymmetric.Statement := by
  intro f N τ R hR π
  have key := congrArg (fun φ : RootRing f N →ₐ[ℚ] MvPolynomial (Fin N) ℚ => φ R)
    (rename_comp_restrictToBlock f N τ π)
  simp only [AlgHom.comp_apply] at key
  rw [key, hR]

end RestTerms

end GroundTheory.Heights₂.Heights
