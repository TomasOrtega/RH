import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨σ, i⟩`. Distinguish the cases in `h : σ = τ`. Substitute `h` using the available equality. Simplify using `[restrictToBlock, blockPermute]`.

Simplify using `[restrictToBlock, blockPermute, h]`.
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
Introduce `f N τ R hR π`. Establish `key` using `congrArg (fun φ : RootRing f N →ₐ[ℚ] MvPolynomial (Fin N) ℚ => φ R) (rename_comp_restrictToBlock f N τ π)`. Simplify using `only [AlgHom.comp_apply] at key`. Rewrite using `[key, hR]`.
-/
theorem FlagRestrictSymmetric.proof : FlagRestrictSymmetric.Statement := by
  intro f N τ R hR π
  have key := congrArg (fun φ : RootRing f N →ₐ[ℚ] MvPolynomial (Fin N) ℚ => φ R)
    (rename_comp_restrictToBlock f N τ π)
  simp only [AlgHom.comp_apply] at key
  rw [key, hR]

end RestTerms

end GroundTheory.Heights₂.Heights
