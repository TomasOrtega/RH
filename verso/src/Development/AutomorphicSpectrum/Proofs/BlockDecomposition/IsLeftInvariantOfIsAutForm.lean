import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.LeftInv

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ratGL_eq_diagonal (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (γ : GL (Fin a) E) : ratGL E a γ = AdelicGLn.diagonal E a γ :=
  Units.ext (Matrix.ext fun _ _ => rfl)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isLeftInvariant_of_isAutForm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    (a : ℕ) (φ : Sm E a), IsAutForm φ → AutomorphicForm.IsLeftInvariant φ.1 := by
  intro E _ _ _ a φ h γ g
  rw [← ratGL_eq_diagonal]
  exact h.left γ g

end GlobalTheory.CompanionTheory.LeftInv
