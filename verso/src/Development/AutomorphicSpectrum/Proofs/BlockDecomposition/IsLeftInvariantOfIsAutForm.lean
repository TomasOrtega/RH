import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.LeftInv

/- English proof (translation)
The claim follows from `Units.ext (Matrix.ext fun _ _ => rfl)`.
-/
theorem ratGL_eq_diagonal (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (γ : GL (Fin a) E) : ratGL E a γ = AdelicGLn.diagonal E a γ :=
  Units.ext (Matrix.ext fun _ _ => rfl)

/- English proof (translation)
Introduce `E _ _ _ a φ h γ g`. Rewrite using `[← ratGL_eq_diagonal]`. Conclude with `h.left γ g`.
-/
theorem isLeftInvariant_of_isAutForm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    (a : ℕ) (φ : Sm E a), IsAutForm φ → AutomorphicForm.IsLeftInvariant φ.1 := by
  intro E _ _ _ a φ h γ g
  rw [← ratGL_eq_diagonal]
  exact h.left γ g

end GlobalTheory.CompanionTheory.LeftInv
