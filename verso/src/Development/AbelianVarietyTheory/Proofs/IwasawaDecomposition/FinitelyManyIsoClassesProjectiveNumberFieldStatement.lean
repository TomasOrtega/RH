import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitelyManyIsoClassesProjectiveNumberField
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ProjModFinIso.finitely_many_iso_classes` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFinitelyManyIsoClassesProjectiveNumberField.lean&line=121#L121)
-/
theorem _root_.GlobalTheory.T.finitely_many_iso_classes_projective_numberField : ∀ (E : Type) [Field E] [NumberField E] (q : ℕ), ∃ (n : ℕ) (Y : Fin n → ModuleCat.{0} (𝓞 E)), ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∃ k, Nonempty (X ≃ₗ[𝓞 E] Y k) := by
  first | exact @GlobalTheory.ProjModFinIso.finitely_many_iso_classes | exact GlobalTheory.ProjModFinIso.finitely_many_iso_classes | (intros; apply GlobalTheory.ProjModFinIso.finitely_many_iso_classes <;> assumption)
