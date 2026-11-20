import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperInfIdealSheaves
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GE.Union.isProper_inf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FProperInfIdealSheaves.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.proper_inf_ideal_sheaves : ∀ {X S : Scheme.{0}} (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] (T₁ T₂ : X.IdealSheafData), IsProper (T₁.subschemeι ≫ f) → IsProper (T₂.subschemeι ≫ f) → IsProper ((T₁ ⊓ T₂).subschemeι ≫ f) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Union.isProper_inf | exact GlobalTheory.CompanionTheory.GE.Union.isProper_inf | (intros; apply GlobalTheory.CompanionTheory.GE.Union.isProper_inf <;> assumption)
