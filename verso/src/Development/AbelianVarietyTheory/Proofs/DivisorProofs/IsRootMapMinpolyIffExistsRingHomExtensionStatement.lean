import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRootMapMinpolyIffExistsRingHomExtension

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsRootMapMinpolyIffExistsRingHomExtension.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.isRoot_map_minpoly_iff_exists_ringHom_extension : ∀ (A B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B], Function.Injective (algebraMap A B) → ∀ (g : B) (φ : A →+* ℂ) (z : ℂ), ((minpoly A g).map φ).IsRoot z ↔ ∃ x : B →+* ℂ, x.comp (algebraMap A B) = φ ∧ x g = z := by
  first | exact @GlobalTheory.isRoot_map_minpoly_iff_exists_ringHom | exact GlobalTheory.isRoot_map_minpoly_iff_exists_ringHom | (intros; apply GlobalTheory.isRoot_map_minpoly_iff_exists_ringHom <;> assumption)
