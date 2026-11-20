import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedWeierstrassPTorsion
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WpFam.ExpP.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHasQExpansionNormalizedWeierstrassPTorsion.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.hasQExpansion_normalizedWeierstrassPTorsion : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), HasQ N (wp N x) (cP N x) := by
  first | exact @GlobalTheory.WpFam.ExpP.main | exact GlobalTheory.WpFam.ExpP.main | (intros; apply GlobalTheory.WpFam.ExpP.main <;> assumption)
