import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingLocusClosedSubscheme
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ZeroLocus.exists_closed_zeroLocus` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FVanishingLocusClosedSubscheme.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.vanishing_locus_closed_subscheme : ∀ (Y : Scheme.{0}) (G Q : Y.Modules) (u : G ⟶ Q), G.IsQuasicoherent → IsVB Q 1 → ∃ (Z : Scheme.{0}) (j : Z ⟶ Y), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (h : T ⟶ Y), (Scheme.Modules.pullback h).map u = 0 ↔ ∃ h' : T ⟶ Z, h' ≫ j = h := by
  first | exact @GlobalTheory.ZeroLocus.exists_closed_zeroLocus | exact GlobalTheory.ZeroLocus.exists_closed_zeroLocus | (intros; apply GlobalTheory.ZeroLocus.exists_closed_zeroLocus <;> assumption)
