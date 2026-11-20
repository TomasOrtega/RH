import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveMapUniversalLine
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LineQuot.exists_taut_quot` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProjectiveMapUniversalLine.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.projective_map_universal_line : ∀ (k : Type) [CommRing k] (N : ℕ) (T : Scheme.{0}) (φ : T ⟶ PSpace k N) (L : T.Modules), IsVB L 1 → ∃ (Q : T.Modules) (s : Fin (N + 1) → (L ⟶ Q)), IsVB Q 1 ∧ JointEpi s ∧ Rel φ s := by
  first | exact @GlobalTheory.LineQuot.exists_taut_quot | exact GlobalTheory.LineQuot.exists_taut_quot | (intros; apply GlobalTheory.LineQuot.exists_taut_quot <;> assumption)
