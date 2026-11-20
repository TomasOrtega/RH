import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveRelationUniqueQuotient
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LineQuot.exists_factor_of_rel` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProjectiveRelationUniqueQuotient.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.projective_relation_unique_quotient : ∀ (k : Type) [CommRing k] (N : ℕ) (T : Scheme.{0}) (L Q Q' : T.Modules) (s : Fin (N + 1) → (L ⟶ Q)) (s' : Fin (N + 1) → (L ⟶ Q')) (φ : T ⟶ PSpace k N), IsVB L 1 → IsVB Q 1 → JointEpi s → Gen s → Rel φ s → Rel φ s' → ∃ e : Q ⟶ Q', ∀ j, s j ≫ e = s' j := by
  first | exact @GlobalTheory.LineQuot.exists_factor_of_rel | exact GlobalTheory.LineQuot.exists_factor_of_rel | (intros; apply GlobalTheory.LineQuot.exists_factor_of_rel <;> assumption)
