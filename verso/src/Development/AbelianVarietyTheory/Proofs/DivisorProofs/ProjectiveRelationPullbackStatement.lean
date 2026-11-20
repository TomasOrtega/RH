import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveRelationPullback
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProjectiveRelationPullback.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.projective_relation_pullback : ∀ (k : Type) [CommRing k] (N : ℕ) (S T : Scheme.{0}) (g : S ⟶ T) (L Q : T.Modules) (s : Fin (N + 1) → (L ⟶ Q)) (φ : T ⟶ PSpace k N), IsVB L 1 → IsVB Q 1 → Rel φ s → Rel (g ≫ φ) fun j => (Scheme.Modules.pullback g).map (s j) := by
  first | exact @GlobalTheory.LineQuot.rel_pullback | exact GlobalTheory.LineQuot.rel_pullback | (intros; apply GlobalTheory.LineQuot.rel_pullback <;> assumption)
