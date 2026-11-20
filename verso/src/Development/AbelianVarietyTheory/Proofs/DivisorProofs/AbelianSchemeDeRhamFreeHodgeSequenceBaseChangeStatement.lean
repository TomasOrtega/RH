import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamFreeHodgeSequenceBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.abelianDeRham_free_hodge_baseChange` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAbelianSchemeDeRhamFreeHodgeSequenceBaseChange.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange : GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.AbelianDeRham.Free ∧ GlobalTheory.Published.AbelianDeRham.Hodge ∧ GlobalTheory.Published.AbelianDeRham.BaseChange := by
  first | exact @GlobalTheory.abelianDeRham_free_hodge_baseChange | exact GlobalTheory.abelianDeRham_free_hodge_baseChange | (intros; apply GlobalTheory.abelianDeRham_free_hodge_baseChange <;> assumption)
