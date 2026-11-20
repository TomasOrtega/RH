import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionUniformisingSpaceIsType
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLieConditionUniformisingSpaceIsType.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.lieCondition_uniformisingSpace_isType : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL (D' : PLat D.O D.inv) t Q e, UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → b.IsType σ ρ := by
  first | exact @GlobalTheory.UPel.HT.LieType.lie_isType | exact GlobalTheory.UPel.HT.LieType.lie_isType | (intros; apply GlobalTheory.UPel.HT.LieType.lie_isType <;> assumption)
