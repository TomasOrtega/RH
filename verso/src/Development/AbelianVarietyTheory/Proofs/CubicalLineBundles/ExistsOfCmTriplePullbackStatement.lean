import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOfCmTriplePullback
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

/- English proof (citation)
Apply `GlobalTheory.CM.PAT.exists_of_sabMap` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCubicalLineBundles%2FExistsOfCmTriplePullback.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exists_of_cmTriple_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (T : PAT H S) (t' : SAB H S') (m : SABMap t' T.t f), (∃ T' : PAT H S', T'.t = t' ∧ T'.g = T.g) ∧ LBIso (T.t.PP.L.pull m.φ) t'.PP.L := by
  first | exact @GlobalTheory.CM.PAT.exists_of_sabMap | exact GlobalTheory.CM.PAT.exists_of_sabMap | (intros; apply GlobalTheory.CM.PAT.exists_of_sabMap <;> assumption)
