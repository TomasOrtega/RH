import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLocalRingEssFiniteTypeInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeSpanSupPow
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FModelLocalRingEssFiniteTypeInt.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.modelLocalRing_essFiniteType_int : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (x : M.Z), Algebra.EssFiniteType ℤ (M.O x) := by
  first | exact @GlobalTheory.Izumi.essFiniteType_int_O | exact GlobalTheory.Izumi.essFiniteType_int_O | (intros; apply GlobalTheory.Izumi.essFiniteType_int_O <;> assumption)
