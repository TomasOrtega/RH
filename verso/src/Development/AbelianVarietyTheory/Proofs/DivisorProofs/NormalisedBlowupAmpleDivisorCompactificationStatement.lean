import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedBlowupAmpleDivisorCompactification
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PoincTop.poinSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormalisedBlowupAmpleDivisorCompactification.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.normalisedBlowup_ampleDivisor_compactification : PoinSt := by
  first | exact @GlobalTheory.PoincTop.poinSt | exact GlobalTheory.PoincTop.poinSt | (intros; apply GlobalTheory.PoincTop.poinSt <;> assumption)
