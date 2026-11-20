import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibLieLatticeFull
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
open NumberField ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LieHt.SemiFib.full_lieLat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSemiFibLieLatticeFull.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.semiFib_lie_lattice_full : ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K), Full F.lieLat := by
  first | exact @GlobalTheory.LieHt.SemiFib.full_lieLat | exact GlobalTheory.LieHt.SemiFib.full_lieLat | (intros; apply GlobalTheory.LieHt.SemiFib.full_lieLat <;> assumption)
