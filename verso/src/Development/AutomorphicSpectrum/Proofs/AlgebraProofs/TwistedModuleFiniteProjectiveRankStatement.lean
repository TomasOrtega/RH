import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwistedModuleFiniteProjectiveRank
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.TwModule.twMod_finite_projective_finrank` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FTwistedModuleFiniteProjectiveRank.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.twisted_module_finite_projective_rank : ∀ (O : Type) [CommRing O] [IsDomain O] (s : O ≃+* O) (L : Type) [AddCommGroup L] [Module O L] [Module.Finite O L] [Module.Projective O L], Module.Finite O (TwMod s L) ∧ Module.Projective O (TwMod s L) ∧ Module.finrank O (TwMod s L) = Module.finrank O L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwModule.twMod_finite_projective_finrank | exact GlobalTheory.CompanionTheory.Ar.TwModule.twMod_finite_projective_finrank | (intros; apply GlobalTheory.CompanionTheory.Ar.TwModule.twMod_finite_projective_finrank <;> assumption)
