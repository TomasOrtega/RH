import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitLatticesIsoFormsProportionalRamification
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Poinc.TraitUniq.traitUniq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTraitLatticesIsoFormsProportionalRamification.lean&line=136#L136)
-/
theorem _root_.GlobalTheory.T.trait_lattices_iso_forms_proportional_ramification : TraitUniqSt := by
  first | exact @GlobalTheory.Poinc.TraitUniq.traitUniq | exact GlobalTheory.Poinc.TraitUniq.traitUniq | (intros; apply GlobalTheory.Poinc.TraitUniq.traitUniq <;> assumption)
