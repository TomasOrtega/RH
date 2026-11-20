import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonCharacterLatticeOfGoodReductionTrait
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSubsingletonCharacterLatticeOfGoodReductionTrait.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.subsingleton_characterLattice_of_goodReduction_trait : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F) (ξ : Sp T.V ⟶ F.X), jK T.V ≫ ξ = T.y → Subsingleton T.D.toPre.X := by
  first | exact @GlobalTheory.Poinc.GoodRed.subsingleton_lattice_of_extends | exact GlobalTheory.Poinc.GoodRed.subsingleton_lattice_of_extends | (intros; apply GlobalTheory.Poinc.GoodRed.subsingleton_lattice_of_extends <;> assumption)
