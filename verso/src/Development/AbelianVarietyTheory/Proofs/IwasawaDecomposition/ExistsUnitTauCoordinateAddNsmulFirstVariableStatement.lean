import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitTauCoordinateAddNsmulFirstVariable
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsUnitTauCoordinateAddNsmulFirstVariable.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.exists_unit_tauCoordinate_add_nsmul_first_variable : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), D.TauBimult →
    ∀ (a z b : D.X) (k : ℕ) (x x' x'' : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D a b x →
      GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D z b x' → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D (a + k • z) b x'' →
      ∃ u : Rˣ, x'' = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * (x * x' ^ k) := by
  first | exact @GlobalTheory.TauShift.main | exact GlobalTheory.TauShift.main | (intros; apply GlobalTheory.TauShift.main <;> assumption)
