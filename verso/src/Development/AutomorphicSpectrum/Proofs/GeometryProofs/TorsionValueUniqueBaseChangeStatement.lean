import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionValueUniqueBaseChange
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Sl.TorsExist.torsVal_existsUnique` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FTorsionValueUniqueBaseChange.lean&line=165#L165)
-/
theorem _root_.GlobalTheory.T.torsion_value_unique_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (n : ℕ) (s : Out.H0 D.t.PP.L n) (F : Type) [Field F] (b : Sp F ⟶ Sp (𝓞 L)) (y : Over.mk b ⟶ D.t.G) (N : ℕ), 1 ≤ N → y ^ N = 1 → (∃! T : F, TorsVal D.t.PP s y N T) ∧ ∀ (F' : Type) [Field F'] (f : F →+* F') (y' : Over.mk (spMap f ≫ b) ⟶ D.t.G) (T : F), y'.left = spMap f ≫ y.left → TorsVal D.t.PP s y N T → TorsVal D.t.PP s y' N (f T) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.TorsExist.torsVal_existsUnique | exact GlobalTheory.CompanionTheory.Ar.Sl.TorsExist.torsVal_existsUnique | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.TorsExist.torsVal_existsUnique <;> assumption)
