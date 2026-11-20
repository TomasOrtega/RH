import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionPairRepresentative
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PairScheme.pairRep_exists` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FExistsTorsionPairRepresentative.lean&line=144#L144)
-/
theorem _root_.GlobalTheory.T.exists_torsion_pair_representative : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ y : P.D.toPre.X, ∃ (N : Over W.toScheme) (p₀ : QkPtW P.D.toPre W ψW k N), PairRep ψW k y N p₀ := by
  first | exact @GlobalTheory.PairScheme.pairRep_exists | exact GlobalTheory.PairScheme.pairRep_exists | (intros; apply GlobalTheory.PairScheme.pairRep_exists <;> assumption)
