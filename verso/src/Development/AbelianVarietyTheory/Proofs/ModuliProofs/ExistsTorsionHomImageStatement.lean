import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionHomImage
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FExistsTorsionHomImage.lean&line=96#L96)
-/
theorem _root_.GlobalTheory.T.exists_torsion_hom_image : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ y N p₀, PairRep ψW k y N p₀ → ∃ v : overW W N ⟶ t.G, v ^ k = 1 ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : Sp F ⟶ N.left), OverGen F (overW W N) x → ∀ q : QkPt P.D.toPre F k, QkPtW.IsPullF F x p₀ q → IsImage P F k q (x ≫ v.left) := by
  first | exact @GlobalTheory.TorsRepMap.exists_repMap | exact GlobalTheory.TorsRepMap.exists_repMap | (intros; apply GlobalTheory.TorsRepMap.exists_repMap <;> assumption)
