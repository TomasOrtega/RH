import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerI5OfFibreInput
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Ht.TopLower.i5_of_hasRef_of_fibreInput` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FTowerI5OfFibreInput.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.tower_i5_of_fibre_input : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (j k : ℕ) (T : RootTower Ψ (j + 1 + (k + 1))) (II : IntersectionSystem) (R : T.Comp → RootModel Ψ (j + 1 + (k + 1))), IsIntersectionSystem II → HasRef T R → (∀ c, AmpleQ (R c).y (R c).A.a ∧ FlatUnit (R c) ∧ FibreInput (R c)) → T.I5 II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.TopLower.i5_of_hasRef_of_fibreInput | exact GlobalTheory.CompanionTheory.Ar.Ht.TopLower.i5_of_hasRef_of_fibreInput | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.TopLower.i5_of_hasRef_of_fibreInput <;> assumption)
