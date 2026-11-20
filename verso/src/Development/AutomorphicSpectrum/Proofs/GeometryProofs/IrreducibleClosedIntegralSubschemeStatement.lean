import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IrreducibleClosedIntegralSubscheme
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToXQFst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FIrreducibleClosedIntegralSubscheme.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.irreducible_closed_integral_subscheme : ∀ (S : Scheme.{0}) (F : Set S), IsClosed F → IsIrreducible F →
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (i : Z ⟶ S), IsClosedImmersion i ∧ Set.range i = F ∧
      ∀ (k : Type) [Field k] (x : Sp k ⟶ S), x (IsLocalRing.closedPoint k) ∈ F → ∃ x' : Sp k ⟶ Z, x' ≫ i = x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.exists_integral_closed_subscheme | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.exists_integral_closed_subscheme | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.exists_integral_closed_subscheme <;> assumption)
