import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitFiniteResidueCharZeroAvoiding
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_trait_finite_residueField_charZero_avoiding` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsTraitFiniteResidueCharZeroAvoiding.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.exists_trait_finiteResidue_charZero_avoiding : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B] (m : Ideal B) (h : B), m.IsMaximal → h ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : CharZero V) (t : B →+* V), IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ Finite (IsLocalRing.ResidueField V) ∧ t h ≠ 0 ∧ (IsLocalRing.maximalIdeal V).comap t = m := by
  first | exact @GlobalTheory.exists_trait_finite_residueField_charZero_avoiding | exact GlobalTheory.exists_trait_finite_residueField_charZero_avoiding | (intros; apply GlobalTheory.exists_trait_finite_residueField_charZero_avoiding <;> assumption)
