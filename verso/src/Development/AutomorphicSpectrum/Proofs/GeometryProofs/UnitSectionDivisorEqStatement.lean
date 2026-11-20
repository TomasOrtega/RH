import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitSectionDivisorEq
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FUnitSectionDivisorEq.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.unit_section_divisor_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (f g : MRing ι), IsUnitSec P f g → divSupp P f = divSupp P g ∧ (∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W) ∧ ∀ (n : ℕ) (L : Fin n → HermLine ι), vertR P L f = vertR P L g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.cycles_eq_of_isUnitSec | exact GlobalTheory.CompanionTheory.Ar.Flat.cycles_eq_of_isUnitSec | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.cycles_eq_of_isUnitSec <;> assumption)
