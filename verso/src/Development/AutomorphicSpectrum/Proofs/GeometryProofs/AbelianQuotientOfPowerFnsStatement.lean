import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientOfPowerFns
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QQuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.AbQ.exists_abQuot` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FAbelianQuotientOfPowerFns.lean&line=174#L174)
-/
theorem _root_.GlobalTheory.T.abelian_quotient_of_power_fns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), PowFns t → ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X), GeomPF t x → Nonempty (AbQuot t x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AbQ.exists_abQuot | exact GlobalTheory.CompanionTheory.Ar.AbQ.exists_abQuot | (intros; apply GlobalTheory.CompanionTheory.Ar.AbQ.exists_abQuot <;> assumption)
