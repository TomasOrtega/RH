import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModuliTwistAutomorphism
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.moduli_twist_phi` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FModuliTwistAutomorphism.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.moduli_twist_automorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : HostAut H) (a : TwIso D g) (h : TwOK Xo.univ g a), ∃ Φ : Xo.X ⟶ Xo.X, Φ ≫ Xo.s = Xo.s ∧ Nonempty (ObjMap (twistObj Xo.univ g a h) Xo.univ Φ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.moduli_twist_phi | exact GlobalTheory.CompanionTheory.Ar.moduli_twist_phi | (intros; apply GlobalTheory.CompanionTheory.Ar.moduli_twist_phi <;> assumption)
