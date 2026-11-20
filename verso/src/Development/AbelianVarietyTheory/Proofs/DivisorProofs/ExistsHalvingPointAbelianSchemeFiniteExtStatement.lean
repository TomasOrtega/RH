import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalvingPointAbelianSchemeFiniteExt
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsHalvingPointAbelianSchemeFiniteExt.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.exists_halving_point_abelianScheme_finite_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (a : 𝟙_ (Over (Sp R)) ⟶ B), IsCN R → IsAbelianScheme B → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (b : Over.mk (spMap ρ) ⟶ B), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ b ^ 2 = toUnit _ ≫ a := by
  first | exact @GlobalTheory.HalfPt.exists_half_point | exact GlobalTheory.HalfPt.exists_half_point | (intros; apply GlobalTheory.HalfPt.exists_half_point <;> assumption)
