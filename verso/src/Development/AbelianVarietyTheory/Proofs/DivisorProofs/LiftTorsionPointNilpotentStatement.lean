import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftTorsionPointNilpotent
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.FiniteLocalLifts.SmLift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorsionLift.exists_torsion_lift` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLiftTorsionPointNilpotent.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.lift_torsion_point_nilpotent : ∀ {R : Type} [CommRing R] [Algebra ℂ R] (π : R →ₐ[ℂ] ℂ), (∀ x ∈ RingHom.ker π, IsNilpotent x) →
    ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (G₀ : Over (Sp ℂ)) [GrpObj G₀] (i : G₀.left ⟶ G.left), IsGrpPullback G₀ G (spMap (π : R →+* ℂ)) i →
    ∀ (N : ℕ), 1 ≤ N → ∀ (p : 𝟙_ (Over (Sp ℂ)) ⟶ G₀), p ^ N = 1 →
    ∃ q : 𝟙_ (Over (Sp R)) ⟶ G, q ^ N = 1 ∧ p.left ≫ i = spMap (π : R →+* ℂ) ≫ q.left := by
  first | exact @GlobalTheory.TorsionLift.exists_torsion_lift | exact GlobalTheory.TorsionLift.exists_torsion_lift | (intros; apply GlobalTheory.TorsionLift.exists_torsion_lift <;> assumption)
