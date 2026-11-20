import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnramTorsion.psiUnitOn_of_unramified` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FPsiUnitOnOfFixedOverUnramifiedExtension.lean&line=324#L324)
-/
theorem _root_.GlobalTheory.T.psiUnitOn_of_fixed_over_unramified_extension : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (D : DegPre R), D.TauBimult → D.PsiEven → ∀ (P : PrimeSpectrum R), P.asIdeal.height = 1 → ∀ (n : ℕ), 2 ≤ n → (∀ (j : ℕ), ∃ (T' : Subring (AlgebraicClosure (FractionRing R))) (_ : IsDiscreteValuationRing T') (f : Localization.AtPrime P.asIdeal →+* T'), (∀ r : R, (f (algebraMap R _ r) : AlgebraicClosure (FractionRing R)) = algebraMap (FractionRing R) _ (algebraMap R _ r)) ∧ (∀ π, Irreducible π → Irreducible (f π)) ∧ ∀ (σ : AlgebraicClosure (FractionRing R) ≃+* AlgebraicClosure (FractionRing R)), (∀ x ∈ T', σ x = x) → ∀ p q : QkPt D (AlgebraicClosure (FractionRing R)) (n ^ j), QkExt σ.toRingHom p q → QkPt.Equiv D _ p q) → ∀ y, ∃ V : (Sp R).Opens, P ∈ V ∧ PsiUnitOn D y V := by
  first | exact @GlobalTheory.UnramTorsion.psiUnitOn_of_unramified | exact GlobalTheory.UnramTorsion.psiUnitOn_of_unramified | (intros; apply GlobalTheory.UnramTorsion.psiUnitOn_of_unramified <;> assumption)
