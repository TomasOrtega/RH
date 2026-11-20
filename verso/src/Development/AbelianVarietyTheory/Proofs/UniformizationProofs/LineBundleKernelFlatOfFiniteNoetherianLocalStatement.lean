import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleKernelFlatOfFiniteNoetherianLocal
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.StabFlatLocal.flat_of_isFinite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUniformizationProofs%2FLineBundleKernelFlatOfFiniteNoetherianLocal.lean&line=110#L110)
-/
theorem _root_.GlobalTheory.T.lineBundleKernel_flat_of_finite_noetherian_local : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ L : LB B.left, L.IsLB → (∃ t : LB.Gen (Theta B L), t.IsGen) → ∀ (H : Over (Sp V)) (j : H ⟶ B), IsClosedImmersion j.left → (∀ (T : Over (Sp V)) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) → IsFinite H.hom → Flat H.hom := by
  first | exact @GlobalTheory.StabFlatLocal.flat_of_isFinite | exact GlobalTheory.StabFlatLocal.flat_of_isFinite | (intros; apply GlobalTheory.StabFlatLocal.flat_of_isFinite <;> assumption)
