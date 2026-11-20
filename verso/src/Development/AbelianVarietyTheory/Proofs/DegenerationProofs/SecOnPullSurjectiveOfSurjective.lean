import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

/- English proof (translation)
Introduce `A A' _ _ g hg X X' f f' β hβ H hH D hD y`. Use `letI := g.toAlgebra`. Take `⟨z, hz⟩` from `(SecOnR.baseChangeHom_bijective (R := A) (R' := A') hH hβ hD rfl).2 y`. Take `⟨x, rfl⟩` from `TensorProduct.mk_surjective A (SecOnR f H D) A' hg z`. Use `⟨x, ?_⟩` and prove the remaining obligations.

Establish `h` using `(SecOnR.baseChangeHom_tmul (R := A) (R' := A') hβ.w le_rfl 1 x).symm.trans hz`. Rewrite `h` using `[one_smul]`. Conclude with `(SecOn.pullLE_self β x).symm.trans h`.
-/
theorem secOn_pull_surjective_of_surjective :
    ∀ (A A' : Type) [CommRing A] [CommRing A'] (g : A →+* A'), Function.Surjective g → ∀ (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of A')) (β : X' ⟶ X), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ H : LB X, H.IsLB → ∀ D : X.Opens, IsAffineOpen D → Function.Surjective (SecOn.pull H β D) := by
  intro A A' _ _ g hg X X' f f' β hβ H hH D hD y
  letI := g.toAlgebra
  obtain ⟨z, hz⟩ := (SecOnR.baseChangeHom_bijective (R := A) (R' := A') hH hβ hD rfl).2 y
  obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective A (SecOnR f H D) A' hg z
  refine ⟨x, ?_⟩
  have h := (SecOnR.baseChangeHom_tmul (R := A) (R' := A') hβ.w le_rfl 1 x).symm.trans hz
  rw [one_smul] at h
  exact (SecOn.pullLE_self β x).symm.trans h

end GlobalTheory.AbLaw
