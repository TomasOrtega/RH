import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities.
-/
theorem finrank_eq_card_kernel_points_of_etale :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ φ : B ⟶ B, ∀ [IsFinite φ.left] [Etale φ.left], ∀ x : B.left, φ.left.finrank x = Nat.card {y : 𝟙_ _ ⟶ B // y ≫ φ = 1} := by
  intro K _ _ B _ _ hB φ _ _ x
  have := hB.geomConnected
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace_of_subsingleton B.hom
  let o : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B := 1
  let t : Spec (CommRingCat.of K) ⟶ B.left := o.left
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  have ht : t ≫ B.hom = 𝟙 _ := Over.w o
  rw [(Scheme.Hom.isLocallyConstant_finrank φ.left).apply_eq_of_preconnectedSpace x (t z),
    ← (GlobalTheory.FinEt.card_points_eq_finrank φ.left t z).2]
  refine Nat.card_congr
    { toFun := fun y ↦ ⟨Over.homMk y.1 ?_, Over.OverMorphism.ext y.2⟩
      invFun := fun y ↦ ⟨y.1.left, congrArg CommaMorphism.left y.2⟩
      left_inv := fun y ↦ rfl
      right_inv := fun y ↦ Subtype.ext (Over.OverMorphism.ext rfl) }
  change y.1 ≫ B.hom = 𝟙 _
  rw [← Over.w φ, ← Category.assoc, y.2, ht]

end GlobalTheory
