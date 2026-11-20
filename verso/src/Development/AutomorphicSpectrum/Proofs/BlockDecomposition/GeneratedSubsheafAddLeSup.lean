import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.TwGen

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem imageSubobject_add_le {C : Type*} [Category C] [Preadditive C] [HasImages C]
    [HasBinaryCoproducts C] {A B : C} (f g : A ⟶ B) :
    imageSubobject (f + g) ≤ imageSubobject f ⊔ imageSubobject g := by
  have key : ∀ h : A ⟶ B, (imageSubobject h).Factors h := fun h => by
    have := Subobject.factors_comp_arrow (P := imageSubobject h) (factorThruImageSubobject h)
    rwa [imageSubobject_arrow_comp] at this
  have h := Subobject.factors_add f g
    (Subobject.factors_of_le f le_sup_left (key f)) (Subobject.factors_of_le g le_sup_right (key g))
  exact imageSubobject_le (f + g) _ (Subobject.factorThru_arrow _ _ h)

/- English proof (translation)
By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem sectionHom_add {X : Scheme.{0}} {F : X.Modules} (b c : Γ(F, ⊤)) :
    GlobalTheory.QCoh.sectionHom (b + c) = GlobalTheory.QCoh.sectionHom b + GlobalTheory.QCoh.sectionHom c := by
  ext V a
  change GlobalTheory.QCoh.structureModuleSectionsEquiv V a • GlobalTheory.Twist.resM F (le_top : V ≤ ⊤) (b + c) =
    GlobalTheory.QCoh.structureModuleSectionsEquiv V a • GlobalTheory.Twist.resM F (le_top : V ≤ ⊤) b +
      GlobalTheory.QCoh.structureModuleSectionsEquiv V a • GlobalTheory.Twist.resM F (le_top : V ≤ ⊤) c
  rw [map_add, smul_add]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem genHom_add {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules}
    (n : ℤ) (b c : Γ(GlobalTheory.twistZ P H n, ⊤)) :
    genHom hH n (b + c) = genHom hH n b + genHom hH n c := by
  have h : GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.QCoh.sectionHom (b + c)) =
      GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.QCoh.sectionHom b) +
        GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.QCoh.sectionHom c) := by
    rw [sectionHom_add]
    exact (GlobalTheory.twistFunctor (GlobalTheory.lbZPow H (-n))).map_add
  simp only [genHom, h, Preadditive.add_comp]

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem genSub_add_le {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules}
    (n : ℤ) (b c : Γ(GlobalTheory.twistZ P H n, ⊤)) :
    genSub hH n (b + c) ≤ genSub hH n b ⊔ genSub hH n c := by
  unfold genSub
  simp only [genHom_add]
  exact imageSubobject_add_le _ _

end GlobalTheory.CompanionTheory.GE.TwGen
