import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isModel_id (X : Scheme.{0}) [IsIntegral X] : IsModel (𝟙 X) (RingHom.id X.functionField) where
  gen := rfl
  deg := Scheme.Hom.residueDegree_id _
  compat y a := by
    simp only [RingHom.id_apply, Scheme.Hom.stalkMap_id]
    rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem IsModel.comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z] {π : Y ⟶ X} {π' : Z ⟶ Y}
    {φ : X.functionField →+* Y.functionField} {φ' : Y.functionField →+* Z.functionField}
    (h : IsModel π φ) (h' : IsModel π' φ') : IsModel (π' ≫ π) (φ'.comp φ) where
  gen := by
    show π (π' (genericPoint Z)) = genericPoint X
    rw [h'.gen, h.gen]
  deg := by
    rw [GlobalTheory.CurveDegreesCompare.residueDegree_comp π' π (genericPoint Z), h'.deg]
    rw [h'.gen, h.deg]
  compat z a := by
    refine (congrArg φ' (h.compat (π' z) a)).trans ((h'.compat z _).trans ?_)
    rw [Scheme.Hom.stalkMap_comp]
    rfl

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem isModel_id_and_comp : ∀ (X Y Z : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (π : Y ⟶ X) (π' : Z ⟶ Y)
    (φ : X.functionField →+* Y.functionField) (φ' : Y.functionField →+* Z.functionField),
    IsModel (𝟙 X) (RingHom.id _) ∧ (IsModel π φ → IsModel π' φ' → IsModel (π' ≫ π) (φ'.comp φ)) :=
  fun X _ _ _ _ _ _ _ _ _ => ⟨isModel_id X, fun h h' => h.comp h'⟩

end GlobalTheory.HSNef
