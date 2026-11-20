import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenFiniteComp

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem apply_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  have := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at this
  exact this.eq (genericPoint_spec Y)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isField_stalk_apply {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [IsDominant f] : IsField (Y.presheaf.stalk (f (genericPoint X))) := by
  rw [apply_genericPoint f]
  exact Field.toIsField Y.functionField

/- English proof (translation)
Equip the data with the indicated structure. Equip the data with the indicated structure. Equip the data with the indicated structure. Equip the data with the indicated structure. Equip the data with the indicated structure.

A detailed English derivation is pending.
-/
theorem finrank_comp {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (hA : IsField A)
    (hB : IsField B) :
    (letI := (f ≫ g).hom.toAlgebra; Module.finrank A C) =
      (letI := f.hom.toAlgebra; Module.finrank A B) * (letI := g.hom.toAlgebra; Module.finrank B C) := by
  letI := hA.toField
  letI := hB.toField
  letI := f.hom.toAlgebra
  letI := g.hom.toAlgebra
  letI := (f ≫ g).hom.toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact (Module.finrank_mul_finrank A B C).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isGenFinite_comp : ∀ (T'' T' T : Scheme.{0}) [IsIntegral T''] [IsIntegral T'] [IsIntegral T] (ρ' : T'' ⟶ T') (ρ : T' ⟶ T) (d' d : ℕ), IsGenFinite ρ' d' → IsGenFinite ρ d → IsGenFinite (ρ' ≫ ρ) (d' * d) := by
  intro T'' T' T _ _ _ ρ' ρ d' d h' h
  have := h'.isDominant
  have := h.isDominant
  refine ⟨inferInstance, Nat.mul_pos h'.pos h.pos, ?_⟩
  have e' := h'.finrank_eq
  have e := h.finrank_eq
  have hF₁ : IsField (T.presheaf.stalk (ρ (ρ' (genericPoint T'')))) := by
    rw [apply_genericPoint ρ']
    exact isField_stalk_apply ρ
  have key := finrank_comp (ρ.stalkMap (ρ' (genericPoint T''))) (ρ'.stalkMap (genericPoint T''))
    hF₁ (isField_stalk_apply ρ')
  rw [Scheme.Hom.stalkMap_comp]
  refine key.trans ?_
  rw [e', mul_comm]
  congr 1
  rw [← e]
  rw [apply_genericPoint ρ']

end GlobalTheory.GenFiniteComp
