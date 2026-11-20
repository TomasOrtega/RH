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
Use `(genericPoint_spec X).image f.continuous` as an intermediate fact. Rewrite `this` using `[Set.image_univ, f.denseRange.closure_range]`. Conclude with `this.eq (genericPoint_spec Y)`.
-/
theorem apply_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  have := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at this
  exact this.eq (genericPoint_spec Y)

/- English proof (translation)
Rewrite using `[apply_genericPoint f]`. Conclude with `Field.toIsField Y.functionField`.
-/
theorem isField_stalk_apply {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [IsDominant f] : IsField (Y.presheaf.stalk (f (genericPoint X))) := by
  rw [apply_genericPoint f]
  exact Field.toIsField Y.functionField

/- English proof (translation)
Use `letI := hA.toField`. Use `letI := hB.toField`. Use `letI := f.hom.toAlgebra`. Use `letI := g.hom.toAlgebra`. Use `letI := (f ≫ g).hom.toAlgebra`.

Use `haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Conclude with `(Module.finrank_mul_finrank A B C).symm`.
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
Introduce `T'' T' T _ _ _ ρ' ρ d' d h' h`. Use `h'.isDominant` as an intermediate fact. Use `h.isDominant` as an intermediate fact. Use `⟨inferInstance, Nat.mul_pos h'.pos h.pos, ?_⟩` and prove the remaining obligations. Establish `e'` using `h'.finrank_eq`.

Establish `e` using `h.finrank_eq`. Establish `hF₁ : IsField (T.presheaf.stalk (ρ (ρ' (genericPoint T''))))`. Rewrite using `[apply_genericPoint ρ']`. Conclude with `isField_stalk_apply ρ`. Establish `key` using `finrank_comp (ρ.stalkMap (ρ' (genericPoint T''))) (ρ'.stalkMap (genericPoint T'')) hF₁ (isField_stalk_apply ρ')`.

Rewrite using `[Scheme.Hom.stalkMap_comp]`. Use `key.trans ?_` and prove the remaining obligations. Rewrite using `[e', mul_comm]`. Use `congr 1`. Rewrite using `[← e]`.

Rewrite using `[apply_genericPoint ρ']`.
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
