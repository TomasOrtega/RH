import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.FlagConnect

def Carries {B Y T : Scheme.{0}} (π : Y ⟶ B) {ι : Type} (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g)
    (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a)) : Prop :=
  ∀ a i, ∃ e : (Scheme.Modules.pullback g').obj ((fl a).F i) ≅ (fl' a).F i,
    e.hom ≫ (fl' a).ι i = (Scheme.Modules.pullback g').map ((fl a).ι i) ≫
      (Scheme.Modules.pullbackComp g' π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a)

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem isFlagBundle_iff {B Y : Scheme.{0}} (π : Y ⟶ B) {ι : Type} (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) :
    CovTest.IsFlagBundle π E n fl ↔ ∀ (T : Scheme.{0}) (g : T ⟶ B)
      (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a)),
      ∃! g' : T ⟶ Y, ∃ w : g' ≫ π = g, Carries π E n fl g' g w fl' := Iff.rfl

def carried {B Y T : Scheme.{0}} (π : Y ⟶ B) {ι : Type} (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g) :
    ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a) := fun a =>
  ((fl a).pull g').ofIso ((Scheme.Modules.pullbackComp g' π).app (E a) ≪≫ (Scheme.Modules.pullbackCongr w).app (E a))

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem carries_carried {B Y T : Scheme.{0}} (π : Y ⟶ B) {ι : Type} (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g) :
    Carries π E n fl g' g w (carried π E n fl g' g w) := fun a i =>
  ⟨Iso.refl _, by simp [carried, Vert.Flag.ofIso, Vert.Flag.pull]⟩

/- English proof (translation)
Substitute using the available equality. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem carries_comp {B Y T T' : Scheme.{0}} (π : Y ⟶ B) {ι : Type} (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g)
    (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a)) (h : T' ⟶ T) (k : T' ⟶ B) (v : h ≫ g = k)
    (fl'' : ∀ a, Vert.Flag ((Scheme.Modules.pullback k).obj (E a)) (n a)) (w' : (h ≫ g') ≫ π = k) :
    Carries π E n fl g' g w fl' → Carries g E n fl' h k v fl'' → Carries π E n fl (h ≫ g') k w' fl'' := by
  subst w v
  intro H₁ H₂ a i
  obtain ⟨e, he⟩ := H₁ a i
  obtain ⟨e', he'⟩ := H₂ a i
  refine ⟨(Scheme.Modules.pullbackComp h g').symm.app _ ≪≫ (Scheme.Modules.pullback h).mapIso e ≪≫ e', ?_⟩
  have assoc := congr_arg (fun φ => φ.app (E a)) (Scheme.Modules.pseudofunctor_associativity h g' π)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp, eqToHom_app] at assoc
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc, he']
  rw [← Functor.map_comp_assoc, he]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id,
    Functor.map_comp, Category.assoc]
  erw [← NatTrans.naturality_assoc]
  congr 1
  rw [← cancel_epi ((Scheme.Modules.pullbackComp h (g' ≫ π)).symm.app (E a) ≪≫
    (Scheme.Modules.pullback h).mapIso ((Scheme.Modules.pullbackComp g' π).symm.app (E a)) ≪≫
      (Scheme.Modules.pullbackComp h g').app _).hom]
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% assoc]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app, eqToIso.hom, eqToHom_app, eqToHom_trans, eqToHom_refl]
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]

end GlobalTheory.FlagConnect

end
