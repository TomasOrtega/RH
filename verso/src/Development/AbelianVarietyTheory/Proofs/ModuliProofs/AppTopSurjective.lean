import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.BaseChangeFns

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem surjective_appTop_of_iso {X Y : Scheme.{0}} (e : X ≅ Y) : Function.Surjective e.hom.appTop.hom := by
  first
  | exact (ConcreteCategory.bijective_of_isIso e.hom.appTop).2
  | exact (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).2
  | exact fun a => ⟨e.inv.appTop.hom a, by
      rw [← CommRingCat.comp_apply, ← Scheme.comp_appTop, e.inv_hom_id, Scheme.id_appTop]; rfl⟩

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
private theorem surjective_appTop_comp {X Y Z : Scheme.{0}} (p : X ⟶ Y) (q : Y ⟶ Z)
    (hp : Function.Surjective p.appTop.hom) (hq : Function.Surjective q.appTop.hom) :
    Function.Surjective (p ≫ q).appTop.hom := by
  first
  | exact hp.comp hq
  | (rw [Scheme.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]; exact hp.comp hq)
  | exact surj_comp hp hq

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
private theorem surjective_of_comp_surjective_of_injective {A B C : CommRingCat} (g : A ⟶ B) (m : B ⟶ C)
    (hm : Function.Injective m.hom) (h : Function.Surjective (g ≫ m).hom) : Function.Surjective g.hom := by
  intro y
  obtain ⟨x, hx⟩ := h (m.hom y)
  exact ⟨x, hm hx⟩

/- English proof (translation)
Substitute using the available equality. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
private theorem injective_presheaf_map_eqToHom {X : Scheme.{0}} {V W : X.Opens} (p : V = W) :
    Function.Injective (X.presheaf.map (eqToHom p).op).hom := by
  subst p
  first
  | (intro a b hab; simpa using hab)
  | (simp only [eqToHom_refl, op_id, Functor.map_id, CommRingCat.hom_id]; exact Function.injective_id)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion.

Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately.
-/
private theorem isAbelianScheme_pullback' {S₀ S : Scheme.{0}} {B : Over S₀} [GrpObj B] (t : S ⟶ S₀)
    (hB : IsAbelianScheme B) : IsAbelianScheme ((Over.pullback t).obj B) := by
  have h1 := hB.smooth
  have h2 := hB.proper
  have h3 := hB.geomConnected
  have h4 := hB.comm
  constructor
  case comm =>
    first
    | infer_instance
    | exact Functor.obj.instIsCommMonObj _
  case smooth =>
    show Smooth (pullback.snd B.hom t)
    first
    | infer_instance
    | exact MorphismProperty.pullback_snd _ _ h1
  case proper =>
    show IsProper (pullback.snd B.hom t)
    first
    | infer_instance
    | exact MorphismProperty.pullback_snd _ _ h2
  case geomConnected =>
    show GeometricallyConnected (pullback.snd B.hom t)
    first
    | infer_instance
    | exact MorphismProperty.pullback_snd _ _ h3

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem appTop_surjective (hG : Out.GlobalFnsSt) {S₀ : Scheme.{0}} {B : Over S₀} [GrpObj B]
    (hB : IsAbelianScheme B) {S X : Scheme.{0}} {t : S ⟶ S₀} {π : X ⟶ B.left} {f : X ⟶ S}
    (h : IsPullback π f B.hom t) : Function.Surjective f.appTop.hom := by
  have key : Function.Surjective (pullback.snd B.hom t).appTop.hom :=
    (hG S ((Over.pullback t).obj B) (isAbelianScheme_pullback' t hB)).2
  rw [← h.isoPullback_hom_snd]
  exact surjective_appTop_comp _ _ (surjective_appTop_of_iso _) key

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem app_surjective : Out.GlobalFnsSt → ∀ (S₀ : Scheme.{0}) (B : Over S₀) [GrpObj B], IsAbelianScheme B → ∀ (S X : Scheme.{0}) (t : S ⟶ S₀) (π : X ⟶ B.left) (f : X ⟶ S), IsPullback π f B.hom t → ∀ U : S.Opens, Function.Surjective (f.app U).hom := by
  intro hG S₀ B _ hB S X t π f h U
  have hP : IsPullback ((f ⁻¹ᵁ U).ι ≫ π) (f ∣_ U) B.hom (U.ι ≫ t) :=
    (isPullback_morphismRestrict f U).flip.paste_horiz h
  have hres := appTop_surjective hG hB hP
  rw [morphismRestrict_appTop] at hres
  have hV := surjective_of_comp_surjective_of_injective _ _ (injective_presheaf_map_eqToHom _) hres
  change Function.Surjective (f.app (U.ι ''ᵁ ⊤)).hom at hV
  rwa [Scheme.Opens.ι_image_top] at hV

end GlobalTheory.BaseChangeFns
