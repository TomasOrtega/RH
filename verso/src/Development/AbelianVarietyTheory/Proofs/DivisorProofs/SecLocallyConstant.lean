import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsModuleCatIffForgetIffElStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleModuleSheafSectionsCoprodBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecPiCofanIsColimitOfRingEquiv
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.LCSec

variable (X : Type) [TopologicalSpace X] (B : Type) [CommRing B]

def preQ {S T : DiscreteQuotient X} (h : T ≤ S) : (S → B) →+* (T → B) where
  toFun g t := g (DiscreteQuotient.ofLE h t)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem preQ_apply {S T : DiscreteQuotient X} (h : T ≤ S) (g : S → B) (t : T) :
    preQ X B h g t = g (DiscreteQuotient.ofLE h t) := rfl

def stage : (DiscreteQuotient X)ᵒᵖ ⥤ CommRingCat.{0} where
  obj S := CommRingCat.of (S.unop → B)
  map f := CommRingCat.ofHom (preQ X B (leOfHom f.unop))
  map_id S := by
    refine CommRingCat.hom_ext (RingHom.ext fun g => funext fun t => ?_)
    exact congrArg g (DiscreteQuotient.ofLE_refl_apply t)
  map_comp f g := by
    refine CommRingCat.hom_ext (RingHom.ext fun h => funext fun t => ?_)
    exact congrArg h (DiscreteQuotient.ofLE_ofLE _ _ t).symm

def pullQ (S : DiscreteQuotient X) : (S → B) →+* LocallyConstant X B where
  toFun g := ⟨fun x => g (S.proj x), S.proj_isLocallyConstant.comp g⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem pullQ_apply (S : DiscreteQuotient X) (g : S → B) (x : X) : pullQ X B S g x = g (S.proj x) := rfl

def lcCocone : Cocone (stage X B) where
  pt := CommRingCat.of (LocallyConstant X B)
  ι := { app := fun S => CommRingCat.ofHom (pullQ X B S.unop)
         naturality := fun S T f => by
           refine CommRingCat.hom_ext (RingHom.ext fun g => LocallyConstant.ext fun x => ?_)
           exact congrArg g (DiscreteQuotient.ofLE_proj _ x) }

def lcCoconeIsColimit : IsColimit (lcCocone X B) := by
  haveI : ReflectsColimitsOfShape (DiscreteQuotient X)ᵒᵖ (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (forget CommRingCat.{0})
  apply Types.FilteredColimit.isColimitOf
  · intro f
    refine ⟨op f.discreteQuotient, ⇑f.lift, ?_⟩
    exact LocallyConstant.ext fun x => rfl
  · intro S T g h e
    change pullQ X B S.unop g = pullQ X B T.unop h at e
    refine ⟨op (S.unop ⊓ T.unop), (homOfLE inf_le_left).op, (homOfLE inf_le_right).op, ?_⟩
    change preQ X B _ g = preQ X B _ h
    funext q
    obtain ⟨x, rfl⟩ := DiscreteQuotient.proj_surjective _ q
    have hx := congrArg (fun φ : LocallyConstant X B => φ x) e
    change g (S.unop.proj x) = h (T.unop.proj x) at hx
    exact (congrArg g (DiscreteQuotient.ofLE_proj _ x)).trans (hx.trans (congrArg h (DiscreteQuotient.ofLE_proj _ x).symm))

end GlobalTheory.EtC.LCSec

namespace GlobalTheory.EtC.LCSec

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem res_res {R : Type} [CommRing R] {F : Shv R} {U V W : Scheme.{0}} (a : W ⟶ V) (b : V ⟶ U) (y : Sec F U) :
    Sec.res a (Sec.res b y) = Sec.res (a ≫ b) y := by
  simp [Sec.res]

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem sec_pi_bijective (R : Type) [CommRing R] (F : Shv R) (B : Type) [CommRing B] (S : Type) [Finite S] :
    Function.Bijective (fun (y : Sec F (Spec (CommRingCat.of (S → B)))) (s : S) =>
      Sec.res (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : S => B) s))) y) := by
  obtain ⟨hc⟩ := GlobalTheory.EtC.spec_pi_cofan_isColimit S (fun _ => B) (S → B) (RingEquiv.refl _)
  exact GlobalTheory.T.etaleModuleSheaf_sections_coprod_bijective R F _ S _ _ hc

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem res_eval_pullQ (R : Type) [CommRing R] (F : Shv R) (X : Type) [TopologicalSpace X] (B : Type) [CommRing B]
    (S : DiscreteQuotient X) (y : Sec F (Spec (CommRingCat.of (S → B)))) (x : X) :
    Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x)))
        (Sec.res (Spec.map (CommRingCat.ofHom (pullQ X B S))) y) =
      Sec.res (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : S => B) (S.proj x)))) y := by
  rw [res_res, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end GlobalTheory.EtC.LCSec

open GlobalTheory.EtC.LCSec in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem GlobalTheory.EtC.sec_locallyConstant : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] (B : Type) [CommRing B], (∀ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), IsLocallyConstant (fun x : X => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t)) ∧ Function.Injective (fun (t : Sec F (Spec (CommRingCat.of (LocallyConstant X B)))) (x : X) => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t) ∧ ∀ ψ : X → Sec F (Spec (CommRingCat.of B)), IsLocallyConstant ψ → ∃ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), ∀ x, Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t = ψ x := by
  intro R _ F hF X _ _ B _
  have hfin := ((GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements (ULift.{1} R) (onRings F)).2.mp hF) _ (stage X B) (lcCocone X B) (lcCoconeIsColimit X B)
  have hrep : ∀ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), ∃ (S : DiscreteQuotient X)
      (y : Sec F (Spec (CommRingCat.of (S → B)))), Sec.res (Spec.map (CommRingCat.ofHom (pullQ X B S))) y = t := by
    intro t
    obtain ⟨S, y, hy⟩ := hfin.1 t
    exact ⟨S.unop, y, hy⟩
  have hzero : ∀ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))),
      (∀ x, Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t = 0) → t = 0 := by
    intro t ht
    obtain ⟨S, y, rfl⟩ := hrep t
    have hall : ∀ s : S, Sec.res (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : S => B) s))) y = 0 := by
      intro s
      obtain ⟨x, rfl⟩ := DiscreteQuotient.proj_surjective _ s
      rw [← res_eval_pullQ]
      exact ht x
    have hy : y = 0 := by
      apply (sec_pi_bijective R F B S).1
      funext s
      exact (hall s).trans (map_zero _).symm
    rw [hy]
    exact map_zero _
  refine ⟨fun t => ?_, fun t₁ t₂ h => ?_, fun ψ hψ => ?_⟩
  · obtain ⟨S, y, rfl⟩ := hrep t
    have he : (fun x : X => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x)))
        (Sec.res (Spec.map (CommRingCat.ofHom (pullQ X B S))) y)) =
        (fun s : S => Sec.res (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : S => B) s))) y) ∘ S.proj :=
      funext fun x => res_eval_pullQ R F X B S y x
    rw [he]
    exact S.proj_isLocallyConstant.comp _
  · have h0 := hzero (t₁ - t₂) fun x => by
      change (F.obj.map _).hom (t₁ - t₂) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (congrFun h x)
    exact sub_eq_zero.mp h0
  · let f : LocallyConstant X (Sec F (Spec (CommRingCat.of B))) := ⟨ψ, hψ⟩
    obtain ⟨y, hy⟩ := (sec_pi_bijective R F B f.discreteQuotient).2 (⇑f.lift)
    refine ⟨Sec.res (Spec.map (CommRingCat.ofHom (pullQ X B f.discreteQuotient))) y, fun x => ?_⟩
    rw [res_eval_pullQ]
    exact congrFun hy (f.discreteQuotient.proj x)
