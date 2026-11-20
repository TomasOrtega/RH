import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

section Objects

variable {X : Scheme.{u}}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨fun _ => inferInstance, h⟩, fun h => h.isIntegrallyClosed_stalk⟩`.
-/
theorem isNormalScheme_iff_model (X : Scheme.{u}) [IsIntegral X] :
    GroundTheory.Heights₂.Heights.Model.IsNormalScheme X ↔ GroundTheory.Arith.SchemeCoh.IsNormalScheme X :=
  ⟨fun h => ⟨fun _ => inferInstance, h⟩, fun h => h.isIntegrallyClosed_stalk⟩

variable [IrreducibleSpace X]

/- English proof (translation)
Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, rfl⟩`. Take `⟨U, hxU, s, rfl⟩` from `E.presheaf.exists_germ_eq w`. Conclude with `⟨U, hxU, (genericPoint_specializes x).mem_open U.isOpen hxU, s, (E.presheaf.germ_stalkSpecializes_apply hxU (genericPoint_specializes x) s).symm⟩`.

Introduce and unpack `⟨U, hxU, hU, s, rfl⟩`. Conclude with `⟨E.presheaf.germ U x hxU s, E.presheaf.germ_stalkSpecializes_apply hxU _ s⟩`.
-/
theorem genericImage_eq_germImage (E : X.Modules) (x : X) :
    (GroundTheory.Heights₂.Heights.Model.genericImage E x : Set (E.presheaf.stalk (genericPoint X))) =
      germImage E x := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨U, hxU, s, rfl⟩ := E.presheaf.exists_germ_eq w
    exact ⟨U, hxU, (genericPoint_specializes x).mem_open U.isOpen hxU, s,
      (E.presheaf.germ_stalkSpecializes_apply hxU (genericPoint_specializes x) s).symm⟩
  · rintro ⟨U, hxU, hU, s, rfl⟩
    exact ⟨E.presheaf.germ U x hxU s, E.presheaf.germ_stalkSpecializes_apply hxU _ s⟩

/- English proof (translation)
The claim follows from `PresheafOfModules.germ_smul (M := E.val) _ U hU r s`.
-/
theorem germ_smul_generic (E : X.Modules) {U : X.Opens} (hU : genericPoint X ∈ U) (r : Γ(X, U))
    (s : Γ(E, U)) :
    E.presheaf.germ U _ hU (r • s) = X.presheaf.germ U _ hU r • E.presheaf.germ U _ hU s :=
  PresheafOfModules.germ_smul (M := E.val) _ U hU r s

/- English proof (translation)
Take `⟨U, hU, r, rfl⟩` from `X.presheaf.exists_germ_eq c`. Take `⟨V, hV, s, rfl⟩` from `E.presheaf.exists_germ_eq v`. Take `⟨W, hW, t, ht⟩` from `E'.presheaf.exists_germ_eq (φ.toAddEquiv (E.presheaf.germ V _ hV s))`. Establish `hO : genericPoint X ∈ U ⊓ V ⊓ W` using `⟨⟨hU, hV⟩, hW⟩`. Establish `iU : U ⊓ V ⊓ W ≤ U` using `inf_le_left.trans inf_le_left`.

Establish `iV : U ⊓ V ⊓ W ≤ V` using `inf_le_left.trans inf_le_right`. Establish `iW : U ⊓ V ⊓ W ≤ W` using `inf_le_right`. Rewrite `*` using `[← X.presheaf.germ_res_apply (homOfLE iU) _ hO r, ← E.presheaf.germ_res_apply (homOfLE iV) _ hO s]`. Rewrite `ht` using `[← E'.presheaf.germ_res_apply (homOfLE iW) _ hO t]`. Rewrite using `[← germ_smul_generic, φ.map_smul_germ _ hO _ _ _ ht.symm, germ_smul_generic, ht]`.
-/
theorem GenericStalkIso.map_smul_stalk {E E' : X.Modules} (φ : GenericStalkIso E E')
    (c : X.presheaf.stalk (genericPoint X)) (v : E.presheaf.stalk (genericPoint X)) :
    φ.toAddEquiv (c • v) = c • φ.toAddEquiv v := by
  obtain ⟨U, hU, r, rfl⟩ := X.presheaf.exists_germ_eq c
  obtain ⟨V, hV, s, rfl⟩ := E.presheaf.exists_germ_eq v
  obtain ⟨W, hW, t, ht⟩ := E'.presheaf.exists_germ_eq (φ.toAddEquiv (E.presheaf.germ V _ hV s))
  have hO : genericPoint X ∈ U ⊓ V ⊓ W := ⟨⟨hU, hV⟩, hW⟩
  have iU : U ⊓ V ⊓ W ≤ U := inf_le_left.trans inf_le_left
  have iV : U ⊓ V ⊓ W ≤ V := inf_le_left.trans inf_le_right
  have iW : U ⊓ V ⊓ W ≤ W := inf_le_right
  rw [← X.presheaf.germ_res_apply (homOfLE iU) _ hO r,
    ← E.presheaf.germ_res_apply (homOfLE iV) _ hO s] at *
  rw [← E'.presheaf.germ_res_apply (homOfLE iW) _ hO t] at ht
  rw [← germ_smul_generic, φ.map_smul_germ _ hO _ _ _ ht.symm, germ_smul_generic, ht]

variable {E E' : X.Modules}

def GenericStalkIso.toLinearEquiv (φ : GenericStalkIso E E') :
    E.presheaf.stalk (genericPoint X) ≃ₗ[X.presheaf.stalk (genericPoint X)]
      E'.presheaf.stalk (genericPoint X) :=
  { φ.toAddEquiv with map_smul' := φ.map_smul_stalk }

def GenericStalkIso.ofLinearEquiv
    (φ : E.presheaf.stalk (genericPoint X) ≃ₗ[X.presheaf.stalk (genericPoint X)]
      E'.presheaf.stalk (genericPoint X)) : GenericStalkIso E E' where
  toAddEquiv := φ.toAddEquiv
  map_smul_germ U hU r s t h := by
    simp only [LinearEquiv.coe_toAddEquiv] at h ⊢
    rw [germ_smul_generic, germ_smul_generic, ← h]
    exact φ.map_smul _ _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h U hU s`. Conclude with `(h _).symm.trans (TopCat.Presheaf.stalkFunctor_map_germ_apply U _ hU _ s)`. Introduce `h v`. Take `⟨U, hU, s, rfl⟩` from `E.presheaf.exists_germ_eq v`.

Conclude with `(TopCat.Presheaf.stalkFunctor_map_germ_apply U _ hU _ s).trans (h U hU s).symm`.
-/
theorem stalkMap_eq_iff_germ (ψ : E ≅ E')
    (f : E.presheaf.stalk (genericPoint X) → E'.presheaf.stalk (genericPoint X)) :
    (∀ v, ((TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map
      (Scheme.Modules.Hom.mapPresheaf ψ.hom)).hom v = f v) ↔
    ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)),
      f (E.presheaf.germ U _ hU s) = E'.presheaf.germ U _ hU (Scheme.Modules.Hom.app ψ.hom U s) := by
  constructor
  · intro h U hU s
    exact (h _).symm.trans (TopCat.Presheaf.stalkFunctor_map_germ_apply U _ hU _ s)
  · intro h v
    obtain ⟨U, hU, s, rfl⟩ := E.presheaf.exists_germ_eq v
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U _ hU _ s).trans (h U hU s).symm

end Objects

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h X _ hN _ E E' hE hE' φ hφ`. Take `⟨ψ, hψ, huniq⟩` from `h X ((isNormalScheme_iff_model X).2 hN) E E' hE hE' φ.toLinearEquiv (fun x hx => SetLike.coe_injective (by`. Rewrite using `[AddSubgroup.coe_map, genericImage_eq_germImage, genericImage_eq_germImage]`. Conclude with `hφ x hx))`.

Conclude with `⟨ψ, (stalkMap_eq_iff_germ ψ _).1 hψ, fun ψ' h' => huniq ψ' ((stalkMap_eq_iff_germ ψ' _).2 h')⟩`. Introduce `h X _ _ hN E E' hE hE' φ hφ`. Use `(isNormalScheme_iff_model X).1 hN` as an intermediate fact. Take `⟨ψ, hψ, huniq⟩` from `h X E E' hE hE' (GenericStalkIso.ofLinearEquiv φ) (fun x hx => by`. Use `congrArg SetLike.coe (hφ x hx)` as an intermediate fact.

Simplify using `only [AddSubgroup.coe_map, genericImage_eq_germImage] at this`. Conclude with `this)`. Conclude with `⟨ψ, (stalkMap_eq_iff_germ ψ _).2 hψ, fun ψ' h' => huniq ψ' ((stalkMap_eq_iff_germ ψ' _).1 h')⟩`.
-/
theorem BundlesAgree.equiv :
    GroundTheory.Heights₂.Heights.Model.BundlesAgree.Statement ↔ BundlesAgree.Statement := by
  constructor
  · intro h X _ hN _ E E' hE hE' φ hφ
    obtain ⟨ψ, hψ, huniq⟩ := h X ((isNormalScheme_iff_model X).2 hN) E E' hE hE' φ.toLinearEquiv
      (fun x hx => SetLike.coe_injective (by
        rw [AddSubgroup.coe_map, genericImage_eq_germImage, genericImage_eq_germImage]
        exact hφ x hx))
    exact ⟨ψ, (stalkMap_eq_iff_germ ψ _).1 hψ,
      fun ψ' h' => huniq ψ' ((stalkMap_eq_iff_germ ψ' _).2 h')⟩
  · intro h X _ _ hN E E' hE hE' φ hφ
    have := (isNormalScheme_iff_model X).1 hN
    obtain ⟨ψ, hψ, huniq⟩ := h X E E' hE hE' (GenericStalkIso.ofLinearEquiv φ)
      (fun x hx => by
        have := congrArg SetLike.coe (hφ x hx)
        simp only [AddSubgroup.coe_map, genericImage_eq_germImage] at this
        exact this)
    exact ⟨ψ, (stalkMap_eq_iff_germ ψ _).2 hψ,
      fun ψ' h' => huniq ψ' ((stalkMap_eq_iff_germ ψ' _).1 h')⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
