import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory

namespace GlobalTheory.StalkLength

/- English proof (translation)
Set `G` to `(Scheme.Modules.pushforward i).obj F`. Set `φ` to `i.stalkMap y`. Use `letI : Algebra (X.presheaf.stalk (i y)) (Y.presheaf.stalk y) := φ.hom.toAlgebra`. Use `letI : Module (X.presheaf.stalk (i y)) (F.presheaf.stalk y :) := Module.compHom _ (algebraMap (X.presheaf.stalk (i y)) (Y.presheaf.stalk y))`. Use `haveI : IsScalarTower (X.presheaf.stalk (i y)) (Y.presheaf.stalk y) (F.presheaf.stalk y :) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl`.

Set `Ψ : (G.presheaf.stalk (i y) :) →+ (F.presheaf.stalk y :)` to `(F.presheaf.stalkPushforward _ i.base y).hom`. Establish `hΨ (U : X.Opens) (hU : i y ∈ U) (s : Γ(G, U)) : Ψ (G.presheaf.germ U _ hU s) = F.presheaf.germ (i ⁻¹ᵁ U) y hU s` using `congr($(TopCat.Presheaf.stalkPushforward_germ _ i.base F.presheaf U y hU).hom s)`. Establish `hiso` using `TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing _ (f := i.base) i.isClosedEmbedding.isInducing F.presheaf y`. Establish `hbij : Function.Bijective Ψ` using `ConcreteCategory.bijective_of_isIso (F.presheaf.stalkPushforward _ i.base y)`. Establish `hsmul (a : X.presheaf.stalk (i y)) (m : (G.presheaf.stalk (i y) :)) : Ψ (a • m) = φ.hom a • Ψ m`.

Take `⟨U₁, hU₁, r, rfl⟩` from `X.presheaf.germ_exist a`. Take `⟨U₂, hU₂, s, rfl⟩` from `G.presheaf.germ_exist m`. Establish `hU : i y ∈ U₁ ⊓ U₂` using `⟨hU₁, hU₂⟩`. Rewrite using `[← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) _ hU, ← TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) _ hU]`. Generalize the expression as in `X.presheaf.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op r = r'`.

Generalize the expression as in `G.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op s = s'`. Rewrite using `[← GlobalTheory.QCoh.germ_smul G, hΨ, hΨ]`. Use `(GlobalTheory.QCoh.germ_smul F (U := i ⁻¹ᵁ (U₁ ⊓ U₂)) _ _ (i.app _ r') s').trans ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `congr($(Scheme.Hom.germ_stalkMap i (U₁ ⊓ U₂) y hU).hom r').symm`.

Set `e : (G.presheaf.stalk (i y) :) ≃ₗ[X.presheaf.stalk (i y)] (F.presheaf.stalk y :)` to `{ AddEquiv.ofBijective Ψ hbij with map_smul' := hsmul }`. Conclude with `e.length_eq.trans (Module.length_eq_of_surjective (i.stalkMap_surjective y))`.
-/
theorem length_stalk_pushforward {X Y : Scheme.{0}} (i : Y ⟶ X) [IsClosedImmersion i]
    (F : Y.Modules) (y : Y) :
    Module.length (X.presheaf.stalk (i y))
        (((Scheme.Modules.pushforward i).obj F).presheaf.stalk (i y) :) =
      Module.length (Y.presheaf.stalk y) (F.presheaf.stalk y :) := by
  let G := (Scheme.Modules.pushforward i).obj F
  let φ := i.stalkMap y
  letI : Algebra (X.presheaf.stalk (i y)) (Y.presheaf.stalk y) := φ.hom.toAlgebra
  letI : Module (X.presheaf.stalk (i y)) (F.presheaf.stalk y :) :=
    Module.compHom _ (algebraMap (X.presheaf.stalk (i y)) (Y.presheaf.stalk y))
  haveI : IsScalarTower (X.presheaf.stalk (i y)) (Y.presheaf.stalk y) (F.presheaf.stalk y :) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let Ψ : (G.presheaf.stalk (i y) :) →+ (F.presheaf.stalk y :) :=
    (F.presheaf.stalkPushforward _ i.base y).hom
  have hΨ (U : X.Opens) (hU : i y ∈ U) (s : Γ(G, U)) :
      Ψ (G.presheaf.germ U _ hU s) = F.presheaf.germ (i ⁻¹ᵁ U) y hU s :=
    congr($(TopCat.Presheaf.stalkPushforward_germ _ i.base F.presheaf U y hU).hom s)
  have hiso := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing _
    (f := i.base) i.isClosedEmbedding.isInducing F.presheaf y
  have hbij : Function.Bijective Ψ :=
    ConcreteCategory.bijective_of_isIso (F.presheaf.stalkPushforward _ i.base y)
  have hsmul (a : X.presheaf.stalk (i y)) (m : (G.presheaf.stalk (i y) :)) :
      Ψ (a • m) = φ.hom a • Ψ m := by
    obtain ⟨U₁, hU₁, r, rfl⟩ := X.presheaf.germ_exist a
    obtain ⟨U₂, hU₂, s, rfl⟩ := G.presheaf.germ_exist m
    have hU : i y ∈ U₁ ⊓ U₂ := ⟨hU₁, hU₂⟩
    rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) _ hU,
      ← TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) _ hU]
    generalize X.presheaf.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op r = r'
    generalize G.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op s = s'
    rw [← GlobalTheory.QCoh.germ_smul G, hΨ, hΨ]
    refine (GlobalTheory.QCoh.germ_smul F (U := i ⁻¹ᵁ (U₁ ⊓ U₂)) _ _ (i.app _ r') s').trans ?_
    congr 1
    exact congr($(Scheme.Hom.germ_stalkMap i (U₁ ⊓ U₂) y hU).hom r').symm
  let e : (G.presheaf.stalk (i y) :) ≃ₗ[X.presheaf.stalk (i y)] (F.presheaf.stalk y :) :=
    { AddEquiv.ofBijective Ψ hbij with map_smul' := hsmul }
  exact e.length_eq.trans (Module.length_eq_of_surjective (i.stalkMap_surjective y))

/- English proof (translation)
Introduce `X Z _ G _`. Rewrite using `[length_stalk_pushforward]`. Conclude with `Module.length_eq_finrank (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.functionField (GlobalTheory.VB.genStalk G)`.
-/
theorem length_stalk_pushforward_genericPoint : ∀ (X : Scheme.{0}) (Z : Closeds X)
    [IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme]
    (G : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Modules) [GlobalTheory.QCoh.IsFiniteQC G],
    Module.length (X.presheaf.stalk (redι Z (genericPoint _)))
      (((Scheme.Modules.pushforward (redι Z)).obj G).presheaf.stalk (redι Z (genericPoint _)) :) =
      (GlobalTheory.VB.genRank G : ℕ∞) := by
  intro X Z _ G _
  rw [length_stalk_pushforward]
  exact Module.length_eq_finrank (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.functionField
    (GlobalTheory.VB.genStalk G)

end GlobalTheory.StalkLength
