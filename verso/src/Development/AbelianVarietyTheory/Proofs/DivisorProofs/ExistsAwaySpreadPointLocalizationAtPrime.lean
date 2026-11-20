import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitIntCastStalkIff
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SpreadPoint

set_option backward.isDefEq.respectTransparency false

/- English proof (translation)
Set `x : PrimeSpectrum R` to `⟨𝔭, inferInstance⟩`. Set `T` to `(Spec.structureSheaf R).presheaf.stalk x`. Use `haveI : IsLocalization x.asIdeal.primeCompl T := StructureSheaf.IsLocalization.to_stalk R x`. Set `e : T ≃ₐ[R] Localization.AtPrime 𝔭` to `IsLocalization.algEquiv x.asIdeal.primeCompl T _`. Use `⟨x, asIso (Spec.map (e.toRingEquiv.toCommRingCatIso).hom), ?_, fun a ha => IsLocalization.map_units (Localization.AtPrime 𝔭) (⟨a, ha⟩ : 𝔭.primeCompl)⟩` and prove the remaining obligations.

Rewrite using `[Spec.fromSpecStalk_eq', asIso_hom, ← Spec.map_comp]`. Use `congr 1`. Use extensionality with `a`. Conclude with `e.commutes a`.
-/
theorem isStalkMap_atPrime (R : Type) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] :
    GlobalTheory.UPoinc.LocSpread.IsStalkMap (algebraMap R (Localization.AtPrime 𝔭)) := by
  let x : PrimeSpectrum R := ⟨𝔭, inferInstance⟩
  let T := (Spec.structureSheaf R).presheaf.stalk x
  haveI : IsLocalization x.asIdeal.primeCompl T := StructureSheaf.IsLocalization.to_stalk R x
  let e : T ≃ₐ[R] Localization.AtPrime 𝔭 := IsLocalization.algEquiv x.asIdeal.primeCompl T _
  refine ⟨x, asIso (Spec.map (e.toRingEquiv.toCommRingCatIso).hom), ?_, fun a ha =>
    IsLocalization.map_units (Localization.AtPrime 𝔭) (⟨a, ha⟩ : 𝔭.primeCompl)⟩
  rw [Spec.fromSpecStalk_eq', asIso_hom, ← Spec.map_comp]
  congr 1
  ext a
  exact e.commutes a

end GlobalTheory.SpreadPoint

/- English proof (translation)
Introduce `B _ X q _ R _ β 𝔭 _ f₀ hf₀`. Use `set σ := algebraMap R (Localization.AtPrime 𝔭)`. Establish `hσ` using `GlobalTheory.SpreadPoint.isStalkMap_atPrime R 𝔭`. Set `q' : pullback q (spMap β) ⟶ Sp R` to `pullback.snd q (spMap β)`. Establish `hP : IsPullback (spMap σ) (𝟙 _) (𝟙 (Sp R)) (spMap σ)` using `IsPullback.of_vert_isIso ⟨by simp⟩`.

Establish `hcomp : ∀ {A C D : Type} [CommRing A] [CommRing C] [CommRing D] (f : A →+* C) (g : C →+* D), spMap g ≫ spMap f = spMap (g.comp f)` using `fun f g => (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm`. Set `u₀ : Sp (Localization.AtPrime 𝔭) ⟶ pullback q (spMap β)` to `pullback.lift f₀ (spMap σ) (by rw [hf₀, hcomp])`. Take `⟨a, ha, H⟩` from `GlobalTheory.UPoinc.LocSpread.exists_hom hσ (𝟙 (Sp R)) q' hP u₀ (by rw [Category.comp_id]; exact pullback.lift_snd _ _ _)`. Establish `ha' : a ∉ 𝔭`. Introduce `h`.

Conclude with `(IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔭) 𝔭 a).1 ha h`. Set `g` to `algebraMap R (Localization.Away a)`. Take `⟨u, hu, hu₀⟩` from `H (Localization.Away a) g (IsLocalization.Away.algebraMap_isUnit a) (Sp (Localization.Away a)) (spMap g) (𝟙 _) (by simp)`. Set `j : Localization.Away a →+* Localization.AtPrime 𝔭` to `IsLocalization.Away.lift a ha`. Establish `hj : j.comp g = σ` using `IsLocalization.Away.lift_comp _ _`.

Use `⟨a, ha', j, u ≫ pullback.fst q (spMap β), hj, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc]`. Express the relevant statement in the definitionally equal form `(u ≫ q') ≫ _ = _`. Rewrite using `[hu, Category.comp_id, hcomp]`. Rewrite using `[← Category.assoc, hu₀ (spMap j) (by rw [hcomp, hj])]`.

Conclude with `pullback.lift_fst _ _ _`.
-/
theorem GlobalTheory.SpreadPoint.exists_away : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (q : X ⟶ Sp B) [LocallyOfFinitePresentation q] (R : Type) [CommRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (f₀ : Sp (Localization.AtPrime 𝔭) ⟶ X), f₀ ≫ q = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) → ∃ r ∉ 𝔭, ∃ (j : Localization.Away r →+* Localization.AtPrime 𝔭) (f : Sp (Localization.Away r) ⟶ X), j.comp (algebraMap R (Localization.Away r)) = algebraMap R (Localization.AtPrime 𝔭) ∧ f ≫ q = spMap ((algebraMap R (Localization.Away r)).comp β) ∧ spMap j ≫ f = f₀ := by
  intro B _ X q _ R _ β 𝔭 _ f₀ hf₀
  set σ := algebraMap R (Localization.AtPrime 𝔭)
  have hσ := GlobalTheory.SpreadPoint.isStalkMap_atPrime R 𝔭
  let q' : pullback q (spMap β) ⟶ Sp R := pullback.snd q (spMap β)
  have hP : IsPullback (spMap σ) (𝟙 _) (𝟙 (Sp R)) (spMap σ) :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have hcomp : ∀ {A C D : Type} [CommRing A] [CommRing C] [CommRing D] (f : A →+* C) (g : C →+* D),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g => (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm
  let u₀ : Sp (Localization.AtPrime 𝔭) ⟶ pullback q (spMap β) :=
    pullback.lift f₀ (spMap σ) (by rw [hf₀, hcomp])
  obtain ⟨a, ha, H⟩ := GlobalTheory.UPoinc.LocSpread.exists_hom hσ (𝟙 (Sp R)) q' hP u₀ (by rw [Category.comp_id]; exact pullback.lift_snd _ _ _)
  have ha' : a ∉ 𝔭 := by
    intro h
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔭) 𝔭 a).1 ha h
  let g := algebraMap R (Localization.Away a)
  obtain ⟨u, hu, hu₀⟩ := H (Localization.Away a) g (IsLocalization.Away.algebraMap_isUnit a) (Sp (Localization.Away a))
    (spMap g) (𝟙 _) (by simp)
  let j : Localization.Away a →+* Localization.AtPrime 𝔭 := IsLocalization.Away.lift a ha
  have hj : j.comp g = σ := IsLocalization.Away.lift_comp _ _
  refine ⟨a, ha', j, u ≫ pullback.fst q (spMap β), hj, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (u ≫ q') ≫ _ = _
    rw [hu, Category.comp_id, hcomp]
  · rw [← Category.assoc, hu₀ (spMap j) (by rw [hcomp, hj])]
    exact pullback.lift_fst _ _ _
