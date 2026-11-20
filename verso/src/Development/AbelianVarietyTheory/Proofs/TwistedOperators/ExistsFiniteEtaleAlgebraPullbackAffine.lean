import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.HeckeEx

/- English proof (translation)
Introduce `X Y π hfin het R _ x`. Use `haveI : IsAffine (pullback π x) := isAffine_of_isAffineHom (pullback.snd π x)`. Take `⟨S, e, -⟩ : ∃ (S : CommRingCat.{0}) (_ : Spec S ≅ pullback π x), True` from `⟨_, (pullback π x).isoSpec.symm, trivial⟩`. Take `⟨f, hf⟩` from `Spec.map_surjective (R := CommRingCat.of R) (S := S) (e.hom ≫ pullback.snd π x)`. Use `letI : Algebra R S := f.hom.toAlgebra`.

Establish `hsp : spMap (algebraMap R S) = e.hom ≫ pullback.snd π x` using `hf`. Use `⟨S, inferInstance, inferInstance, e.hom ≫ pullback.fst π x, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : IsFinite (Spec.map f)` using `by rw [hf]; infer_instance`. Conclude with `(IsFinite.SpecMap_iff f).1 h1`. Establish `h1 : Etale (Spec.map f)` using `by rw [hf]; infer_instance`.

Conclude with `RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1 h1)`. Rewrite using `[hsp, Category.assoc, Category.assoc, pullback.condition]`. Introduce `hs`. Establish `h1 : Surjective (Spec.map f)` using `by rw [hf]; infer_instance`. Conclude with `h1.surj`.

Introduce `Ω _ φ w hw`. Take `⟨g, hg⟩` from `Spec.map_surjective (R := S) (S := CommRingCat.of Ω) (pullback.lift w (spMap φ) hw ≫ e.inv)`. Establish `key : ∀ χ : S →+* Ω, χ.comp (algebraMap R S) = φ ↔ spMap χ ≫ e.hom ≫ pullback.snd π x = spMap φ`. Introduce `χ`. Rewrite using `[← hsp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h]`. Introduce `h`. Conclude with `congrArg CommRingCat.Hom.hom (Spec.map_injective h)`.

Establish `hg' : spMap g.hom = pullback.lift w (spMap φ) hw ≫ e.inv` using `hg`. Use `⟨g.hom, ⟨(key _).2 ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hg', Category.assoc, e.inv_hom_id_assoc, pullback.lift_snd]`. Rewrite using `[hg', Category.assoc, e.inv_hom_id_assoc, pullback.lift_fst]`. Introduce and unpack `χ ⟨h1, h2⟩`.

Establish `h3 : spMap χ = spMap g.hom`. Rewrite using `[hg', Iso.eq_comp_inv]`. Use `pullback.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[pullback.lift_fst, Category.assoc]`. Conclude with `h2`.

Rewrite using `[pullback.lift_snd, Category.assoc]`. Conclude with `(key _).1 h1`. Conclude with `congrArg CommRingCat.Hom.hom (Spec.map_injective h3)`.
-/
theorem exists_finiteEtale_algebra_pullback : ∀ (X Y : Scheme.{0}) (π : Y ⟶ X), IsFinite π → Etale π → ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (h : Sp B ⟶ Y), Module.Finite R B ∧ Algebra.Etale R B ∧ h ≫ π = spMap (algebraMap R B) ≫ x ∧ (Surjective π → Function.Surjective (PrimeSpectrum.comap (algebraMap R B))) ∧ ∀ (Ω : Type) [CommRing Ω] (φ : R →+* Ω) (w : Sp Ω ⟶ Y), w ≫ π = spMap φ ≫ x → ∃! χ : B →+* Ω, χ.comp (algebraMap R B) = φ ∧ spMap χ ≫ h = w := by
  intro X Y π hfin het R _ x
  haveI : IsAffine (pullback π x) := isAffine_of_isAffineHom (pullback.snd π x)
  obtain ⟨S, e, -⟩ : ∃ (S : CommRingCat.{0}) (_ : Spec S ≅ pullback π x), True :=
    ⟨_, (pullback π x).isoSpec.symm, trivial⟩
  obtain ⟨f, hf⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := S)
    (e.hom ≫ pullback.snd π x)
  letI : Algebra R S := f.hom.toAlgebra
  have hsp : spMap (algebraMap R S) = e.hom ≫ pullback.snd π x := hf
  refine ⟨S, inferInstance, inferInstance, e.hom ≫ pullback.fst π x, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : IsFinite (Spec.map f) := by rw [hf]; infer_instance
    exact (IsFinite.SpecMap_iff f).1 h1
  · have h1 : Etale (Spec.map f) := by rw [hf]; infer_instance
    exact RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1 h1)
  · rw [hsp, Category.assoc, Category.assoc, pullback.condition]
  · intro hs
    have h1 : Surjective (Spec.map f) := by rw [hf]; infer_instance
    exact h1.surj
  · intro Ω _ φ w hw
    obtain ⟨g, hg⟩ := Spec.map_surjective (R := S) (S := CommRingCat.of Ω)
      (pullback.lift w (spMap φ) hw ≫ e.inv)
    have key : ∀ χ : S →+* Ω, χ.comp (algebraMap R S) = φ ↔
        spMap χ ≫ e.hom ≫ pullback.snd π x = spMap φ := by
      intro χ
      rw [← hsp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      constructor
      · intro h; rw [h]
      · intro h
        exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
    have hg' : spMap g.hom = pullback.lift w (spMap φ) hw ≫ e.inv := hg
    refine ⟨g.hom, ⟨(key _).2 ?_, ?_⟩, ?_⟩
    · rw [hg', Category.assoc, e.inv_hom_id_assoc, pullback.lift_snd]
    · rw [hg', Category.assoc, e.inv_hom_id_assoc, pullback.lift_fst]
    · rintro χ ⟨h1, h2⟩
      have h3 : spMap χ = spMap g.hom := by
        rw [hg', Iso.eq_comp_inv]
        refine pullback.hom_ext ?_ ?_
        · rw [pullback.lift_fst, Category.assoc]; exact h2
        · rw [pullback.lift_snd, Category.assoc]; exact (key _).1 h1
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h3)

end GlobalTheory.HeckeEx
