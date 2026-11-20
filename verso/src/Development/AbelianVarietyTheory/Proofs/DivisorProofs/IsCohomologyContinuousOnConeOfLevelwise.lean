import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContCxOfDegreewise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyPresheafClassesAsCocyclesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafBasicPropertiStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ContLevel

/- English proof (translation)
The claim follows from `HomologicalComplex.extendMap_f ((chainsN R).map φ) ComplexShape.embeddingDownNat (i := k) rfl`.
-/
theorem chains_map_f (R : Type) [CommRing R] {E E' : Spc} (φ : E ⟶ E') (k : ℕ) :
    ((chains R).map φ).f (-(k : ℤ)) = (chainsXIso R E k).hom ≫ (free R).map (φ.app (op (SimplexCategory.mk k))) ≫ (chainsXIso R E' k).inv :=
  HomologicalComplex.extendMap_f ((chainsN R).map φ) ComplexShape.embeddingDownNat (i := k) rfl

end GlobalTheory.EtC.ContLevel

open GlobalTheory.EtC.ContLevel in

/- English proof (translation)
Introduce `R _ F I _ _ G c hG`. Take `⟨-, hneg, -, -, -, hpos⟩` from `GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F`. Take `⟨cl, hsurj, hiff, hzero, hpull⟩` from `GlobalTheory.T.etaleSpaceCohomology_presheaf_classes_as_cocycles R F`. Use `fun n => GlobalTheory.EtC.cont_cx_of_degreewise R I (G ⋙ chains R) ((chains R).mapCone c) (res R F) (fun i p hp => hpos (G.obj i) p hp) (fun p hp => hpos c.pt p hp) hneg ?_ n` and prove the remaining obligations. Introduce `p s`.

Distinguish the cases in `hp : 0 < p`. Prove the components needed by the constructor for the conclusion. Introduce `t _`. Take `⟨i⟩` from `IsCofiltered.nonempty (C := I)`. Use `⟨i, 0, 0, zero_comp, ?_⟩` and prove the remaining obligations.

Establish `: t = 0` using `(hpos c.pt p hp).eq_of_src _ _`. Simplify using `[this]`. Introduce `i u _ _`. Use `⟨i, 𝟙 i, 0, ?_⟩` and prove the remaining obligations. Establish `: u = 0` using `(hpos (G.obj i) p hp).eq_of_src _ _`.

Simplify using `[this]`. Take `⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ)` from `⟨(-p).toNat, by omega⟩`. Establish `hk` using `hG (op (SimplexCategory.mk k)) s`. Prove the components needed by the constructor for the conclusion. Introduce `t ht`.

Set `t'` to `(chainsXIso R c.pt k).inv ≫ t`. Establish `ht' : t' ≫ (res R F).d s (s + 1) = 0` using `by simp [t', ht]`. Take `⟨i, y, hy⟩` from `hk.1 (cl _ s t' ht')`. Take `⟨u', hu', rfl⟩` from `hsurj _ s y`. Take `⟨h2, hp2⟩` from `hpull (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj c.pt) (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj i)) ((c.π.app i).app (op (SimplexCategory.mk k))) s u' hu'`.

Express the relevant statement in the definitionally equal form `pull R (disc.map ((c.π.app i).app (op (SimplexCategory.mk k)))) F s _ = _ at hy`. Rewrite `hy` using `[hp2, hiff]`. Take `⟨y', hy'⟩` from `hy`. Use `⟨i, (chainsXIso R (G.obj i) k).hom ≫ u', (chainsXIso R c.pt k).hom ≫ y', by simp [hu'], ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((chains R).map (c.π.app i)).f _ ≫ _ = _`.

Rewrite using `[chains_map_f]`. Simplify using `only [Category.assoc, Iso.inv_hom_id_assoc]`. Rewrite using `[hy']`. Simplify using `[t', Preadditive.comp_add]`. Introduce and unpack `i u hu ⟨y, hy⟩`.

Set `u'` to `(chainsXIso R (G.obj i) k).inv ≫ u`. Establish `hu' : u' ≫ (res R F).d s (s + 1) = 0` using `by simp [u', hu]`. Establish `hdie : pull R ((((evaluation _ PSh).obj (op (SimplexCategory.mk k)) ⋙ disc).mapCone c).π.app i) F s (cl _ s u' hu') = 0`. Express the relevant statement in the definitionally equal form `pull R (disc.map ((c.π.app i).app _)) F s _ = 0`. Take `⟨h2, hp2⟩` from `hpull (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj c.pt) (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj i)) ((c.π.app i).app (op (SimplexCategory.mk k))) s u' hu'`.

Rewrite using `[hp2, ← hzero (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj c.pt) s, hiff]`. Use `⟨(chainsXIso R c.pt k).inv ≫ y, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((chains R).map (c.π.app i)).f _ ≫ u = _ at hy`. Rewrite `hy` using `[chains_map_f]`. Rewrite using `[zero_add, Category.assoc, ← hy]`.

Simplify using `[u']`. Take `⟨k', f, hf⟩` from `hk.2 i _ hdie`. Express the relevant statement in the definitionally equal form `pull R (disc.map ((G.map f).app (op (SimplexCategory.mk k)))) F s _ = 0 at hf`. Take `⟨h3, hp3⟩` from `hpull (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj k')) (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj i)) ((G.map f).app (op (SimplexCategory.mk k))) s u' hu'`. Rewrite `hf` using `[hp3, ← hzero (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj k')) s, hiff]`.

Take `⟨y'', hy''⟩` from `hf`. Use `⟨k', f, (chainsXIso R (G.obj k') k).hom ≫ y'', ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((chains R).map (G.map f)).f _ ≫ u = _`. Rewrite `*` using `[chains_map_f, zero_add]`. Simplify using `only [Category.assoc]`.

Conclude with `congrArg ((chainsXIso R (G.obj k') k).hom ≫ ·) hy''`.
-/
theorem GlobalTheory.EtC.contCone_of_levelwise : ∀ (R : Type) [CommRing R] (F : Shv R) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Spc) (c : Cone G), (∀ k : SimplexCategoryᵒᵖ, ContCone R F (((evaluation _ PSh).obj k ⋙ disc).mapCone c)) → ContCone R F c := by
  intro R _ F I _ _ G c hG
  obtain ⟨-, hneg, -, -, -, hpos⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  obtain ⟨cl, hsurj, hiff, hzero, hpull⟩ := GlobalTheory.T.etaleSpaceCohomology_presheaf_classes_as_cocycles R F
  refine fun n => GlobalTheory.EtC.cont_cx_of_degreewise R I (G ⋙ chains R) ((chains R).mapCone c) (res R F)
     (fun i p hp => hpos (G.obj i) p hp) (fun p hp => hpos c.pt p hp) hneg ?_ n
  intro p s
  by_cases hp : 0 < p
  · constructor
    · intro t _
      obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
      refine ⟨i, 0, 0, zero_comp, ?_⟩
      have : t = 0 := (hpos c.pt p hp).eq_of_src _ _
      simp [this]
    · intro i u _ _
      refine ⟨i, 𝟙 i, 0, ?_⟩
      have : u = 0 := (hpos (G.obj i) p hp).eq_of_src _ _
      simp [this]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
    have hk := hG (op (SimplexCategory.mk k)) s
    constructor
    · intro t ht
      let t' := (chainsXIso R c.pt k).inv ≫ t
      have ht' : t' ≫ (res R F).d s (s + 1) = 0 := by simp [t', ht]
      obtain ⟨i, y, hy⟩ := hk.1 (cl _ s t' ht')
      obtain ⟨u', hu', rfl⟩ := hsurj _ s y
      obtain ⟨h2, hp2⟩ := hpull (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj c.pt) (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj i)) ((c.π.app i).app (op (SimplexCategory.mk k))) s u' hu'
      change pull R (disc.map ((c.π.app i).app (op (SimplexCategory.mk k)))) F s _ = _ at hy
      rw [hp2, hiff] at hy
      obtain ⟨y', hy'⟩ := hy
      refine ⟨i, (chainsXIso R (G.obj i) k).hom ≫ u', (chainsXIso R c.pt k).hom ≫ y', by simp [hu'], ?_⟩
      change ((chains R).map (c.π.app i)).f _ ≫ _ = _
      rw [chains_map_f]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [hy']
      simp [t', Preadditive.comp_add]
    · rintro i u hu ⟨y, hy⟩
      let u' := (chainsXIso R (G.obj i) k).inv ≫ u
      have hu' : u' ≫ (res R F).d s (s + 1) = 0 := by simp [u', hu]
      have hdie : pull R ((((evaluation _ PSh).obj (op (SimplexCategory.mk k)) ⋙ disc).mapCone c).π.app i) F s
          (cl _ s u' hu') = 0 := by
        change pull R (disc.map ((c.π.app i).app _)) F s _ = 0
        obtain ⟨h2, hp2⟩ := hpull (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj c.pt) (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj i)) ((c.π.app i).app (op (SimplexCategory.mk k))) s u' hu'
        rw [hp2, ← hzero (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj c.pt) s, hiff]
        refine ⟨(chainsXIso R c.pt k).inv ≫ y, ?_⟩
        change ((chains R).map (c.π.app i)).f _ ≫ u = _ at hy
        rw [chains_map_f] at hy
        rw [zero_add, Category.assoc, ← hy]
        simp [u']
      obtain ⟨k', f, hf⟩ := hk.2 i _ hdie
      change pull R (disc.map ((G.map f).app (op (SimplexCategory.mk k)))) F s _ = 0 at hf
      obtain ⟨h3, hp3⟩ := hpull (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj k')) (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj i)) ((G.map f).app (op (SimplexCategory.mk k))) s u' hu'
      rw [hp3, ← hzero (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj k')) s, hiff] at hf
      obtain ⟨y'', hy''⟩ := hf
      refine ⟨k', f, (chainsXIso R (G.obj k') k).hom ≫ y'', ?_⟩
      change ((chains R).map (G.map f)).f _ ≫ u = _
      rw [chains_map_f, zero_add] at *
      simp only [Category.assoc]
      exact congrArg ((chainsXIso R (G.obj k') k).hom ≫ ·) hy''

end
