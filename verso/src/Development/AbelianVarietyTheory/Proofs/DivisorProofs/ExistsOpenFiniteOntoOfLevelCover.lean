import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegTh

/- English proof (translation)
Introduce `g n F o Ω _ _ _ β S u Y X M q f Xab d hL hf hiso hd hdo hrange`. Establish `hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω)`. Rewrite using `[spMap, CommRingCat.ofHom_id, Spec.map_id]`. Establish `hf' : M.pt ≫ f = X.pt` using `by simpa [RatModel.IsHom, hid] using hf`. Establish `hd' : Y.pt ≫ d = X.pt` using `by simpa [RatModel.IsHom, hid] using hd`.

Use `set U : M.Z.Opens := f ⁻¹ᵁ d.opensRange with hUdef`. Establish `hUle : U ≤ f ⁻¹ᵁ Xab` using `fun m hm => hrange hm`. Establish `hopen : IsOpenImmersion (U.ι ≫ f)`. Establish `e : U.ι ≫ f = M.Z.homOfLE hUle ≫ (f ∣_ Xab) ≫ Xab.ι`. Rewrite using `[morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]`.

Rewrite using `[e]`. Use `infer_instance`. Establish `hrng : Set.range (U.ι ≫ f) = Set.range d`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨m, rfl⟩`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `m.2`. Introduce and unpack `⟨y, rfl⟩`. Establish `hy : d y ∈ Xab` using `hrange ⟨y, rfl⟩`.

Take `⟨m', hm'⟩` from `(f ∣_ Xab).surjective ⟨d y, hy⟩`. Establish `h1 : f ((f ⁻¹ᵁ Xab).ι m') = d y`. Rewrite using `[← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply, hm']`. Both sides reduce to the same expression. Establish `h2 : (f ⁻¹ᵁ Xab).ι m' ∈ U` using `⟨y, h1.symm⟩`.

Conclude with `⟨⟨_, h2⟩, h1⟩`. Set `e` to `IsOpenImmersion.isoOfRangeEq (U.ι ≫ f) d hrng`. Establish `he : e.hom ≫ d = U.ι ≫ f` using `IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _`. Take `⟨-, hfin, hsurj, hs, hpt⟩` from `hL`. Use `⟨U, e.hom ≫ q, ⟨?_, inferInstance, inferInstance, ?_, ?_⟩, fun m hm => hUle hm⟩` and prove the remaining obligations.

Take `⟨w⟩ : Nonempty (Sp Ω)` from `inferInstance`. Use `⟨M.pt w, Y.pt w, ?_⟩` and prove the remaining obligations. Establish `h1 : d (Y.pt w) = X.pt w` using `by rw [← hd']; rfl`. Establish `h2 : f (M.pt w) = X.pt w` using `by rw [← hf']; rfl`. Conclude with `h1.trans h2.symm`.

Rewrite using `[Category.assoc, hs, ← hd.inducedModelMorphism_comp_structureMap, ← hf.inducedModelMorphism_comp_structureMap]`. Simplify using `only [← Category.assoc, he]`. Introduce `x hx`. Establish `h : x ≫ e.hom = Y.pt`. Rewrite using `[← cancel_mono d, Category.assoc, he, ← Category.assoc, hx, hf', hd']`.

Rewrite using `[← Category.assoc, h, hpt]`.
-/
theorem exists_openAt_of_levAt : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    (β : cycAway n →+* o) (S : ThetaSys o Ω) (u : Sp S.R ⟶ F.X) (Y X M : RatModel o Ω) (q : Y.Z ⟶ F.X)
    (f : M.Z ⟶ X.Z) (Xab : X.Z.Opens) (d : Y.Z ⟶ X.Z), LevAt F β u Y q → X.IsHom M (AlgHom.id o Ω) f →
    IsIso (f ∣_ Xab) → X.IsHom Y (AlgHom.id o Ω) d → IsOpenImmersion d → Set.range d ⊆ Xab →
    ∃ (U : M.Z.Opens) (c : U.toScheme ⟶ F.X), OpenAt F β u M U c ∧ (U : Set M.Z) ⊆ f ⁻¹' Xab := by
  intro g n F o Ω _ _ _ β S u Y X M q f Xab d hL hf hiso hd hdo hrange
  have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by
    rw [spMap, CommRingCat.ofHom_id, Spec.map_id]
  have hf' : M.pt ≫ f = X.pt := by simpa [RatModel.IsHom, hid] using hf
  have hd' : Y.pt ≫ d = X.pt := by simpa [RatModel.IsHom, hid] using hd
  set U : M.Z.Opens := f ⁻¹ᵁ d.opensRange with hUdef
  have hUle : U ≤ f ⁻¹ᵁ Xab := fun m hm => hrange hm
  have hopen : IsOpenImmersion (U.ι ≫ f) := by
    have e : U.ι ≫ f = M.Z.homOfLE hUle ≫ (f ∣_ Xab) ≫ Xab.ι := by
      rw [morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
    rw [e]
    infer_instance
  have hrng : Set.range (U.ι ≫ f) = Set.range d := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact m.2
    · rintro ⟨y, rfl⟩
      have hy : d y ∈ Xab := hrange ⟨y, rfl⟩
      obtain ⟨m', hm'⟩ := (f ∣_ Xab).surjective ⟨d y, hy⟩
      have h1 : f ((f ⁻¹ᵁ Xab).ι m') = d y := by
        rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply, hm']
        rfl
      have h2 : (f ⁻¹ᵁ Xab).ι m' ∈ U := ⟨y, h1.symm⟩
      exact ⟨⟨_, h2⟩, h1⟩
  let e := IsOpenImmersion.isoOfRangeEq (U.ι ≫ f) d hrng
  have he : e.hom ≫ d = U.ι ≫ f := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  obtain ⟨-, hfin, hsurj, hs, hpt⟩ := hL
  refine ⟨U, e.hom ≫ q, ⟨?_, inferInstance, inferInstance, ?_, ?_⟩, fun m hm => hUle hm⟩
  · obtain ⟨w⟩ : Nonempty (Sp Ω) := inferInstance
    refine ⟨M.pt w, Y.pt w, ?_⟩
    have h1 : d (Y.pt w) = X.pt w := by rw [← hd']; rfl
    have h2 : f (M.pt w) = X.pt w := by rw [← hf']; rfl
    exact h1.trans h2.symm
  · rw [Category.assoc, hs, ← hd.inducedModelMorphism_comp_structureMap, ← hf.inducedModelMorphism_comp_structureMap]
    simp only [← Category.assoc, he]
  · intro x hx
    have h : x ≫ e.hom = Y.pt := by
      rw [← cancel_mono d, Category.assoc, he, ← Category.assoc, hx, hf', hd']
    rw [← Category.assoc, h, hpt]

end GlobalTheory.SiegTh

end
