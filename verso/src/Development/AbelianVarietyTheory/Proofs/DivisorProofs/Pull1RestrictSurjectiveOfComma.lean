import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh

/- English proof (translation)
Introduce `R _ C _ C' _ F G hsep hglue hvan c`. Take `⟨y, rfl⟩` from `H1.mk_surjective _ c`. Establish `hb : ∀ T : C, ∃ b : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), b t' (u ≫ G.map a) - mp F (G.map a) (b t u) = y.1 t t' a` using `fun T ↦ hvan T (fun t t' _ a ↦ y.1 t t' a) fun t t' t'' _ a a' ↦ Z1.comp y a a'`. Use `choose b hb using hb`. Establish `hx : ∀ T T' (φ : T ⟶ T'), ∃ x : F.obj T', ∀ t u, mp F u x = b T t (φ ≫ u) - b T' t u`.

Introduce `T T' φ`. Use `hglue T' _ fun t t' u a ↦ ?_` and prove the remaining obligations. Establish `k1` using `hb T t t' (φ ≫ u) a`. Establish `k2` using `hb T' t t' u a`. Rewrite `k1` using `[Category.assoc]`.

Rewrite using `[map_sub]`. Take the linear combination `k1 - k2`. Use `choose x hx using hx`. Establish `hxc : x ∈ Z1 F` using `fun T T' T'' φ ψ ↦ sub_eq_zero.1 (hsep T'' _ fun t u ↦ by`. Establish `k1` using `hx T T'' (φ ≫ ψ) t u`.

Establish `k2` using `hx T T' φ t (ψ ≫ u)`. Establish `k3` using `hx T' T'' ψ t u`. Rewrite `k2` using `[mp_comp]`. Simplify using `only [map_sub, map_add, Category.assoc] at k1 k2 ⊢`. Take the linear combination `k1 - k2 - k3)`.

Use `⟨H1.mk F ⟨x, hxc⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[CoefMap.pullCohomologyOne_class, H1.mk_eq_mk]`. Use `⟨fun t ↦ -b (G.obj t) t (𝟙 _), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `t t' a`. Establish `k1` using `hx _ _ (G.map a) t' (𝟙 _)`.

Establish `k2` using `hb (G.obj t) t t' (𝟙 _) a`. Rewrite `k1` using `[mp_id, Category.comp_id]`. Rewrite `k2` using `[Category.id_comp]`. Use `show -b _ t' (𝟙 _) - mp F (G.map a) (-b _ t (𝟙 _)) = x _ _ (G.map a) - (show F.obj (G.obj t') from y.1 t t' a)`. Rewrite using `[map_neg]`.

Take the linear combination `-k1 - k2`.
-/
theorem pull1_restrict_surjective_of_comma : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : F.obj T), (∀ t (u : T ⟶ G.obj t), mp F u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : F.obj T, ∀ t u, mp F u x = s t u) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp F (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = y t t' u a) → Function.Surjective (CoefMap.restrict F G).pull1 := by
  intro R _ C _ C' _ F G hsep hglue hvan c
  obtain ⟨y, rfl⟩ := H1.mk_surjective _ c
  have hb : ∀ T : C, ∃ b : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t)
      (a : t ⟶ t'), b t' (u ≫ G.map a) - mp F (G.map a) (b t u) = y.1 t t' a := fun T ↦
    hvan T (fun t t' _ a ↦ y.1 t t' a) fun t t' t'' _ a a' ↦ Z1.comp y a a'
  choose b hb using hb
  have hx : ∀ T T' (φ : T ⟶ T'), ∃ x : F.obj T', ∀ t u, mp F u x = b T t (φ ≫ u) - b T' t u := by
    intro T T' φ
    refine hglue T' _ fun t t' u a ↦ ?_
    have k1 := hb T t t' (φ ≫ u) a
    have k2 := hb T' t t' u a
    rw [Category.assoc] at k1
    rw [map_sub]
    linear_combination k1 - k2
  choose x hx using hx
  have hxc : x ∈ Z1 F := fun T T' T'' φ ψ ↦ sub_eq_zero.1 (hsep T'' _ fun t u ↦ by
    have k1 := hx T T'' (φ ≫ ψ) t u
    have k2 := hx T T' φ t (ψ ≫ u)
    have k3 := hx T' T'' ψ t u
    rw [mp_comp] at k2
    simp only [map_sub, map_add, Category.assoc] at k1 k2 ⊢
    linear_combination k1 - k2 - k3)
  refine ⟨H1.mk F ⟨x, hxc⟩, ?_⟩
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk]
  refine ⟨fun t ↦ -b (G.obj t) t (𝟙 _), ?_⟩
  funext t t' a
  have k1 := hx _ _ (G.map a) t' (𝟙 _)
  have k2 := hb (G.obj t) t t' (𝟙 _) a
  rw [mp_id, Category.comp_id] at k1
  rw [Category.id_comp] at k2
  show -b _ t' (𝟙 _) - mp F (G.map a) (-b _ t (𝟙 _)) = x _ _ (G.map a) - (show F.obj (G.obj t') from y.1 t t' a)
  rw [map_neg]
  linear_combination -k1 - k2

end GlobalTheory.CatCoh
