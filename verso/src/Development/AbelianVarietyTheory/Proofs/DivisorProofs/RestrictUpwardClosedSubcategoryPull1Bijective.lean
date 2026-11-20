import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.Desc

open Classical in

/- English proof (translation)
Introduce `R _ C _ F P hP sep glue van`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `c hc`. Take `⟨f, rfl⟩` from `H1.mk_surjective F c`.

Rewrite `hc` using `[CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]`. Take `⟨g₀, hg⟩` from `hc`. Set `g : ∀ S, P S → F.obj S` to `fun S hS ↦ g₀ ⟨S, hS⟩`. Establish `hg' : ∀ (S S' : C) (hS : P S) (hS' : P S') (ψ : S ⟶ S'), g S' hS' - mp F ψ (g S hS) = f.1 S S' ψ` using `fun S S' hS hS' ψ ↦ congrFun (congrFun (congrFun hg ⟨S, hS⟩) ⟨S', hS'⟩) (ObjectProperty.homMk ψ)`. Establish `h1 : ∀ T : C, ∃ x : F.obj T, ∀ S (u : T ⟶ S) (hS : P S), mp F u x = g S hS - f.1 T S u`.

Introduce `T`. Take `⟨x, hx⟩` from `glue T (fun S u ↦ if hS : P S then g S hS - f.1 T S u else 0) fun S S' u ψ hS ↦ by`. Establish `hS'` using `hP _ _ ψ hS`. Simplify using `only [dif_pos hS, dif_pos hS', map_sub]`. Establish `k1` using `Z1.comp f u ψ`.

Establish `k2` using `hg' S S' hS hS' ψ`. Take the linear combination `k2 - k1`. Conclude with `⟨x, fun S u hS ↦ by rw [hx S u hS, dif_pos hS]⟩`. Use `choose x hx using h1`. Use `H1.mk_eq_zero.2 ⟨x, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `T T' φ`. Rewrite using `[amitsur_d0_apply]`. Use `(sub_eq_zero.1 (sep T' _ fun S u hS ↦ ?_)).symm` and prove the remaining obligations. Establish `k1` using `Z1.comp f φ u`. Establish `k2` using `hx T' S u hS`.

Establish `k3` using `hx T S (φ ≫ u) hS`. Rewrite `k3` using `[mp_comp]`. Simplify using `only [map_sub]`. Take the linear combination `k3 - k2 - k1`. Introduce `c`.

Take `⟨y, rfl⟩` from `H1.mk_surjective _ c`. Set `z : ∀ S S', (S ⟶ S') → F.obj S'` to `fun S S' ψ ↦ if h : P S then y.1 ⟨S, h⟩ ⟨S', hP _ _ ψ h⟩ (ObjectProperty.homMk ψ) else 0`. Establish `hz : ∀ S S' S'' (ψ : S ⟶ S') (χ : S' ⟶ S''), P S → z S S'' (ψ ≫ χ) = mp F χ (z S S' ψ) + z S' S'' χ`. Introduce `S S' S'' ψ χ hp`. Establish `hp'` using `hP _ _ ψ hp`.

Simplify using `only [z, dif_pos hp, dif_pos hp']`. Conclude with `y.2 (T := ⟨S, hp⟩) (T' := ⟨S', hp'⟩) (T'' := ⟨S'', hP _ _ χ hp'⟩) (ObjectProperty.homMk ψ) (ObjectProperty.homMk χ)`. Establish `hzy : ∀ (S S' : P.FullSubcategory) (ψ : S ⟶ S'), z S.obj S'.obj ψ.hom = y.1 S S' ψ`. Introduce `S S' ψ`. Simplify using `only [z, dif_pos S.property]`.

Both sides reduce to the same expression. Establish `h1 : ∀ T : C, ∃ b : ∀ S, (T ⟶ S) → F.obj S, (∀ S S' u ψ, P S → b S' (u ≫ ψ) - mp F ψ (b S u) = z S S' ψ) ∧ (P T → ∀ S u, b S u = z T S u)`. Introduce `T`. Distinguish the cases in `hp : P T`. Conclude with `⟨fun S u ↦ z T S u, fun S S' u ψ _ ↦ by`.

Use `hz _ _ _ u ψ hp` as an intermediate fact. Take the linear combination `this, fun _ _ _ ↦ rfl⟩`. Take `⟨b, hb⟩` from `van T (fun S S' _ ψ ↦ z S S' ψ) fun S S' S'' u ψ χ h ↦ hz _ _ _ ψ χ h`. Conclude with `⟨b, hb, fun h ↦ absurd h hp⟩`. Use `choose b hb hb' using h1`.

Establish `h2 : ∀ T T' (φ : T ⟶ T'), ∃ x : F.obj T', ∀ S (u : T' ⟶ S), P S → mp F u x = b T S (φ ≫ u) - b T' S u`. Introduce `T T' φ`. Use `glue T' _ fun S S' u ψ hp ↦ ?_` and prove the remaining obligations. Establish `k1` using `hb T _ _ (φ ≫ u) ψ hp`. Establish `k2` using `hb T' _ _ u ψ hp`.

Simplify using `only [map_sub, Category.assoc] at k1 ⊢`. Take the linear combination `k1 - k2`. Use `choose f hf using h2`. Use `⟨H1.mk F ⟨f, fun T T' T'' φ ψ ↦ sub_eq_zero.1 (sep T'' _ fun S u hp ↦ ?_)⟩, ?_⟩` and prove the remaining obligations. Establish `k1` using `hf _ _ (φ ≫ ψ) S u hp`.

Establish `k2` using `hf _ _ φ S (ψ ≫ u) hp`. Establish `k3` using `hf _ _ ψ S u hp`. Simplify using `only [map_sub, map_add, mp_comp, Category.assoc] at k1 k2 ⊢`. Take the linear combination `k1 - k2 - k3`. Rewrite using `[CoefMap.pullCohomologyOne_class]`.

Use `congr 1`. Use `Subtype.ext ?_` and prove the remaining obligations. Use function extensionality and compare the values at `S S' ψ`. Establish `k1` using `hf _ _ ψ.hom _ (𝟙 _) S'.property`. Rewrite `k1` using `[hb' _ S.property, hb' _ S'.property, mp_id, Category.comp_id]`.

Establish `k2` using `hz _ _ _ (𝟙 S'.obj) (𝟙 S'.obj) S'.property`. Rewrite `k2` using `[Category.id_comp, mp_id]`. Rewrite using `[← hzy]`. Express the relevant statement in the definitionally equal form `f _ _ ψ.hom = _`. Take the linear combination `k1 + k2`.
-/
theorem restrict_upwardClosed_subcategory_pull1_bijective : ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (P : ObjectProperty C), (∀ S S', (S ⟶ S') → P S → P S') →
    (∀ T, Desc.Sep F fun S (_ : T ⟶ S) ↦ P S) → (∀ T, Desc.Glue F fun S (_ : T ⟶ S) ↦ P S) →
    (∀ T, Desc.Van1 F fun S (_ : T ⟶ S) ↦ P S) → Function.Bijective (CoefMap.restrict F P.ι).pull1 := by
  intro R _ C _ F P hP sep glue van
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨f, rfl⟩ := H1.mk_surjective F c
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
    obtain ⟨g₀, hg⟩ := hc
    let g : ∀ S, P S → F.obj S := fun S hS ↦ g₀ ⟨S, hS⟩
    have hg' : ∀ (S S' : C) (hS : P S) (hS' : P S') (ψ : S ⟶ S'),
        g S' hS' - mp F ψ (g S hS) = f.1 S S' ψ := fun S S' hS hS' ψ ↦
      congrFun (congrFun (congrFun hg ⟨S, hS⟩) ⟨S', hS'⟩) (ObjectProperty.homMk ψ)
    have h1 : ∀ T : C, ∃ x : F.obj T, ∀ S (u : T ⟶ S) (hS : P S),
        mp F u x = g S hS - f.1 T S u := by
      intro T
      obtain ⟨x, hx⟩ := glue T (fun S u ↦ if hS : P S then g S hS - f.1 T S u else 0)
        fun S S' u ψ hS ↦ by
          have hS' := hP _ _ ψ hS
          simp only [dif_pos hS, dif_pos hS', map_sub]
          have k1 := Z1.comp f u ψ
          have k2 := hg' S S' hS hS' ψ
          linear_combination k2 - k1
      exact ⟨x, fun S u hS ↦ by rw [hx S u hS, dif_pos hS]⟩
    choose x hx using h1
    refine H1.mk_eq_zero.2 ⟨x, ?_⟩
    funext T T' φ
    rw [amitsur_d0_apply]
    refine (sub_eq_zero.1 (sep T' _ fun S u hS ↦ ?_)).symm
    have k1 := Z1.comp f φ u
    have k2 := hx T' S u hS
    have k3 := hx T S (φ ≫ u) hS
    rw [mp_comp] at k3
    simp only [map_sub]
    linear_combination k3 - k2 - k1
  · intro c
    obtain ⟨y, rfl⟩ := H1.mk_surjective _ c
    let z : ∀ S S', (S ⟶ S') → F.obj S' := fun S S' ψ ↦
      if h : P S then y.1 ⟨S, h⟩ ⟨S', hP _ _ ψ h⟩ (ObjectProperty.homMk ψ) else 0
    have hz : ∀ S S' S'' (ψ : S ⟶ S') (χ : S' ⟶ S''), P S →
        z S S'' (ψ ≫ χ) = mp F χ (z S S' ψ) + z S' S'' χ := by
      intro S S' S'' ψ χ hp
      have hp' := hP _ _ ψ hp
      simp only [z, dif_pos hp, dif_pos hp']
      exact y.2 (T := ⟨S, hp⟩) (T' := ⟨S', hp'⟩) (T'' := ⟨S'', hP _ _ χ hp'⟩)
        (ObjectProperty.homMk ψ) (ObjectProperty.homMk χ)
    have hzy : ∀ (S S' : P.FullSubcategory) (ψ : S ⟶ S'), z S.obj S'.obj ψ.hom = y.1 S S' ψ := by
      intro S S' ψ
      simp only [z, dif_pos S.property]
      rfl
    have h1 : ∀ T : C, ∃ b : ∀ S, (T ⟶ S) → F.obj S, (∀ S S' u ψ, P S →
        b S' (u ≫ ψ) - mp F ψ (b S u) = z S S' ψ) ∧ (P T → ∀ S u, b S u = z T S u) := by
      intro T
      by_cases hp : P T
      · exact ⟨fun S u ↦ z T S u, fun S S' u ψ _ ↦ by
          have := hz _ _ _ u ψ hp
          linear_combination this, fun _ _ _ ↦ rfl⟩
      · obtain ⟨b, hb⟩ := van T (fun S S' _ ψ ↦ z S S' ψ) fun S S' S'' u ψ χ h ↦ hz _ _ _ ψ χ h
        exact ⟨b, hb, fun h ↦ absurd h hp⟩
    choose b hb hb' using h1
    have h2 : ∀ T T' (φ : T ⟶ T'), ∃ x : F.obj T', ∀ S (u : T' ⟶ S), P S →
        mp F u x = b T S (φ ≫ u) - b T' S u := by
      intro T T' φ
      refine glue T' _ fun S S' u ψ hp ↦ ?_
      have k1 := hb T _ _ (φ ≫ u) ψ hp
      have k2 := hb T' _ _ u ψ hp
      simp only [map_sub, Category.assoc] at k1 ⊢
      linear_combination k1 - k2
    choose f hf using h2
    refine ⟨H1.mk F ⟨f, fun T T' T'' φ ψ ↦ sub_eq_zero.1 (sep T'' _ fun S u hp ↦ ?_)⟩, ?_⟩
    · have k1 := hf _ _ (φ ≫ ψ) S u hp
      have k2 := hf _ _ φ S (ψ ≫ u) hp
      have k3 := hf _ _ ψ S u hp
      simp only [map_sub, map_add, mp_comp, Category.assoc] at k1 k2 ⊢
      linear_combination k1 - k2 - k3
    · rw [CoefMap.pullCohomologyOne_class]
      congr 1
      refine Subtype.ext ?_
      funext S S' ψ
      have k1 := hf _ _ ψ.hom _ (𝟙 _) S'.property
      rw [hb' _ S.property, hb' _ S'.property, mp_id, Category.comp_id] at k1
      have k2 := hz _ _ _ (𝟙 S'.obj) (𝟙 S'.obj) S'.property
      rw [Category.id_comp, mp_id] at k2
      rw [← hzy]
      change f _ _ ψ.hom = _
      linear_combination k1 + k2

end GlobalTheory.CatCoh.Desc
